#include<stdio.h>
#include<stdlib.h>
#include<windows.h>

typedef struct {
	int* target;
	int* source;
	int status;
} tag;

enum stat { null, pc, bd };

int* tmp;

// Function par performs the following:
// 
// It stores all such sequences in descending order into the target of a, and assigns initial status pc:
// Positions 0 to num-1 are the same as tmp;
// The sum of positions num to num+hom-1 equals top;
// Position 0 is >= -w and not -1;
// Positions from 1 onwards are non-negative, and each element is at least half of the previous one.
// 
// The value of cnt records the number of sequences.

void par(tag* a, int num, int* const cnt, int hom, int top, int w) {
	int i;
	// When hom=1, the num-th position must be top, previous positions match tmp.
	if (hom == 1) {
		// For position 1, no admissibility check is needed; for position 0, -1 should be excluded.
		if ((num == 0 && top + 1 != 0) || num == 1 || (num > 1 && top <= 2 * tmp[num - 1])) {
			tmp[num] = top;
			for (i = 0; i <= num; i++) {
				a[*cnt].target[i] = tmp[i];
			}
			a[*cnt].status = pc;
			(*cnt)++;
		}
	}
	// When hom>1, recursively assign position num from large to small.
	else {
		// When num > 0, the max value at position num is top or twice the previous value, min is 0.
		if (num > 0) {
			i = top;
			if (num > 1 && 2 * tmp[num - 1] < top) {
				i = 2 * tmp[num - 1];
			}
			for (; i >= 0; i--) {
				tmp[num] = i;
				par(a, num + 1, cnt, hom - 1, top - i, w);
			}
		}
		// When num = 0, max value is top, min is -w, -1 excluded.
		else {
			for (i = top; i + w >= 0; i--) {
				if (i + 1 == 0) {
					continue;
				}
				tmp[0] = i;
				par(a, 1, cnt, hom - 1, top - i, w);
			}
		}
	}
}

int mod(int a, int b) {
	if (a >= 0) {
		return a % b;
	}
	return (b + a % b) % b;
}

int diw(int a, int b) {
	if (a >= 0) {
		return a / b;
	}
	return (a + 1 - b) / b;
}

int binom(int a, int b) {
	if (b == 0) {
		return 1;
	}
	if (mod(a, 2) < mod(b, 2)) {
		return 0;
	}
	return binom(diw(a, 2), diw(b, 2));
}

int addmon(int** a, const int* b, int* cnt, int len) {
	int i, j;
	for (i = 0; i < *cnt; i++) {
		for (j = 0; j < len && a[i][j] == b[j]; j++);
		if (j == len) {
			for (j = 0; j < len; j++) {
				a[i][j] = a[*cnt - 1][j];
			}
			(*cnt)--;
			return 0;
		}
	}
	for (j = 0; j < len; j++) {
		a[*cnt][j] = b[j];
	}
	(*cnt)++;
	return 0;
}

// rel function simplifies using relations in the Lambda algebra to get admissible expressions.

void rel(int** a, int* cnt, int len) {
	// flag=1 indicates an inadmissible condition was found.
	int flag = 1;
	int i, j, k, m, n;
	while (flag) {
		flag = 0;
		for (i = 0; i < *cnt; i++) {
			for (j = 1; j < len - 1; j++) {
				if (2 * a[i][j] < a[i][j + 1]) {    /* Inadmissible! */
					flag++;
					for (k = 0; k < len; k++) {
						if (k == j || k == (j + 1)) {
							continue;
						}
						tmp[k] = a[i][k];
					}
					m = a[i][j];
					n = a[i][j + 1];
					for (k = 0; 2 * k <= (n - 2 * m - 2); k++) {
						if (!binom(n - 2 * m - 2 - k, k)) {
							continue;
						}
						tmp[j] = n - m - 1 - k;
						tmp[j + 1] = 2 * m + 1 + k;
						addmon(a, tmp, cnt, len);    /* Add transformed monomial. */
					}
					tmp[j] = m;
					tmp[j + 1] = n;
					addmon(a, tmp, cnt, len);    /* Remove original monomial. */
					break;
				}
			}
			if (flag) {
				break;
			}
		}
	}
}

int comp(const int* a, const int* b, int len) {
	int i;
	for (i = 0; i < len; i++) {
		if (a[i] > b[i]) {
			return 1;
		}
		if (a[i] < b[i]) {
			return -1;
		}
	}
	return 0;
}

int main() {
	int i, j, k, l;
	int i0, i1;
	int low, mid, high;
	long long ub, ubd;
	int w;
	printf("Please input weight:\nw=");
	for (scanf_s("%d", &w); w <= 0;) {
		printf("Error: nonpositive weight!\nw=");
		scanf_s("%d", &w);
	}
	printf("\n");
	int t;
	printf("Please input total degree:\nt=");
	for (scanf_s("%d", &t); t < 1;) {
		printf("Trivial for degree reasons! Please input again:\nt=");    /* The chain complex is trivial. */
		scanf_s("%d", &t);
	}
	printf("\n\n");
	int tot = t - w - 1;
	// ub: provides an upper bound on the dimension of the linear space (guaranteed not to overflow).
	if (t <= 25) {
		ub = 10000;
	}
	else if (t <= 31) {
		ub = 100000;
	}
	else {
		ub = 670000;
		for (i = 36; i < t; i++) {
			ub *= 1.47;
		}
	}
	// ubd: gives an upper bound for the number of monomials in the differentials.
	// (May or may not overflow)
	ubd = ub / 3;
	// Double pointer a: stores the bases of linear spaces for adjacent cohomological degrees.
	tag** a = (tag**)malloc(2 * sizeof(tag*));
	if (!a) {
		perror("malloc");
		system("pause");
		return -1;
	}
	*a = (tag*)malloc(2 * ub * sizeof(tag));
	if (!(*a)) {
		perror("malloc");
		system("pause");
		return -1;
	}
	*(a + 1) = *a + ub;
	for (i = 0; i < 2; i++) {
		for (j = 0; j < ub; j++) {
			a[i][j].target = (int*)malloc(t * sizeof(int));
			if (!(a[i][j].target)) {
				perror("malloc");
				system("pause");
				return -1;
			}
			a[i][j].source = (int*)malloc(t * sizeof(int));
			if (!(a[i][j].source)) {
				perror("malloc");
				system("pause");
				return -1;
			}
		}
	}
	// cnt: records the dimensions of the linear spaces at different cohomological degrees.
	int* cnt = (int*)malloc(t * sizeof(int));
	for (i = 0; i < t; i++) {
		*(cnt + i) = 0;
	}
	// tmp: temporary storage for monomials.
	tmp = (int*)malloc(sizeof(int) * t);
	// temp stores the monomial to be differentiated, diff stores the result of the differential.
	int* temp = (int*)malloc(t * sizeof(int));
	int** diff = (int**)malloc(ubd * sizeof(int*));
	if (!diff) {
		printf("Error: fail to allocate memory!\n");
		system("pause");
		return -1;
	}
	*diff = (int*)malloc(ubd * t * sizeof(int));
	if (!(*diff)) {
		printf("Error: fail to allocate memory!\n");
		system("pause");
		return -1;
	}
	for (i = 1; i < ubd; i++) {
		*(diff + i) = *(diff + (i - 1)) + t;
		if (!(*(diff + i))) {
			printf("Error: fail to allocate memory!\n");
			system("pause");
			return -1;
		}
	}
	// Store the basis of the linear space at cohomological degree 0.
	par(a[0], 0, cnt, 1, tot, w);
	int cntd;    /* Used to count number of monomials in diff. */
	int max;
	// Start computing differentials and output results.
	for (i = 0; i < t - 1; i++) {
		i0 = i % 2;
		i1 = (i + 1) % 2;
		// Store the basis of the linear space at cohomological degree i+1.
		par(a[i1], 0, cnt + (i + 1), i + 2, tot - i - 1, w);
		for (j = *(cnt + i) - 1; j >= 0; j--) {
			// For those already a boundary, skip differentiation.
			if (a[i0][j].status == bd) {
				continue;
			}
			for (k = 0; k <= i; k++) {
				temp[k] = a[i0][j].target[k];
			}
			temp[i + 1] = -1;
			cntd = 0;
			do {
				addmon(diff, temp, &cntd, i + 2);
				for (k = 0; k <= i; k++) {
					// Compute differential of temp[k] at position l, copy other values to tmp first.
					for (l = 0; l < k; l++) {
						tmp[l] = temp[l];
					}
					for (l = k + 2; l <= i + 1; l++) {
						tmp[l] = temp[l - 1];
					}
					// For the first position (cell), and other positions (Lambda algebra), treat separately.
					if (k == 0) {
						for (l = 1; l <= temp[k] + w; l++) {
							if (l == temp[k] + 1 || (!binom(temp[k] - l, l))) {
								continue;
							}
							tmp[k] = temp[k] - l;
							tmp[k + 1] = l - 1;
							addmon(diff, tmp, &cntd, i + 2);
						}
					}
					else {
						for (l = 1; 2 * l <= temp[k]; l++) {
							if (!binom(temp[k] - l, l)) {
								continue;
							}
							tmp[k] = temp[k] - l;
							tmp[k + 1] = l - 1;
							addmon(diff, tmp, &cntd, i + 2);
						}
					}
				}
				// After traversing l, remove temp.
				addmon(diff, temp, &cntd, i + 2);
				// Use rel to simplify and obtain admissible expression.
				rel(diff, &cntd, i + 2);
				// If the differential is zero, no need to update, exit loop and move to next term.
				if (cntd == 0) {
					break;
				}
				// If the differential is not zero, find the leading monomial.
				max = 0;
				for (k = 1; k < cntd; k++) {
					if (comp(diff[k], diff[max], i + 2) == 1) {
						max = k;
					}
				}
				low = 0;
				high = *(cnt + i + 1) - 1;
				while (low <= high) {
					mid = low + (high - low) / 2;
					if (comp(diff[max], a[i1][mid].target, i + 2) == 1) {
						high = mid - 1;
					}
					else if (comp(diff[max], a[i1][mid].target, i + 2) == -1) {
						low = mid + 1;
					}
					else {
						k = mid;
						break;
					}
				}
				// If this monomial is pc, mark it as bd, store source, mark source as null.
				if (a[i1][k].status == pc) {
					for (l = 0; l < i + 1; l++) {
						a[i1][k].source[l] = a[i0][j].target[l];
					}
					a[i1][k].status = bd;
					a[i0][j].status = null;
					break;
				}
				// If already bd, add the differential of its source.
				else {
					for (l = 0; l < i + 1; l++) {
						temp[l] = a[i1][k].source[l];
					}
					temp[i + 1] = -1;
				}
			} while (1);
		}
		printf("homological degree s=%d (topological degree %d, coweight %d):\n", i + 1, t - 1 - i, tot - i);
		for (j = 0; j < *(cnt + i); j++) {
			if (a[i0][j].status == pc) {
				for (k = 0; k < i + 1; k++) {
					printf("%d ", a[i0][j].target[k]);
				}
				printf("\n");
			}
			else if (a[i0][j].status == bd && a[i0][j].target[0] != a[i0][j].source[0]) {
				for (k = 0; k < i + 1; k++) {
					printf("%d ", a[i0][j].target[k]);
				}
				printf("<-- ");
				for (k = 0; k < i; k++) {
					printf("%d ", a[i0][j].source[k]);
				}
				printf("\n");
			}
		}
		printf("\n");
	}
	i0 = i % 2;
	printf("homological degree s=%d (topological degree %d, coweight %d):\n", i + 1, t - 1 - i, tot - i);
	for (j = 0; j < *(cnt + i); j++) {
		if (a[i0][j].status == pc) {
			for (k = 0; k < i + 1; k++) {
				printf("%d ", a[i0][j].target[k]);
			}
			printf("\n");
		}
		else if (a[i0][j].status == bd && a[i0][j].target[0] != a[i0][j].source[0]) {
			for (k = 0; k < i + 1; k++) {
				printf("%d ", a[i0][j].target[k]);
			}
			printf("<-- ");
			for (k = 0; k < i; k++) {
				printf("%d ", a[i0][j].source[k]);
			}
			printf("\n");
		}
	}
	printf("\nComputation finished!\n\n");
	free(tmp);
	free(temp);
	free(*diff);
	free(diff);
	for (i = 0; i < 2; i++) {
		for (j = 0; j < ub; j++) {
			free(a[i][j].target);
			free(a[i][j].source);
		}
	}
	free(*a);
	free(a);
	free(cnt);
	printf("Press any key to exit ...\n");
	system("pause");
	return 0;
}
