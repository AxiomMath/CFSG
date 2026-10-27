module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Proj

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat pairMat_mul pairMat_one)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

variable (K) in
@[expose] def offInd (J : Finset ι) : Matrix ι ι K :=
  diagonal fun i => if i ∈ J then 0 else 1

theorem offInd_mul_apply (J : Finset ι) (g : Matrix ι ι K) (i j : ι) :
    (offInd K J * g) i j = if i ∈ J then 0 else g i j := by
  rw [offInd, diagonal_mul]
  split_ifs <;> simp

theorem mul_offInd_apply (J : Finset ι) (g : Matrix ι ι K) (i j : ι) :
    (g * offInd K J) i j = if j ∈ J then 0 else g i j := by
  rw [offInd, mul_diagonal]
  split_ifs <;> simp

omit [Fintype ι] in
theorem offInd_apply (J : Finset ι) (i j : ι) :
    offInd K J i j = if i ∉ J ∧ i = j then 1 else 0 := by
  rw [offInd, diagonal_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ J <;> simp [hij, hi]

@[expose] def BlockDiag (J : Finset ι) (M : Matrix ι ι K) : Prop :=
  offInd K J * M = M * offInd K J

@[expose] def PairSupp (J : Finset ι) (M : Matrix ι ι K) : Prop :=
  offInd K J * M = offInd K J ∧ M * offInd K J = offInd K J

theorem blockDiag_iff {J : Finset ι} {D : Matrix ι ι K} :
    BlockDiag J D ↔ ∀ i j, (i ∈ J ↔ j ∉ J) → D i j = 0 := by
  constructor
  · intro h i j hij
    have := congrFun (congrFun h i) j
    rw [offInd_mul_apply, mul_offInd_apply] at this
    by_cases hi : i ∈ J
    · have hj : j ∉ J := hij.1 hi
      simp only [hi, hj, ite_true, ite_false] at this
      exact this.symm
    · have hj : j ∈ J := by
        by_contra hj
        exact hi (hij.2 hj)
      simp only [hi, hj, ite_true, ite_false] at this
      exact this
  · intro h
    ext i j
    rw [offInd_mul_apply, mul_offInd_apply]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
    · simp only [hi, hj, ite_true]
    · simp only [hi, hj, ite_true, ite_false]
      exact (h i j (iff_of_true hi hj)).symm
    · simp only [hi, hj, ite_true, ite_false]
      exact h i j (iff_of_false hi (not_not.2 hj))
    · simp only [hi, hj, ite_false]

theorem pairSupp_iff {J : Finset ι} {g : Matrix ι ι K} :
    PairSupp J g ↔ ∀ i j, (i ∉ J ∨ j ∉ J) → g i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [offInd_mul_apply, offInd_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_offInd_apply, offInd_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      rw [offInd_mul_apply, offInd_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact h i j (Or.inl hi)
    · ext i j
      rw [mul_offInd_apply, offInd_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [h i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]

theorem blockDiag_of_pairSupp {J : Finset ι} {M : Matrix ι ι K} (h : PairSupp J M) :
    BlockDiag J M := by
  rw [BlockDiag, h.1, h.2]

theorem pairSupp_one (J : Finset ι) : PairSupp J (1 : Matrix ι ι K) := by
  simp [PairSupp]

theorem pairSupp_mul {J : Finset ι} {M N : Matrix ι ι K} (hM : PairSupp J M)
    (hN : PairSupp J N) : PairSupp J (M * N) :=
  ⟨by rw [← Matrix.mul_assoc, hM.1, hN.1], by rw [Matrix.mul_assoc, hN.2, hM.2]⟩

theorem pairSupp_of_mul_eq_one {J : Finset ι} {M Mi : Matrix ι ι K} (hM : PairSupp J M)
    (h1 : M * Mi = 1) (h2 : Mi * M = 1) : PairSupp J Mi := by
  refine ⟨?_, ?_⟩
  · calc offInd K J * Mi = (offInd K J * M) * Mi := by rw [hM.1]
      _ = offInd K J := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · calc Mi * offInd K J = Mi * (M * offInd K J) := by rw [hM.2]
      _ = offInd K J := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem blockDiag_mul {J : Finset ι} {M N : Matrix ι ι K} (hM : BlockDiag J M)
    (hN : BlockDiag J N) : BlockDiag J (M * N) := by
  have hM' : offInd K J * M = M * offInd K J := hM
  have hN' : offInd K J * N = N * offInd K J := hN
  change offInd K J * (M * N) = M * N * offInd K J
  rw [← Matrix.mul_assoc, hM', Matrix.mul_assoc, hN', Matrix.mul_assoc]

theorem blockDiag_of_mul_eq_one {J : Finset ι} {D Di : Matrix ι ι K} (hD : BlockDiag J D)
    (h1 : D * Di = 1) (h2 : Di * D = 1) : BlockDiag J Di := by
  have hD' : offInd K J * D = D * offInd K J := hD
  change offInd K J * Di = Di * offInd K J
  calc offInd K J * Di = Di * D * offInd K J * Di := by rw [h2, Matrix.one_mul]
    _ = Di * (D * offInd K J) * Di := by simp only [Matrix.mul_assoc]
    _ = Di * (offInd K J * D) * Di := by rw [hD']
    _ = Di * offInd K J * (D * Di) := by simp only [Matrix.mul_assoc]
    _ = Di * offInd K J := by rw [h1, Matrix.mul_one]

theorem pairSupp_conj {J : Finset ι} {D Di M : Matrix ι ι K} (h1 : D * Di = 1) (h2 : Di * D = 1)
    (hD : BlockDiag J D) (hM : PairSupp J M) : PairSupp J (D * M * Di) := by
  have hDi : offInd K J * Di = Di * offInd K J := blockDiag_of_mul_eq_one hD h1 h2
  have hD' : offInd K J * D = D * offInd K J := hD
  set P := offInd K J with hP
  refine ⟨?_, ?_⟩
  · calc P * (D * M * Di) = D * (P * M) * Di := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD']
          simp only [Matrix.mul_assoc]
      _ = D * (P * Di) := by rw [hM.1, Matrix.mul_assoc]
      _ = D * (Di * P) := by rw [hDi]
      _ = P := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · calc (D * M * Di) * P = D * (M * P) * Di := by
          rw [Matrix.mul_assoc, ← hDi]
          simp only [Matrix.mul_assoc]
      _ = (D * P) * Di := by rw [hM.2]
      _ = (P * D) * Di := by rw [hD']
      _ = P := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

variable {a b : ι}

@[expose] def pairBlock (a b : ι) (M : Matrix ι ι K) : Matrix (Fin 2) (Fin 2) K :=
  !![M a a, M a b; M b a, M b b]

omit [Fintype ι] in
theorem mem_pair {x : ι} : x ∈ ({a, b} : Finset ι) ↔ x = a ∨ x = b := by simp

theorem pairSupp_pairMat (hab : a ≠ b) (X : Matrix (Fin 2) (Fin 2) K) :
    PairSupp {a, b} (pairMat a b X) := by
  rw [pairSupp_iff]
  intro x y hxy
  simp only [mem_pair, not_or] at hxy
  rcases hxy with ⟨hxa, hxb⟩ | ⟨hya, hyb⟩
  · simp [pairMat, hxa, hxb, one_apply]
  · by_cases hxa : x = a
    · subst hxa
      simp [pairMat, hya, hyb, Ne.symm hya]
    · by_cases hxb : x = b
      · subst hxb
        simp [pairMat, hya, hyb, hxa, Ne.symm hyb]
      · simp [pairMat, hxa, hxb, one_apply]

omit [Fintype ι] in
theorem pairBlock_pairMat (hab : a ≠ b) (X : Matrix (Fin 2) (Fin 2) K) :
    pairBlock a b (pairMat a b X) = X := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [pairBlock, pairMat, Ne.symm hab]

theorem pairMat_pairBlock (hab : a ≠ b) {M : Matrix ι ι K} (hM : PairSupp {a, b} M) :
    pairMat a b (pairBlock a b M) = M := by
  have h := pairSupp_iff.1 hM
  ext x y
  by_cases hxa : x = a
  · subst hxa
    by_cases hya : y = x
    · subst hya
      simp [pairMat, pairBlock]
    · by_cases hyb : y = b
      · subst hyb
        simp [pairMat, pairBlock, hya]
      · simp only [pairMat, Matrix.of_apply, hya, hyb, ite_true, ite_false]
        rw [h x y (Or.inr (by simp [hya, hyb]))]
        simp [Ne.symm hya]
  · by_cases hxb : x = b
    · subst hxb
      by_cases hya : y = a
      · subst hya
        simp [pairMat, pairBlock, hxa]
      · by_cases hyb : y = x
        · subst hyb
          simp [pairMat, pairBlock, hxa]
        · simp only [pairMat, Matrix.of_apply, hxa, hya, hyb, ite_true, ite_false]
          rw [h x y (Or.inr (by simp [hya, hyb]))]
          simp [Ne.symm hyb]
    · simp only [pairMat, Matrix.of_apply, hxa, hxb, ite_false]
      rw [h x y (Or.inl (by simp [hxa, hxb])), one_apply]

theorem pairBlock_mul (hab : a ≠ b) {M N : Matrix ι ι K} (hM : BlockDiag {a, b} M) :
    pairBlock a b (M * N) = pairBlock a b M * pairBlock a b N := by
  have h0 := blockDiag_iff.1 hM
  have hsum : ∀ k l, k ∈ ({a, b} : Finset ι) → (M * N) k l = M k a * N a l + M k b * N b l := by
    intro k l hk
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_add a b hab (fun c _ hc => ?_) (by simp) (by simp)
    have hc' : c ∉ ({a, b} : Finset ι) := by simp [hc.1, hc.2]
    rw [h0 k c (iff_of_true hk hc'), zero_mul]
  have ha : a ∈ ({a, b} : Finset ι) := by simp
  have hb : b ∈ ({a, b} : Finset ι) := by simp
  rw [pairBlock, pairBlock, pairBlock, Matrix.mul_fin_two, hsum a a ha, hsum a b ha, hsum b a hb,
    hsum b b hb]

theorem pairMat_mulVec_apply (hab : a ≠ b) (X : Matrix (Fin 2) (Fin 2) K) (u : ι → K) (x : ι) :
    (pairMat a b X *ᵥ u) x =
      if x = a then X 0 0 * u a + X 0 1 * u b
      else if x = b then X 1 0 * u a + X 1 1 * u b else u x := by
  rw [mulVec, dotProduct]
  by_cases hxa : x = a
  · subst hxa
    simp only [↓reduceIte]
    rw [Finset.sum_eq_add x b hab (fun c _ hc => by simp [pairMat, hc.1, hc.2])
      (by simp) (by simp)]
    simp [pairMat, Ne.symm hab]
  · by_cases hxb : x = b
    · subst hxb
      simp only [hxa, ↓reduceIte]
      rw [Finset.sum_eq_add a x hab
        (fun c _ hc => by simp [pairMat, hxa, hc.1, hc.2]) (by simp) (by simp)]
      simp [pairMat, hxa]
    · simp only [hxa, hxb, ↓reduceIte]
      rw [Finset.sum_eq_single x (fun c _ hc => by
        simp [pairMat, hxa, hxb, Ne.symm hc]) (by simp)]
      simp [pairMat, hxa, hxb]

theorem pairBlock_scalar_of_commute (hab : a ≠ b) {D : Matrix ι ι K} (hD : BlockDiag {a, b} D)
    (h1 : D * pairMat a b !![1, 1; 0, 1] = pairMat a b !![1, 1; 0, 1] * D)
    (h2 : D * pairMat a b !![1, 0; 1, 1] = pairMat a b !![1, 0; 1, 1] * D) :
    D a b = 0 ∧ D b a = 0 ∧ D a a = D b b := by
  have e1 := congrArg (pairBlock a b) h1
  have e2 := congrArg (pairBlock a b) h2
  rw [pairBlock_mul hab hD, pairBlock_mul hab (blockDiag_of_pairSupp (pairSupp_pairMat hab _)),
    pairBlock_pairMat hab] at e1 e2
  have f1 := congrFun (congrFun e1 0) 0
  have f2 := congrFun (congrFun e1 0) 1
  have f3 := congrFun (congrFun e2 0) 0
  simp [pairBlock] at f1 f2 f3
  exact ⟨by linear_combination f3, by linear_combination f1, by linear_combination f2⟩

end CFSG.ComponentClassification.Burgoyne.Proj
