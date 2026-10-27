module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisB12
public import CFSG.LieType.SeitzGeneration.HeisSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

section ToMat

variable {L : Type} [Field L]

@[expose] def toMat (ι : L →+* K) (A : M3 L) : Matrix (Fin 3) (Fin 3) K :=
  !![ι A.a00, ι A.a01, ι A.a02; ι A.a10, ι A.a11, ι A.a12; ι A.a20, ι A.a21, ι A.a22]

theorem toMat_mul (ι : L →+* K) (A B : M3 L) : toMat ι (A * B) = toMat ι A * toMat ι B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, M3.mul_def, Matrix.mul_apply, Fin.sum_univ_three]

theorem toMat_one (ι : L →+* K) : toMat ι (1 : M3 L) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, show (1 : M3 L) = ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ from rfl]

theorem toMat_smul (ι : L →+* K) (c : L) (A : M3 L) :
    toMat ι (M3.smul c A) = ι c • toMat ι A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, M3.smul]

theorem toMat_det (ι : L →+* K) (A : M3 L) : (toMat ι A).det = ι A.det := by
  rw [Matrix.det_fin_three]
  simp [toMat, M3.det]

theorem toMat_transpose_map (h : UnitaryFieldData ℓ f K) (ι : L →+* K) (A : M3 L) :
    toMat ι ((A.map (· ^ (ℓ ^ f))).transpose) = ((toMat ι A).map h.bar)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, M3.map, M3.transpose, h.bar_apply]

theorem toMat_dM3 (ι : L →+* K) (ω₀ : L) : toMat ι (dM3 ω₀) = hD (ι ω₀) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, dM3, hD]

theorem toMat_sM3 (ι : L →+* K) : toMat ι (sM3 : M3 L) = hS := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, sM3, hS]

theorem toMat_mem_heisLines (ι : L →+* K) {ω₀ : L} {M : M3 L} (hM : M ∈ lineList ω₀) :
    toMat ι M ∈ heisLines (ι ω₀) := by
  simp only [lineList, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · simp [heisLines, toMat_dM3]
  · simp [heisLines, toMat_sM3]
  · simp [heisLines, toMat_mul, toMat_dM3, toMat_sM3]
  · simp [heisLines, toMat_mul, toMat_dM3, toMat_sM3]

end ToMat

variable (ℓ f K) in
def GoodMat (ω : K) (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ g ∈ heisClosure ℓ f K ω, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A

theorem goodMat_one (ω : K) : GoodMat ℓ f K ω 1 := ⟨1, Subgroup.one_mem _, rfl⟩

theorem goodMat_mul {ω : K} {A B : Matrix (Fin 3) (Fin 3) K} (hA : GoodMat ℓ f K ω A)
    (hB : GoodMat ℓ f K ω B) : GoodMat ℓ f K ω (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := hB
  exact ⟨g * g', Subgroup.mul_mem _ hg hg', rfl⟩

theorem goodMat_of_gen (h : UnitaryFieldData ℓ f K) {ω : K} {A M : Matrix (Fin 3) (Fin 3) K}
    (hdet : A.det = 1) (hu : (A.map h.bar)ᵀ * A = 1) (hM : M ∈ heisLines ω) {c : K}
    (hc : A * M = c • (M * A)) : GoodMat ℓ f K ω A := by
  let g : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL ⟨A, hdet⟩
  have hg : g ∈ unitarySU ℓ f K 3 := (mem_unitarySU_iff h).2 ⟨hdet, hu⟩
  exact ⟨⟨g, hg⟩, Subgroup.subset_closure ⟨M, hM, c, hc⟩, rfl⟩

section EvalW

variable {L : Type} [Field L]

theorem goodMat_evalW {ω : K} (ι : L →+* K) {letters : List (M3 L)}
    (hl : ∀ x ∈ letters, GoodMat ℓ f K ω (toMat ι x)) :
    ∀ w : List ℕ, GoodMat ℓ f K ω (toMat ι (evalW letters w))
  | [] => by simpa [evalW, toMat_one] using goodMat_one (ℓ := ℓ) (f := f) ω
  | i :: w => by
    rw [evalW, toMat_mul]
    refine goodMat_mul ?_ (goodMat_evalW ι hl w)
    by_cases hi : i < letters.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hl _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
      exact goodMat_one ω

end EvalW

theorem su2_entries (h : UnitaryFieldData ℓ f K) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hu : (M.map h.bar)ᵀ * M = 1) :
    M 1 0 = -(M 0 1) ^ ℓ ^ f ∧ M 1 1 = (M 0 0) ^ ℓ ^ f ∧
      M 0 0 * (M 0 0) ^ ℓ ^ f + M 0 1 * (M 0 1) ^ ℓ ^ f = 1 := by
  have hinv : M⁻¹ = (M.map h.bar)ᵀ := Matrix.inv_eq_left_inv hu
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two] at hinv
  have e00 := congrFun (congrFun hinv 0) 0
  have e01 := congrFun (congrFun hinv 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01
  have hc : M 1 0 = -h.bar (M 0 1) := by
    rw [← h.bar_bar (M 1 0), ← e01, map_neg]
  have e := congrFun (congrFun hu 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at e
  have e' : h.bar (M 0 0) * M 0 0 + h.bar (M 1 0) * M 1 0 = 1 := e
  rw [← e01, hc] at e'
  refine ⟨by rw [hc, h.bar_apply], by rw [e00, h.bar_apply], ?_⟩
  rw [← h.bar_apply, ← h.bar_apply]
  linear_combination e'

theorem heisB12_le_of_check {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData ℓ f K) {ω₀ : L} {ω : K} (ι : L →+* K) (hι : Function.Surjective ι)
    (hιω : ι ω₀ = ω) {q : ℕ} (hq : ℓ ^ f = q) {gens : List (M3 L)} {ws₁ ws₂ : List (List ℕ)}
    (hcheck : heisCheck q ω₀ gens ws₁ ws₂ = true) : heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
  subst hq hιω
  unfold heisCheck at hcheck
  rw [Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hgens, hcov⟩ := hcheck
  have hG : ∀ G ∈ gens, GoodMat ℓ f K (ι ω₀) (toMat ι G) := by
    intro G hG
    obtain ⟨hdet, hu, M, hM, c, hc⟩ := of_decide_eq_true (hgens G hG)
    refine goodMat_of_gen h (c := ι c) ?_ ?_ (toMat_mem_heisLines ι hM) ?_
    · rw [toMat_det, hdet, map_one]
    · rw [← toMat_transpose_map h, ← toMat_mul, hu, toMat_one]
    · have := congrArg (toMat ι) hc
      rwa [toMat_mul, toMat_smul, toMat_mul] at this
  have hL1 : ∀ x ∈ ws₁.map (evalW gens), GoodMat ℓ f K (ι ω₀) (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodMat_evalW ι hG w
  have hL2 : ∀ x ∈ ws₂.map (evalW (ws₁.map (evalW gens))), GoodMat ℓ f K (ι ω₀) (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodMat_evalW ι hL1 w
  have hcov' := of_decide_eq_true hcov
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hA
  obtain ⟨e10, e11, enorm⟩ := su2_entries h hdet hu
  obtain ⟨a, ha⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 0)
  obtain ⟨b, hb⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
  have hn : a * a ^ ℓ ^ f + b * b ^ ℓ ^ f = 1 := by
    apply ι.injective
    simp only [map_add, map_mul, map_pow, ha, hb, enorm, map_one]
  obtain ⟨g', hg', hgg⟩ := hL2 _ (hcov' a b hn)
  have hmat : toMat ι (blockM3 (ℓ ^ f) a b) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hgA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, blockM3, ha, hb, e10, e11]
  have : g' = g := Subtype.ext (Units.ext (hgg.trans hmat))
  exact this ▸ hg'

theorem exists_ringHom_omega {L : Type} [Field L] [Fintype L] (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hL : Fintype.card L = (ℓ ^ f) ^ 2) {ω₀ : L}
    (hω₀ : IsPrimitiveRoot ω₀ 3) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    ∃ ι : L →+* K, Function.Surjective ι ∧ ι ω₀ = ω := by
  have := h.finite
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card L = Fintype.card K := by
    rw [hL, ← Nat.card_eq_fintype_card, h.card, ← pow_mul, mul_comm]
  let e : L ≃+* K := FiniteField.ringEquivOfCardEq hcard
  have hpr : IsPrimitiveRoot (e ω₀) 3 := hω₀.map_of_injective e.injective
  obtain ⟨i, hi, hiω⟩ := hpr.eq_pow_of_pow_eq_one hω.pow_eq_one
  interval_cases i
  · exact absurd (by simpa using hiω.symm) (hω.ne_one (by norm_num))
  · exact ⟨e, e.surjective, by simpa using hiω⟩
  · refine ⟨h.bar.comp e.toRingHom, ?_, ?_⟩
    · exact (Finite.surjective_of_injective h.bar.injective).comp e.surjective
    · simp [bar_eq_sq_of_cube h hq3 hpr.pow_eq_one, ← hiω]

end CFSG.LieType.SeitzGeneration.HeisSmall
