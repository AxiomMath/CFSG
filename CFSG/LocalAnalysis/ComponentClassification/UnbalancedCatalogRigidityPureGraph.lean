module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraphForms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open UnitaryHigher

variable {K : Type} [Field K] {n : ℕ}

section Canonical

variable {C : GL (Fin n) K} (hC : IsCanonicalGram (C : Matrix (Fin n) (Fin n) K))
include hC

theorem dualAut_mul_conjAut_canonical :
    dualAut n K * conjAut n K C = conjAut n K C * dualAut n K := by
  rw [dualAut_mul_conjAut, hC.inverseTranspose_eq]

theorem fieldAut_mul_conjAut_canonical (φ : K ≃+* K) :
    fieldAut n K φ * conjAut n K C = conjAut n K C * fieldAut n K φ := by
  rw [fieldAut_mul_conjAut, hC.map_eq]

theorem pureGraph_sq : (conjAut n K C * dualAut n K) ^ 2 = 1 := by
  obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hCC : C * C = 1 := Units.ext hC.sq
  rw [sq, mul_assoc, ← mul_assoc (dualAut n K), dualAut_mul_conjAut_canonical hC, mul_assoc,
    hdd, mul_one, ← map_mul, hCC, map_one]

omit hC in
theorem pureGraph_mul_conjAut (A : GL (Fin n) K) :
    conjAut n K C * dualAut n K * conjAut n K A =
      conjAut n K (C * GeneralLinearGroup.inverseTranspose A * C⁻¹) *
        (conjAut n K C * dualAut n K) := by
  rw [mul_assoc, dualAut_mul_conjAut, map_mul, map_mul, map_inv]
  group

theorem commute_pureGraph_fieldAut (φ : K ≃+* K) :
    Commute (conjAut n K C * dualAut n K) (fieldAut n K φ) := by
  change conjAut n K C * dualAut n K * fieldAut n K φ =
    fieldAut n K φ * (conjAut n K C * dualAut n K)
  rw [mul_assoc, dualAut_mul_fieldAut, ← mul_assoc, ← fieldAut_mul_conjAut_canonical hC,
    mul_assoc]

theorem commute_pureGraph_dualAut : Commute (conjAut n K C * dualAut n K) (dualAut n K) := by
  change conjAut n K C * dualAut n K * dualAut n K =
    dualAut n K * (conjAut n K C * dualAut n K)
  rw [← mul_assoc, dualAut_mul_conjAut_canonical hC]

theorem commute_pureGraph_conjAut_iff [Finite K] [CharP K 2] (hn : 3 ≤ n) (A : GL (Fin n) K) :
    Commute (conjAut n K C * dualAut n K) (conjAut n K A) ↔
      ∃ g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K),
        conjAut n K A = conjAut n K g := by
  have hCinv := hC.inv_eq
  have hCC : C * C = 1 := Units.ext hC.sq
  have hβ : ∀ X : GL (Fin n) K,
      conjAut n K (C * GeneralLinearGroup.inverseTranspose X * C⁻¹) =
        conjAut n K C * dualAut n K * conjAut n K X * (conjAut n K C * dualAut n K)⁻¹ :=
    fun X => by rw [pureGraph_mul_conjAut, mul_inv_cancel_right]
  have hcomm : Commute (conjAut n K C * dualAut n K) (conjAut n K A) ↔
      conjAut n K (C * GeneralLinearGroup.inverseTranspose A * C⁻¹) = conjAut n K A := by
    change conjAut n K C * dualAut n K * conjAut n K A =
      conjAut n K A * (conjAut n K C * dualAut n K) ↔ _
    rw [pureGraph_mul_conjAut]
    exact mul_left_inj _
  rw [hcomm]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h
    obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (u : K)
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hb
      exact u.ne_zero hb
    set c : Kˣ := Units.mk0 b hb0 with hc
    have hcc : c * c = u := Units.ext (by rw [Units.val_mul, hc, Units.val_mk0, hb])
    have hsc : GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin n) c) =
        (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv, GeneralLinearGroup.coe_scalar,
        scalar_apply, diagonal_transpose]
    have key : GeneralLinearGroup.inverseTranspose A =
        C * A * C * GeneralLinearGroup.scalar (Fin n) u := by
      have h1 : GeneralLinearGroup.inverseTranspose A =
          C⁻¹ * (A * GeneralLinearGroup.scalar (Fin n) u) * C := by
        rw [← hu]
        group
      rw [h1, hCinv]
      simp only [mul_assoc]
      rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u C).eq]
    refine ⟨A * GeneralLinearGroup.scalar (Fin n) c, ?_, ?_⟩
    · rw [mem_matrixIsometryGroup_iff_inverseTranspose, map_mul]
      calc GeneralLinearGroup.inverseTranspose A *
            GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin n) c)
          _ = C * A * C * GeneralLinearGroup.scalar (Fin n) c := by
            rw [key, hsc, ← hcc, map_mul, ← mul_assoc (C * A * C), mul_inv_cancel_right]
          _ = C * (A * GeneralLinearGroup.scalar (Fin n) c) * C := by
            simp only [mul_assoc]
            rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c C).eq]
          _ = C * (A * GeneralLinearGroup.scalar (Fin n) c) * C⁻¹ := by rw [hCinv]
    · rw [map_mul, conjAut_scalar, mul_one]
  · rintro ⟨g, hg, hAg⟩
    have hgT := (mem_matrixIsometryGroup_iff_inverseTranspose C g).mp hg
    rw [hβ, hAg, ← hβ, hgT, hCinv]
    congr 1
    rw [show C * (C * g * C) * C = (C * C) * g * (C * C) by group, hCC, one_mul, mul_one]

end Canonical

theorem dotProduct_mulVec_isometry {C g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) (x y : Fin n → K) :
    ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ⬝ᵥ
        ((C : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ y)) =
      x ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
  rw [mem_matrixIsometryGroup] at hg
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc,
    hg, ← dotProduct_mulVec]

theorem map_transvGL [CharP K 2] (φ : K →+* K) {C : Matrix (Fin n) (Fin n) K}
    (hCφ : C.map φ = C) {u : Fin n → K} (huφ : ∀ i, φ (u i) = u i)
    (hu : u ⬝ᵥ (C *ᵥ u) = 0) (s : K) :
    GeneralLinearGroup.map φ (transvGL C hu s) = transvGL C hu (φ s) := by
  have hφu : (⇑φ ∘ u) = u := funext huφ
  have hCu : ∀ j, φ ((C *ᵥ u) j) = (C *ᵥ u) j := fun j => by
    rw [RingHom.map_mulVec, hCφ, hφu]
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [GeneralLinearGroup.map_apply]
  change φ (transvMatrix C u s i j) = transvMatrix C u (φ s) i j
  simp only [transvMatrix, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    map_add, map_mul, hCu, huφ, one_apply]
  split_ifs <;> simp

theorem eq_of_transvGL_param_eq [CharP K 2] {C : GL (Fin n) K} {u : Fin n → K}
    (hu : u ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0) (hu0 : u ≠ 0) {s s' : K}
    (h : transvGL (C : Matrix (Fin n) (Fin n) K) hu s =
      transvGL (C : Matrix (Fin n) (Fin n) K) hu s') : s = s' := by
  have h1 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_transvGL, transvMatrix, add_right_inj] at h1
  have hN : vecMulVec u ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra! h0
      exact hu0 (funext h0)
    have hCu : (C : Matrix (Fin n) (Fin n) K) *ᵥ u ≠ 0 := by
      intro h0
      apply hu0
      have := congrArg (((C⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) h0
      simpa [mulVec_mulVec, Units.inv_mul] using this
    obtain ⟨j, hj⟩ : ∃ j, ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) j ≠ 0 := by
      by_contra! h0
      exact hCu (funext h0)
    intro h0
    have := congrFun (congrFun h0 i) j
    rw [vecMulVec_apply, Matrix.zero_apply] at this
    exact mul_ne_zero hi hj this
  have h2 : (s - s') • vecMulVec u ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0 := by
    rw [sub_smul, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hN)

theorem eq_one_of_fixes_pairs [CharP K 2] (hn : Odd n) {g : GL (Fin n) K}
    (hg : g ∈ matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hpair : ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) K) *ᵥ
      (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1) :
    g = 1 := by
  have : NeZero n := ⟨by obtain ⟨m, rfl⟩ := hn; omega⟩
  have hg' : (g : Matrix (Fin n) (Fin n) K)ᵀ * g = 1 := by
    simpa [mem_matrixIsometryGroup] using hg
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  set d : Fin n → K := fun _ => 1 with hd
  have hsq : ∀ x : Fin n → K, x ⬝ᵥ x = (d ⬝ᵥ x) ^ 2 := by
    intro x
    simp only [dotProduct, hd, one_mul]
    rw [sum_pow_char]
    simp only [sq]
  have hgg : ∀ x : Fin n → K,
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ⬝ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) =
        x ⬝ᵥ x := by
    intro x
    rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hg', vecMul_one]
  have hdg : ∀ x, d ⬝ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) = d ⬝ᵥ x := fun x =>
    sq_injective_of_charTwo (by rw [← hsq, ← hsq, hgg])
  have hdgv : d ᵥ* (g : Matrix (Fin n) (Fin n) K) = d := by
    funext j
    have := hdg (Pi.single j 1)
    rwa [dotProduct_mulVec, dotProduct_single_one, dotProduct_single_one] at this
  have hgd : (g : Matrix (Fin n) (Fin n) K) *ᵥ d = d := by
    have h2 : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ = 1 :=
      mul_eq_one_comm.mp hg'
    calc (g : Matrix (Fin n) (Fin n) K) *ᵥ d
        _ = (g : Matrix (Fin n) (Fin n) K) *ᵥ (d ᵥ* (g : Matrix (Fin n) (Fin n) K)) := by
          rw [hdgv]
        _ = ((g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ) *ᵥ d := by
          rw [← mulVec_transpose, mulVec_mulVec]
        _ = d := by rw [h2, one_mulVec]
  set i₀ : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hi₀
  set w : Fin n → K := fun k => (g : Matrix (Fin n) (Fin n) K) k i₀ + (if k = i₀ then 1 else 0)
    with hw
  have hentry : ∀ k i, (g : Matrix (Fin n) (Fin n) K) k i = (if k = i then 1 else 0) + w k := by
    intro k i
    by_cases hi : i = i₀
    · subst hi
      simp only [hw]
      split_ifs
      · linear_combination (-1 : K) * h22
      · ring
    · have h1 := congrFun (hpair i i₀ hi) k
      simp only [mulVec_add, Pi.add_apply, mulVec_single_one, col_apply, Pi.single_apply,
        hw] at h1 ⊢
      split_ifs at h1 ⊢ <;>
        linear_combination h1 - (g : Matrix (Fin n) (Fin n) K) k i₀ * h22
  have hw0 : ∀ k, w k = 0 := by
    intro k
    have h1 := congrFun hgd k
    simp only [mulVec, dotProduct, hd, mul_one, hentry, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    obtain ⟨m, hm⟩ := hn
    rw [hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h22, zero_mul, zero_add, Nat.cast_one,
      one_mul] at h1
    linear_combination h1
  apply Units.ext
  ext k i
  rw [hentry, hw0, add_zero, Units.val_one, one_apply]

theorem conjAut_mul_fieldAut_eq_one_of_centralizes_canonical [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {C : GL (Fin n) K} (hC : IsCanonicalGram (C : Matrix (Fin n) (Fin n) K))
    (hcase : (∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n))
    {g : GL (Fin n) K} (hg : g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K)
    (hc : ∀ h ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K),
      conjAut n K g * fieldAut n K φ * conjAut n K h * (conjAut n K g * fieldAut n K φ)⁻¹ =
        conjAut n K h) :
    conjAut n K g * fieldAut n K φ = 1 := by
  have : NeZero n := ⟨by omega⟩
  have hfix : ∀ u : Fin n → K, (∀ i, u i = 0 ∨ u i = 1) →
      ∀ hu : u ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ u = u := by
    intro u hu01 hu
    have huφ : ∀ i, (φ : K →+* K) (u i) = u i := fun i => by
      rcases hu01 i with h | h <;> simp [h]
    have hgu : ((g : Matrix (Fin n) (Fin n) K) *ᵥ u) ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u)) = 0 := by
      rw [dotProduct_mulVec_isometry hg]
      exact hu
    have h1 := hc _ (transvGL_mem hC.symm hu 1)
    rw [conj_conjAut_fieldAut, map_transvGL (φ : K →+* K) (hC.matrix_map _) huφ hu,
      map_one] at h1
    have h2 := eq_of_conjAut_eq_of_unipotent hn
      (unipotent_conj (transvGL_unipotent _ hu 1)) (transvGL_unipotent _ hu 1) h1
    rw [conj_transvGL hg hu hgu] at h2
    exact eq_of_transvGL_eq hgu hu h2 hC.symm
  obtain ⟨u₀, hu₀01, hu₀, hu₀0, hg1⟩ : ∃ u₀ : Fin n → K, (∀ i, u₀ i = 0 ∨ u₀ i = 1) ∧
      u₀ ⬝ᵥ ((C : Matrix (Fin n) (Fin n) K) *ᵥ u₀) = 0 ∧ u₀ ≠ 0 ∧ g = 1 := by
    rcases hcase with ⟨r, hr, hCJ⟩ | ⟨hC1, hodd⟩
    · have hiso : ∀ i : Fin n, (Pi.single i 1 : Fin n → K) ⬝ᵥ
          ((C : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1) = 0 := fun i => by
        rw [single_one_dotProduct, mulVec_single_one, col_apply, hCJ,
          blockSwapJ_apply_self (by omega)]
      have h01 : ∀ i : Fin n, ∀ j, (Pi.single i 1 : Fin n → K) j = 0 ∨
          (Pi.single i 1 : Fin n → K) j = 1 := fun i j => by
        by_cases h : j = i
        · exact Or.inr (by rw [h, Pi.single_eq_same])
        · exact Or.inl (Pi.single_eq_of_ne h 1)
      refine ⟨Pi.single ⟨0, by omega⟩ 1, h01 _, hiso _, fun h0 => ?_, ?_⟩
      · have := congrFun h0 ⟨0, by omega⟩
        simp at this
      · apply Units.ext
        apply Matrix.ext_of_mulVec_single
        intro i
        rw [hfix _ (h01 i) (hiso i), Units.val_one, one_mulVec]
    · have hCm : (C : Matrix (Fin n) (Fin n) K) = 1 := hC1
      have hCg : C = 1 := Units.ext hC1
      have hiso : ∀ i j : Fin n, i ≠ j → (Pi.single i 1 + Pi.single j 1 : Fin n → K) ⬝ᵥ
          ((C : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 + Pi.single j 1)) = 0 := by
        intro i j hij
        rw [hCm, one_mulVec, add_dotProduct, dotProduct_add, dotProduct_add,
          single_one_dotProduct, single_one_dotProduct, single_one_dotProduct,
          single_one_dotProduct, Pi.single_eq_same, Pi.single_eq_same,
          Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]
        have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h22
      have h01 : ∀ i j : Fin n, i ≠ j → ∀ k, (Pi.single i 1 + Pi.single j 1 : Fin n → K) k = 0 ∨
          (Pi.single i 1 + Pi.single j 1 : Fin n → K) k = 1 := by
        intro i j hij k
        simp only [Pi.add_apply, Pi.single_apply]
        by_cases hki : k = i
        · subst hki
          simp [hij]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      have hi01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      refine ⟨_, h01 _ _ hi01, hiso _ _ hi01, fun h0 => ?_, ?_⟩
      · have := congrFun h0 ⟨0, by omega⟩
        simp [Fin.ext_iff] at this
      · subst hCg
        exact eq_one_of_fixes_pairs hodd hg fun i j hij =>
          hfix _ (h01 i j hij) (hiso i j hij)
  subst hg1
  have hφ : ∀ s : K, φ s = s := by
    intro s
    have huφ : ∀ i, (φ : K →+* K) (u₀ i) = u₀ i := fun i => by
      rcases hu₀01 i with h | h <;> simp [h]
    have h1 := hc _ (transvGL_mem hC.symm hu₀ s)
    rw [conj_conjAut_fieldAut, map_transvGL (φ : K →+* K) (hC.matrix_map _) huφ hu₀,
      one_mul, inv_one, mul_one] at h1
    have h2 := eq_of_conjAut_eq_of_unipotent hn (transvGL_unipotent _ hu₀ _)
      (transvGL_unipotent _ hu₀ s) h1
    exact eq_of_transvGL_param_eq hu₀ hu₀0 h2
  have hφ1 : φ = 1 := RingEquiv.ext hφ
  rw [hφ1, map_one, map_one, one_mul]

theorem finite_mulAut_projectiveSL [Finite K] : Finite (MulAut (projectiveSL n K)) :=
  Finite.of_injective (fun e : MulAut (projectiveSL n K) =>
    (e : projectiveSL n K → projectiveSL n K)) fun _ _ hab => MulEquiv.ext (congrFun hab)


theorem even_linear_canonical_graph_symplectic_centralizers {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) :
    Function.Injective
        ((conjAut n K).comp (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).subtype) ∧
      (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≤
        (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
      (conjAut n K C * dualAut n K) ^ 2 = 1 ∧
      (centralizer {conjAut n K C * dualAut n K} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ g ∈ matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K), ∃ (φ : K ≃+* K) (ε : ℕ),
          ε ≤ 1 ∧ α = conjAut n K g * fieldAut n K φ * (conjAut n K C * dualAut n K) ^ ε} ∧
      (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≤
        centralizer {conjAut n K C * dualAut n K} ∧
      (((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K)).subgroupOf
        (centralizer {conjAut n K C * dualAut n K})).Normal ∧
      ((∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∨
          ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ Odd n) →
        centralizer {conjAut n K C * dualAut n K} ⊓
            centralizer (((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map
              (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
                Set (MulAut (projectiveSL n K))) =
          zpowers (conjAut n K C * dualAut n K) ∧
        ∀ H : Subgroup (MulAut (projectiveSL n K)),
          (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ H →
          ¬(n = 3 ∧ Nat.card K = 2 ∧ (C : Matrix (Fin n) (Fin n) K) = 1) →
          CFSG.oddCore ↥(H ⊓ centralizer {conjAut n K C * dualAut n K}) = ⊥) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero n := ⟨by omega⟩
  have hCan : IsCanonicalGram (C : Matrix (Fin n) (Fin n) K) := by
    rcases hC with h1 | ⟨r, hr, hJ⟩
    · rw [h1]
      exact isCanonicalGram_one
    · rw [hJ]
      exact isCanonicalGram_blockSwapJ (by omega)
  set β := conjAut n K C * dualAut n K with hβ
  set O := matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) with hO
  set N := O.map (conjAut n K) with hN
  have hθf := commute_pureGraph_fieldAut hCan
  have hθd := commute_pureGraph_dualAut hCan
  have hG : ∀ A : GL (Fin n) K, Commute β (conjAut n K A) ↔
      ∃ B ∈ (O : Set (GL (Fin n) K)), conjAut n K A = conjAut n K B :=
    fun A => commute_pureGraph_conjAut_iff hCan hn A
  have hSG : ∀ B ∈ (O : Set (GL (Fin n) K)), ∀ g ∈ O, B * g * B⁻¹ ∈ O :=
    fun B hB g hg => mul_mem (mul_mem hB hg) (inv_mem hB)
  have hSφ : ∀ φ : K ≃+* K, ∀ g ∈ O, GeneralLinearGroup.map (φ : K →+* K) g ∈ O := by
    intro φ g hg
    rw [hO, mem_matrixIsometryGroup_iff_inverseTranspose] at hg ⊢
    rw [← GeneralLinearGroup.map_inverseTranspose, hg, map_mul, map_mul, map_inv,
      hCan.map_eq]
  have hSδ : ∀ g ∈ O, GeneralLinearGroup.inverseTranspose g ∈ O := by
    intro g hg
    rw [(mem_matrixIsometryGroup_iff_inverseTranspose C g).mp hg]
    exact mul_mem (mul_mem hCan.mem hg) (inv_mem hCan.mem)
  have hNβ : ∀ g ∈ O, Commute β (conjAut n K g) := fun g hg => (hG g).mpr ⟨g, hg, rfl⟩
  have hinj : Function.Injective ((conjAut n K).comp O.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn (g : GL (Fin n) K)).mp hg
    have hc1 := eq_one_of_scalar_mem_matrixIsometryGroup (C := C) (hc ▸ g.2)
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  have hinner : N ≤ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    rintro _ ⟨g, hg, rfl⟩
    let g' : SpecialLinearGroup (Fin n) K :=
      ⟨(g : Matrix (Fin n) (Fin n) K), det_eq_one_of_mem_matrixIsometryGroup hg⟩
    refine ⟨proj n K g', ?_⟩
    rw [← conjAut_toGL]
    exact congrArg (conjAut n K) (Units.ext rfl)
  have hM := centralizer_eq_of_conjAut_commute_iff hn hθf hθd (O : Set (GL (Fin n) K)) hG
  have hNM : N ≤ centralizer {β} := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hNβ g hg).eq.symm
  have hnormal := normal_of_conjAut_closed hn hθf hθd (O : Set (GL (Fin n) K)) hG O hSG hSφ hSδ
  have hβ2 : β ^ 2 = 1 := pureGraph_sq hCan
  have hCinv := hCan.inv_eq
  have hMβ : (centralizer {β} : Set (MulAut (projectiveSL n K))) =
      {α | ∃ g ∈ O, ∃ (φ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
        α = conjAut n K g * fieldAut n K φ * β ^ ε} := by
    rw [hM]
    ext α
    constructor
    · rintro ⟨B, hB, φ, ε, hε, rfl⟩
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · exact ⟨B, hB, φ, 0, hε, by rw [pow_zero, pow_zero]⟩
      · refine ⟨B * C⁻¹, mul_mem hB (inv_mem hCan.mem), φ, 1, le_rfl, ?_⟩
        rw [pow_one, pow_one, hβ, map_mul, map_inv]
        have e := fieldAut_mul_conjAut_canonical hCan φ
        calc conjAut n K B * fieldAut n K φ * dualAut n K
            _ = conjAut n K B * (conjAut n K C)⁻¹ * (conjAut n K C * fieldAut n K φ) *
                dualAut n K := by group
            _ = conjAut n K B * (conjAut n K C)⁻¹ * (fieldAut n K φ * conjAut n K C) *
                dualAut n K := by rw [e]
            _ = _ := by group
    · rintro ⟨g, hg, φ, ε, hε, rfl⟩
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · exact ⟨g, hg, φ, 0, hε, by rw [pow_zero, pow_zero]⟩
      · refine ⟨g * C, mul_mem hg hCan.mem, φ, 1, le_rfl, ?_⟩
        rw [pow_one, pow_one, hβ, map_mul]
        have e := fieldAut_mul_conjAut_canonical hCan φ
        calc conjAut n K g * fieldAut n K φ * (conjAut n K C * dualAut n K)
            _ = conjAut n K g * (fieldAut n K φ * conjAut n K C) * dualAut n K := by group
            _ = conjAut n K g * (conjAut n K C * fieldAut n K φ) * dualAut n K := by rw [e]
            _ = _ := by group
  refine ⟨hinj, hinner, hβ2, hMβ, hNM, hnormal, fun hcase => ?_⟩
  have hβN : β ∈ centralizer (N : Set (MulAut (projectiveSL n K))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    exact (hNβ h hh).eq.symm
  have hCMN : centralizer {β} ⊓ centralizer (N : Set (MulAut (projectiveSL n K))) =
      zpowers β := by
    apply le_antisymm
    · intro α hα
      obtain ⟨hαM, hαN⟩ := mem_inf.mp hα
      have hα' : α ∈ (centralizer {β} : Set (MulAut (projectiveSL n K))) := hαM
      rw [hMβ] at hα'
      obtain ⟨g, hg, φ, ε, hε, rfl⟩ := hα'
      have hx : conjAut n K g * fieldAut n K φ ∈
          centralizer (N : Set (MulAut (projectiveSL n K))) := by
        have := mul_mem hαN (inv_mem (pow_mem hβN ε))
        rwa [mul_inv_cancel_right] at this
      have hx1 := conjAut_mul_fieldAut_eq_one_of_centralizes_canonical hn hCan hcase hg φ
        fun h hh => by
          have := mem_centralizer_iff.mp hx (conjAut n K h) (mem_map_of_mem _ hh)
          rw [← this, mul_inv_cancel_right]
      rw [hx1, one_mul]
      exact pow_mem (mem_zpowers β) ε
    · rw [zpowers_le]
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hβN⟩
  refine ⟨hCMN, fun H hH hexc => ?_⟩
  have hOodd : CFSG.oddCore O = ⊥ := by
    rcases hcase with ⟨r, hr, hJ⟩ | ⟨h1, hodd⟩
    · exact oddCore_matrixIsometryGroup_blockSwapJ hf hK hn hr hJ
    · have hC1 : C = 1 := Units.ext h1
      obtain ⟨r, hr⟩ := hodd
      have hr1 : 1 ≤ r := by omega
      have h24 : 2 ≤ r ∨ 4 ≤ Nat.card K := by
        by_contra! hcon
        have hf1 : f = 1 := by
          by_contra hf1
          have h4 : 4 ≤ 2 ^ f := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact hexc ⟨by omega, by rw [hK, hf1, pow_one], h1⟩
      rw [hO, hC1]
      exact oddCore_matrixIsometryGroup_one hf hK hr hr1 h24
  have hrange : ((conjAut n K).comp O.subtype).range = N := by
    rw [MonoidHom.range_comp, range_subtype]
  have hNodd : CFSG.oddCore N = ⊥ :=
    EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)) hOodd
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut_projectiveSL
  set Y := H ⊓ centralizer {β} with hY
  have hNY : N ≤ Y := le_inf (hinner.trans hH) hNM
  have hN'normal : (N.subgroupOf Y).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    have hyM : (y : MulAut (projectiveSL n K)) ∈ centralizer {β} := (mem_inf.mp y.2).2
    have hxM : (x : MulAut (projectiveSL n K)) ∈ centralizer {β} := (mem_inf.mp x.2).2
    have := hnormal.conj_mem ⟨x, hxM⟩ (mem_subgroupOf.mpr hx) ⟨y, hyM⟩
    rw [mem_subgroupOf] at this
    exact this
  have hN'odd : CFSG.oddCore (N.subgroupOf Y) = ⊥ :=
    EvenCatalog.oddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNY).symm hNodd
  have hcentY : ∀ y ∈ centralizer ((N.subgroupOf Y : Subgroup Y) : Set Y), y ^ 2 = 1 := by
    intro y hy
    have hyz : (y : MulAut (projectiveSL n K)) ∈ zpowers β := by
      rw [← hCMN]
      refine mem_inf.mpr ⟨(mem_inf.mp y.2).2, ?_⟩
      rw [mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val
        (mem_centralizer_iff.mp hy ⟨x, hNY hx⟩ (mem_subgroupOf.mpr hx))
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyz
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hβ2, _root_.one_zpow]
    rfl
  exact oddCore_eq_bot_of_normal_of_centralizer hN'normal hN'odd hcentY

end CFSG.ComponentClassification.UnbalancedCatalog
