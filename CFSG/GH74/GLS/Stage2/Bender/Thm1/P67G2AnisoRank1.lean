module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
import CFSG.GH74.Filter.Lie.TwistedE6Odd

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.RankThree.Chevalley
open scoped MatrixGroups commutatorElement

section Pure

variable {L : Type} [Field L]

def diagSL2 : Subgroup SL(2, L) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA1, hA2, hB1, hB2]
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hA1, hA2]

theorem mem_diagSL2 {A : SL(2, L)} :
    A ∈ (diagSL2 : Subgroup SL(2, L)) ↔
      (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := Iff.rfl

theorem monomial_of_conj_diag {χ : L} (hχ : χ ≠ 1) {A : SL(2, L)}
    (h : ∀ i j : Fin 2, i ≠ j →
      ((A : Matrix (Fin 2) (Fin 2) L) * !![χ, 0; 0, 1] *
        ((A⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L)) i j = 0) :
    ((A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) ∨
      ((A : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) := by
  have h01 := h 0 1 (by decide)
  have h10 := h 1 0 (by decide)
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two] at h01 h10
  have hsub : (1 : L) - χ ≠ 0 := sub_ne_zero.2 (Ne.symm hχ)
  have e1 : (A : Matrix (Fin 2) (Fin 2) L) 0 0 * (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    have : (A : Matrix (Fin 2) (Fin 2) L) 0 0 * (A : Matrix (Fin 2) (Fin 2) L) 0 1 * (1 - χ) =
        0 := by
      linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right hsub
  have e2 : (A : Matrix (Fin 2) (Fin 2) L) 1 0 * (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := by
    have : (A : Matrix (Fin 2) (Fin 2) L) 1 0 * (A : Matrix (Fin 2) (Fin 2) L) 1 1 * (χ - 1) =
        0 := by
      linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hχ)
  rcases mul_eq_zero.1 e1 with h00 | h01'
  · right
    refine ⟨h00, ?_⟩
    rcases mul_eq_zero.1 e2 with h10' | h11
    · rw [h00, h10'] at hdet
      simp at hdet
    · exact h11
  · left
    refine ⟨h01', ?_⟩
    rcases mul_eq_zero.1 e2 with h10' | h11
    · exact h10'
    · rw [h01', h11] at hdet
      simp at hdet


def IsMono (A : SL(2, L)) : Prop :=
  ((A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) ∨
    ((A : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0)

theorem commutator_mem_diagSL2 {A B : SL(2, L)} (hA : IsMono A) (hB : IsMono B) :
    ⁅A, B⁆ ∈ (diagSL2 : Subgroup SL(2, L)) := by
  rw [mem_diagSL2]
  have hAd := A.2
  have hBd := B.2
  rw [Matrix.det_fin_two] at hAd hBd
  rcases hA with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hB with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
  · simp [commutatorElement_def, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2] at hAd hBd ⊢


theorem false_of_monomial_conj_perfect {χ : L} (hχ : χ ≠ 1) (S : Subgroup SL(2, L))
    (hperf : ⁅S, S⁆ = S) (hnab : ∃ A ∈ S, ∃ B ∈ S, A * B ≠ B * A)
    (hdiag : ∀ A ∈ S, ∀ i j : Fin 2, i ≠ j →
      ((A : Matrix (Fin 2) (Fin 2) L) * !![χ, 0; 0, 1] *
        ((A⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L)) i j = 0) : False := by
  have hmono : ∀ A ∈ S, IsMono A := fun A hA => monomial_of_conj_diag hχ (hdiag A hA)
  have hcomm : ⁅S, S⁆ ≤ (diagSL2 : Subgroup SL(2, L)) :=
    Subgroup.commutator_le.2 fun A hA B hB => commutator_mem_diagSL2 (hmono A hA) (hmono B hB)
  have hSd : S ≤ (diagSL2 : Subgroup SL(2, L)) := hperf ▸ hcomm
  obtain ⟨A, hA, B, hB, hne⟩ := hnab
  apply hne
  obtain ⟨ha1, ha2⟩ := hSd hA
  obtain ⟨hb1, hb2⟩ := hSd hB
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1, ha2, hb1, hb2, mul_comm]



theorem eq_scalar_of_conjSL_eq' {L : Type} [Field L] {A : GL (Fin 2) L}
    (hA : ∀ g : SL(2, L), conjSL A g = g) :
    ∃ c : Lˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have hcomm : ∀ g : SL(2, L), (A : Matrix (Fin 2) (Fin 2) L) * g =
      (g : Matrix (Fin 2) (Fin 2) L) * A := fun g => commute_of_conjSL_eq A (hA g)
  have e1 := hcomm (sl2Upper L 1)
  have e2 := hcomm (sl2Lower L 1)
  have h10 : (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    have := congrFun (congrFun e1 1) 1
    simpa [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    have := congrFun (congrFun e2 0) 0
    simpa [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (A : Matrix (Fin 2) (Fin 2) L) 1 1 = (A : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    have := congrFun (congrFun e1 0) 1
    simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  have h00 : (A : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h0
    have hdet := (Matrix.isUnits_det_units A).ne_zero
    rw [Matrix.det_fin_two, h0, h01] at hdet
    simp at hdet
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.scalar, h01, h10, h11]



theorem sl2_map_injective {K K₂ : Type} [Field K] [Field K₂] (ι : K →+* K₂) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) ι) :=
  CFSG.GH74.Filter.Lie.sl2_map_injective ι

theorem conjSL_injective (P : GL (Fin 2) L) : Function.Injective (conjSL P) := fun A B h => by
  have h1 := congrArg (conjSL P⁻¹) h
  rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1

theorem natCard_specialLinear_two {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

end Pure

section Rank1

variable {K₂ : Type} [Field K₂]

theorem conj_mem_torus_matrix {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (c : Fin Tag.G2.rank → K₂ˣ) (A : SL2 K₂) {c' : Fin Tag.G2.rank → K₂ˣ}
    (hc' : rootSL2 .G2 K₂ α A * rootDiagUnit .G2 c * (rootSL2 .G2 K₂ α A)⁻¹ =
      rootDiagUnit .G2 c') (B : SL2 K₂) :
    conjSL (Matrix.SpecialLinearGroup.toGL A * diagUnitOne (rootChar c α) *
        (Matrix.SpecialLinearGroup.toGL A)⁻¹) B =
      conjSL (diagUnitOne (rootChar c' α)) B := by
  have hinj := rootSL2_injective_of_field (K := K₂) (τ := .G2) α
  apply hinj
  rw [← rootDiagUnit_conj_rootSL2 c' hα B, ← hc']
  have e : ∀ X : SL2 K₂, rootDiagUnit .G2 c * rootSL2 .G2 K₂ α X * (rootDiagUnit .G2 c)⁻¹ =
      rootSL2 .G2 K₂ α (conjSL (diagUnitOne (rootChar c α)) X) :=
    fun X => rootDiagUnit_conj_rootSL2 c hα X
  have hM : conjSL (Matrix.SpecialLinearGroup.toGL A * diagUnitOne (rootChar c α) *
        (Matrix.SpecialLinearGroup.toGL A)⁻¹) B =
      A * conjSL (diagUnitOne (rootChar c α)) (A⁻¹ * B * A) * A⁻¹ := by
    rw [conjSL_mul, conjSL_mul, ← map_inv, conjSL_toGL, conjSL_toGL, inv_inv]
  rw [hM]
  have step1 : rootSL2 .G2 K₂ α A * rootDiagUnit .G2 c * (rootSL2 .G2 K₂ α A)⁻¹ *
      rootSL2 .G2 K₂ α B *
        (rootSL2 .G2 K₂ α A * rootDiagUnit .G2 c * (rootSL2 .G2 K₂ α A)⁻¹)⁻¹ =
      rootSL2 .G2 K₂ α A * (rootDiagUnit .G2 c * rootSL2 .G2 K₂ α (A⁻¹ * B * A) *
        (rootDiagUnit .G2 c)⁻¹) * (rootSL2 .G2 K₂ α A)⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [step1, e, ← map_inv, ← map_mul, ← map_mul]


theorem rootChar_eq_one_of_conj_mem_torus {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (c : Fin Tag.G2.rank → K₂ˣ) (S : Subgroup (SL2 K₂)) (hperf : ⁅S, S⁆ = S)
    (hnab : ∃ A ∈ S, ∃ B ∈ S, A * B ≠ B * A)
    (hconj : ∀ A ∈ S, rootSL2 .G2 K₂ α A * rootDiagUnit .G2 c * (rootSL2 .G2 K₂ α A)⁻¹ ∈
      torusGroup .G2 K₂) : rootChar c α = 1 := by
  by_contra hχ
  refine false_of_monomial_conj_perfect (χ := ((rootChar c α : K₂ˣ) : K₂))
    (fun h => hχ (Units.ext h)) S hperf hnab ?_
  intro A hA i j hij
  obtain ⟨c', hc'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hconj A hA)
  have key := conj_mem_torus_matrix hα c A hc'
  have hscal : ∀ B : SL2 K₂, conjSL ((diagUnitOne (rootChar c' α))⁻¹ *
      (Matrix.SpecialLinearGroup.toGL A * diagUnitOne (rootChar c α) *
        (Matrix.SpecialLinearGroup.toGL A)⁻¹)) B = B := by
    intro B
    rw [conjSL_mul, key, ← conjSL_mul, inv_mul_cancel, conjSL_one]
  obtain ⟨u, hu⟩ := eq_scalar_of_conjSL_eq' hscal
  have hM : Matrix.SpecialLinearGroup.toGL A * diagUnitOne (rootChar c α) *
      (Matrix.SpecialLinearGroup.toGL A)⁻¹ =
        diagUnitOne (rootChar c' α) * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hu, mul_inv_cancel_left]
  have hcoe := congrArg (fun X : GL (Fin 2) K₂ => (X : Matrix (Fin 2) (Fin 2) K₂)) hM
  simp only [Units.val_mul, coe_diagUnitOne, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    ← map_inv] at hcoe
  rw [hcoe]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]


theorem commute_rootSL2_diag_of_rootChar_eq_one {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (c : Fin Tag.G2.rank → K₂ˣ) (hχ : rootChar c α = 1) (A : SL2 K₂) :
    rootSL2 .G2 K₂ α A * rootDiagUnit .G2 c = rootDiagUnit .G2 c * rootSL2 .G2 K₂ α A := by
  have h := rootDiagUnit_conj_rootSL2 c hα A
  rw [hχ] at h
  have h1 : diagUnitOne (1 : K₂ˣ) = 1 :=
    Units.ext (by
      rw [coe_diagUnitOne]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
  rw [h1, conjSL_one] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

end Rank1

section Fixed

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem exists_fixedRankOne_eq_map (hK : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ φ : SL2 K →* SL2 K₂, Function.Injective φ ∧
      (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) =
        (⊤ : Subgroup (SL2 K)).map φ := by
  obtain ⟨P, hP, -⟩ := rootSL2_comap_fixed_eq hK hdeg σ hσ hg hzdef hz hw hα
  refine ⟨(conjSL P).comp (Matrix.SpecialLinearGroup.map (algebraMap K K₂)),
    (conjSL_injective P).comp (sl2_map_injective (algebraMap K K₂)), ?_⟩
  rw [hP, MonoidHom.range_eq_map, Subgroup.map_map]

theorem rootChar_eq_one_of_conj_mem_torus_fixed (hK : Odd (Nat.card K)) (hK4 : 4 ≤ Nat.card K)
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (c : Fin Tag.G2.rank → K₂ˣ)
    (hconj : ∀ r ∈ rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g,
      r * rootDiagUnit .G2 c * r⁻¹ ∈ torusGroup .G2 K₂) :
    rootChar c α = 1 := by
  obtain ⟨φ, hφ, hS⟩ := exists_fixedRankOne_eq_map hK hdeg σ hσ hg hzdef hz hw hα
  set S : Subgroup (SL2 K₂) :=
    (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) with hSdef
  have hperfK : ⁅(⊤ : Subgroup (SL2 K)), (⊤ : Subgroup (SL2 K))⁆ = (⊤ : Subgroup (SL2 K)) := by
    have h := (isQuasisimple_SL2 (exists_finset_card_four hK4)).1
    rw [Group.isPerfect_def] at h
    rwa [commutator_def] at h
  have hperf : ⁅S, S⁆ = S := by
    rw [hS, ← Subgroup.map_commutator, hperfK]
  have hnab : ∃ A ∈ S, ∃ B ∈ S, A * B ≠ B * A := by
    refine ⟨φ (uSL 1), ?_, φ (vSL 1), ?_, fun h => uSL_mul_vSL_ne (K := K) (hφ ?_)⟩
    · rw [hS]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩
    · rw [hS]
      exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_top _, rfl⟩
    · rw [map_mul, map_mul]
      exact h
  exact rootChar_eq_one_of_conj_mem_torus hα c S hperf hnab fun A hA => hconj _ hA

theorem natCard_rootRankOne_inf_conjEntrywiseImage (hK : Odd (Nat.card K))
    (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K)
    {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    Nat.card ↥(rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨φ, hφ, hS⟩ := exists_fixedRankOne_eq_map hK hdeg σ hσ hg hzdef hz hw hα
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hmap : ((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap
      (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α) =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right inf_le_left
  rw [← hmap, Subgroup.card_map_of_injective hinj, hS, Subgroup.card_map_of_injective hφ,
    Subgroup.card_top]
  exact natCard_specialLinear_two

end Fixed

end CFSG.GH74.GLS.Stage2.Bender.Thm1
