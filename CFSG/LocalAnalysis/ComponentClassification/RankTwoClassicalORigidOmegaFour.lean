module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOFourPerf
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinBarW

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem noNormalTwo_of_isQuasisimple {H : Subgroup G} (hH : CFSG.IsQuasisimple ↥H)
    (hodd : Odd (Nat.card (center ↥H))) : NoNormalTwo H := by
  intro R hR hR2 hN
  have : (R.subgroupOf H).Normal :=
    ⟨fun n hn g => (mem_normalizer_iff.mp (hN g.2) n).mp hn⟩
  have h2 : IsPGroup 2 ↥(R.subgroupOf H) := hR2.of_equiv (subgroupOfEquivOfLe hR).symm
  have hbot := eq_bot_of_normal_isPGroup_two_of_quasisimple hH hodd _ h2
  rw [eq_bot_iff]
  intro r hr
  have h3 : (⟨r, hR hr⟩ : ↥H) ∈ R.subgroupOf H := hr
  rw [hbot, mem_bot] at h3
  rw [mem_bot]
  exact congrArg Subtype.val h3

end Generic

section SL

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem noNormalTwo_top_sl_two (h4 : 4 ≤ Nat.card K) : NoNormalTwo (⊤ : Subgroup SL(2, K)) := by
  refine noNormalTwo_of_isQuasisimple ?_ ?_
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
      (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_four h4))
  · have hc : center ↥(⊤ : Subgroup SL(2, K)) = ⊥ := by
      rw [← Subgroup.map_center_eq (Subgroup.topEquiv (G := SL(2, K))).symm,
        center_SL2_eq_bot', Subgroup.map_bot]
    rw [hc, Subgroup.card_bot]
    exact odd_one

end SL

section Struct

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_rho_of_mem_statedOmega_quadPlus_two {Y : GL (Fin 2 ⊕ Fin 2) K}
    (hY : Y ∈ StatedOmega (StatedQuadPlus 2 K)) :
    ∃ A B : SL(2, K),
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = rhoOneMat A * rhoTwoMat B := by
  have h1 : oPhi K Y ∈ ⁅DeterminantIsometries K, DeterminantIsometries K⁆ := by
    rw [← map_statedOmega_oPhi]
    exact ⟨Y, hY, rfl⟩
  have h2 : ⁅DeterminantIsometries K, DeterminantIsometries K⁆ ≤
      (specialImage K).map (DeterminantIsometries K).subtype := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact ⟨_, commutator_mem_specialImage_charTwo ⟨g, hg⟩ ⟨h, hh⟩, rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := h2 h1
  have h3 : ∀ X, (oPhi K Y) X = (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
      ((z.2⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := fun X => by
    rw [← hz]
    exact specialRho_apply z X
  have hdet : (((z.2⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ).det = 1 := by
    rw [det_transpose]
    exact (z.2⁻¹).2
  obtain ⟨B, hB⟩ : ∃ B : SL(2, K), (B : Matrix (Fin 2) (Fin 2) K) =
      ((z.2⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ := ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨z.1, B, oMat_injective_mulVec (K := K) fun v => ?_⟩
  rw [← mulVec_mulVec, rhoOneMat_eq_shape, oMat_rhoOneShape, oMat_rhoTwoMat, hB,
    transpose_transpose]
  have h4 := h3 (oMat K v)
  rw [oPhi_apply, LinearEquiv.symm_apply_apply] at h4
  rw [h4, Matrix.mul_assoc]

end Struct

section NoTwo

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem noNormalTwo_range_of_injective {G : Type} [Group G] [Finite G] {f : SL(2, K) →* G}
    (hf : Function.Injective f) (h4 : 4 ≤ Nat.card K) : NoNormalTwo f.range := by
  refine noNormalTwo_of_isQuasisimple ?_ ?_
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hf)
      (CFSG.RankThree.Classical.isQuasisimple_SL2 (exists_finset_four h4))
  · have hc : center ↥f.range = ⊥ := by
      rw [← Subgroup.map_center_eq (MonoidHom.ofInjective hf),
        center_SL2_eq_bot', Subgroup.map_bot]
    rw [hc, Subgroup.card_bot]
    exact odd_one

omit [CharP K 2] [Finite K] in
theorem rhoOneMat_toHomUnits_injective :
    Function.Injective (rhoOneMat (K := K)).toHomUnits := by
  intro B B' h
  have h1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [MonoidHom.coe_toHomUnits] at h1
  rw [rhoOneMat_apply, rhoOneMat_apply, fromBlocks_inj] at h1
  obtain ⟨e1, e2, e3, e4⟩ := h1
  have f1 := congrFun (congrFun e1 0) 0
  have f2 := congrFun (congrFun e2 0) 1
  have f3 := congrFun (congrFun e3 1) 0
  have f4 := congrFun (congrFun e4 0) 0
  simp [swapM] at f1 f2 f3 f4
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

omit [CharP K 2] [Finite K] in
theorem rhoTwoMat_toHomUnits_injective :
    Function.Injective (rhoTwoMat (K := K)).toHomUnits := by
  intro A A' h
  have h1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [MonoidHom.coe_toHomUnits] at h1
  rw [rhoTwoMat_apply, rhoTwoMat_apply, fromBlocks_inj] at h1
  exact Subtype.ext h1.1

theorem noNormalTwo_statedOmega_quadPlus_two (h4 : 4 ≤ Nat.card K) :
    NoNormalTwo (StatedOmega (StatedQuadPlus 2 K)) := by
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_four h4)).commutator_eq_top
  set H₁ := (rhoOneMat (K := K)).toHomUnits.range with hH₁
  set H₂ := (rhoTwoMat (K := K)).toHomUnits.range with hH₂
  have hH₁Ω : H₁ ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rintro _ ⟨B, rfl⟩
    refine mem_statedOmega_of_perfect hSL (rhoOneMat (K := K)).toHomUnits
      (fun B' => subset_closure fun v => ?_) B
    simp only [MonoidHom.coe_toHomUnits]
    exact quadPlus_two_rhoOne B' v
  have hH₂Ω : H₂ ≤ StatedOmega (StatedQuadPlus 2 K) := by
    rintro _ ⟨A, rfl⟩
    refine mem_statedOmega_of_perfect hSL (rhoTwoMat (K := K)).toHomUnits
      (fun A' => subset_closure fun v => ?_) A
    simp only [MonoidHom.coe_toHomUnits]
    exact quadPlus_two_rhoTwo A' v
  have hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := by
    rintro _ ⟨B, rfl⟩ _ ⟨A, rfl⟩
    apply Units.ext
    simp only [Units.val_mul, MonoidHom.coe_toHomUnits]
    exact rhoOne_mul_rhoTwo A B
  have hΩ : ∀ Y ∈ StatedOmega (StatedQuadPlus 2 K), ∃ a ∈ H₁, ∃ b ∈ H₂, Y = a * b := by
    intro Y hY
    obtain ⟨B, A, hBA⟩ := exists_rho_of_mem_statedOmega_quadPlus_two hY
    refine ⟨_, ⟨B, rfl⟩, _, ⟨A, rfl⟩, Units.ext ?_⟩
    rw [Units.val_mul, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits]
    exact hBA
  intro R hR hR2 hN
  have hmeet : ∀ {H : Subgroup (GL (Fin 2 ⊕ Fin 2) K)}, NoNormalTwo H →
      H ≤ StatedOmega (StatedQuadPlus 2 K) → R ⊓ H = ⊥ := by
    intro H hH hHΩ
    refine hH _ inf_le_right (hR2.to_le inf_le_left) fun h hh => ?_
    rw [mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hgR, hgH⟩
      exact ⟨(mem_normalizer_iff.mp (hN (hHΩ hh)) g).mp hgR,
        mul_mem (mul_mem hh hgH) (inv_mem hh)⟩
    · rintro ⟨hgR, hgH⟩
      refine ⟨(mem_normalizer_iff.mp (hN (hHΩ hh)) g).mpr hgR, ?_⟩
      have := mul_mem (mul_mem (inv_mem hh) hgH) hh
      rwa [show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this
  have hR₁ := hmeet (noNormalTwo_range_of_injective rhoOneMat_toHomUnits_injective h4) hH₁Ω
  have hR₂ := hmeet (noNormalTwo_range_of_injective rhoTwoMat_toHomUnits_injective h4) hH₂Ω
  have hcomm : ∀ r ∈ R, ∀ Y ∈ StatedOmega (StatedQuadPlus 2 K), r * Y = Y * r := by
    intro r hr Y hY
    obtain ⟨a', ha', b', hb', rfl⟩ := hΩ r (hR hr)
    have hrR : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ⁅a' * b', g⁆ ∈ R := fun g hg => by
      rw [commutatorElement_def, show a' * b' * g * (a' * b')⁻¹ * g⁻¹ =
        a' * b' * (g * (a' * b')⁻¹ * g⁻¹) by group]
      exact mul_mem hr ((mem_normalizer_iff.mp (hN hg) _).mp (inv_mem hr))
    have h₁ : ∀ a ∈ H₁, (a' * b') * a = a * (a' * b') := by
      intro a ha
      have e : ⁅a' * b', a⁆ = a' * a * a'⁻¹ * a⁻¹ := by
        calc ⁅a' * b', a⁆ = a' * (b' * a * b'⁻¹) * a'⁻¹ * a⁻¹ := by
              rw [commutatorElement_def]
              group
          _ = a' * a * a'⁻¹ * a⁻¹ := by rw [← hc a ha b' hb', mul_inv_cancel_right]
      have hmem : ⁅a' * b', a⁆ ∈ R ⊓ H₁ := by
        refine Subgroup.mem_inf.mpr ⟨hrR a (hH₁Ω ha), ?_⟩
        rw [e]
        exact mul_mem (mul_mem (mul_mem ha' ha) (inv_mem ha')) (inv_mem ha)
      rw [hR₁, mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    have h₂ : ∀ b ∈ H₂, (a' * b') * b = b * (a' * b') := by
      intro b hb
      have hX : b' * b * b'⁻¹ ∈ H₂ := mul_mem (mul_mem hb' hb) (inv_mem hb')
      have e : ⁅a' * b', b⁆ = b' * b * b'⁻¹ * b⁻¹ := by
        calc ⁅a' * b', b⁆ = a' * (b' * b * b'⁻¹) * a'⁻¹ * b⁻¹ := by
              rw [commutatorElement_def]
              group
          _ = b' * b * b'⁻¹ * b⁻¹ := by rw [hc a' ha' _ hX, mul_inv_cancel_right]
      have hmem : ⁅a' * b', b⁆ ∈ R ⊓ H₂ := by
        refine Subgroup.mem_inf.mpr ⟨hrR b (hH₂Ω hb), ?_⟩
        rw [e]
        exact mul_mem hX (inv_mem hb)
      rw [hR₂, mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hΩ Y hY
    rw [← mul_assoc, h₁ a ha, mul_assoc, h₂ b hb, ← mul_assoc]
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨d, hd⟩ := commutant_statedOmega_quadPlus (K := K) (by omega) (k := 2) le_rfl
    (r : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) fun Z hZ => by
      rw [← Units.val_mul, ← Units.val_mul, hcomm r hr Z hZ]
  have hv : StatedQuadPlus 2 K (plusVec (K := K) (by omega : 1 ≤ 2)) ≠ 0 := by
    rw [statedQuadPlus_plusVec]
    exact one_ne_zero
  have hiso := quad_mulVec_of_mem_statedOmega (hR hr) (plusVec (K := K) (by omega : 1 ≤ 2))
  rw [hd, Matrix.smul_mulVec, one_mulVec, statedQuadPlus_smul] at hiso
  have hd1 : d = 1 := by
    have h1 : d * d = 1 * 1 := by
      rw [one_mul]
      exact (mul_eq_right₀ hv).mp hiso
    exact eq_of_mul_self_eq h1
  rw [mem_bot]
  apply Units.ext
  rw [hd, hd1, one_smul, Units.val_one]

end NoTwo

section Fix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

omit [CharP K 2] [Finite K] in
theorem eq_zero_of_mul_eq_self {t a : K} (ht : t ≠ 1) (h : t * a = a) : a = 0 := by
  have h1 : (t - 1) * a = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr ht)

omit [CharP K 2] in
theorem eq_zero_of_forall_statedOmega_quadPlus_two (h4 : 4 ≤ Nat.card K)
    {w : Fin 2 ⊕ Fin 2 → K}
    (hw : ∀ Y ∈ StatedOmega (StatedQuadPlus 2 K), (Y : Matrix _ _ K) *ᵥ w = w) : w = 0 := by
  have hSL : commutator SL(2, K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_two_perfect
      (exists_finset_four h4)).commutator_eq_top
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one h4
  obtain ⟨A, hA⟩ := exists_diag_sl2 ht0
  have hmem : (rhoTwoMat (K := K)).toHomUnits A ∈ StatedOmega (StatedQuadPlus 2 K) := by
    refine mem_statedOmega_of_perfect hSL (rhoTwoMat (K := K)).toHomUnits
      (fun A' => subset_closure fun v => ?_) A
    simp only [MonoidHom.coe_toHomUnits]
    exact quadPlus_two_rhoTwo A' v
  have h := hw _ hmem
  simp only [MonoidHom.coe_toHomUnits] at h
  have ht1' : t⁻¹ ≠ 1 := fun h' => ht1 (inv_eq_one.mp h')
  have hadj : adjugate (A : Matrix (Fin 2) (Fin 2) K) = !![t⁻¹, 0; 0, t] := by
    rw [hA, adjugate_fin_two_of]
    simp
  funext c
  have hc := congrFun h c
  rw [rhoTwoMat_apply, hadj, hA] at hc
  rcases c with s | s <;> fin_cases s
  · refine eq_zero_of_mul_eq_self ht1 ?_
    simpa [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] using hc
  · refine eq_zero_of_mul_eq_self ht1' ?_
    simpa [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] using hc
  · refine eq_zero_of_mul_eq_self ht1' ?_
    simpa [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] using hc
  · refine eq_zero_of_mul_eq_self ht1 ?_
    simpa [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] using hc

end Fix

end CFSG.ComponentClassification.RankTwoClassical.ORigid
