module

public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSp4Inner

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique

section Field

variable {K : Type} [Field K]

theorem k32_fixed_of_mem_zpowers {σ : K ≃+* K} {a : K} (ha : σ a = a) {τ : K ≃+* K}
    (hτ : τ ∈ Subgroup.zpowers σ) : τ a = a := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) a := by
    rw [Subgroup.zpowers_le]
    exact MulAction.mem_stabilizer_iff.mpr ha
  exact MulAction.mem_stabilizer_iff.mp (hle hτ)

theorem k32_card_descentField_three [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) : 3 ∣ f ∧ Nat.card (descentField σ) = 2 ^ (f / 3) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [mem_descentField, ← SetLike.mem_coe, hS, Set.mem_ofPred_eq]
  exact ⟨fun ha τ hτ => k32_fixed_of_mem_zpowers ha hτ, fun h => h σ (Subgroup.mem_zpowers σ)⟩

end Field

section Sp4

variable {F : Type} [Field F] [CharP F 2]

theorem k32_center_sp4 : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun p hp => ?_
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
  have h1 : spInner 2 F g = 1 := by
    rw [spInner_eq_conj]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply]
    have hx := Subgroup.mem_center_iff.mp hp x
    rw [← hx, mul_inv_cancel_right]
  have h2 : spInner 2 F g = spInner 2 F 1 := by rw [h1, map_one]
  rw [spInner_injective h2, map_one]

@[expose] noncomputable def k32Sp4Equiv (F : Type) [Field F] [CharP F 2] :
    antiSp F ≃* StatedProj (StatedSp 2 F) :=
  (antiSpEquiv F).trans (projSpEquiv F)

variable [Finite F]

theorem k32_sp4_outer_bound {α : MulAut (StatedProj (StatedSp 2 F))} (hα : α ^ 3 = 1)
    (hD : α ∉ innAut (StatedProj (StatedSp 2 F)))
    {W : Subgroup (StatedProj (StatedSp 2 F))} (hW : IsPGroup 2 ↥W) (hfix : ∀ w ∈ W, α w = w) :
    Nat.card ↥W ≤ Nat.card F ^ 2 := by
  have hD' : α ∉ (SymplecticHigher.conjAut 2 F).range := fun h => by
    obtain ⟨A, rfl⟩ := h
    exact hD (conjAut_mem_inner_of_charTwo A)
  obtain ⟨σ, hσ3, H, hαH⟩ := sp4_even_order_three_field_descent α hα hD'
  set c : MulAut (StatedProj (StatedSp 2 F)) := SymplecticHigher.conjAut 2 F H with hc
  obtain ⟨f, hf1, hf⟩ := exists_card_eq_two_pow (K := F)
  obtain ⟨h3f, hkcard⟩ := k32_card_descentField_three hf1 hf hσ3
  set k : Subfield F := descentField σ with hk
  set ψ : StatedProj (StatedSp 2 F) →* StatedProj (StatedSp 2 F) := (c⁻¹ : MulAut _).toMonoidHom
    with hψ
  have hψinj : Function.Injective ψ := (c⁻¹ : MulAut _).injective
  have hfs : SymplecticHigher.fieldAut 2 F σ = c⁻¹ * α * c := by
    rw [hαH]
    group
  have hW0 : ∀ x ∈ W.map ψ, SymplecticHigher.fieldAut 2 F σ x = x := by
    rintro _ ⟨w, hw, rfl⟩
    have hcw : c (c⁻¹ w) = w := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    change SymplecticHigher.fieldAut 2 F σ (c⁻¹ w) = c⁻¹ w
    rw [hfs, MulAut.mul_apply, MulAut.mul_apply, hcw, hfix w hw]
  have hproj : Function.Injective (proj 2 F) := UnitaryHigher.proj_bijective_of_charTwo.1
  let Φ : StatedSp 2 k →* StatedProj (StatedSp 2 F) := (proj 2 F).comp (subfieldSpHom 2 k)
  have hΦinj : Function.Injective Φ := hproj.comp (subfieldSpHom_injective k)
  have hrange : W.map ψ ≤ Φ.range := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
    have hfx := hW0 _ hx
    rw [fieldAut_proj] at hfx
    obtain ⟨g₀, hg₀⟩ := exists_subfieldSpHom_eq (hproj hfx)
    exact ⟨g₀, congrArg (proj 2 F) hg₀⟩
  set W₁ : Subgroup (StatedSp 2 k) := (W.map ψ).comap Φ with hW₁
  have hmap : W₁.map Φ = W.map ψ := by
    rw [hW₁, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hrange
  have hcard₁ : Nat.card ↥W₁ = Nat.card ↥W := by
    have h1 := Subgroup.card_map_of_injective (K := W₁) hΦinj
    rw [hmap, Subgroup.card_map_of_injective hψinj] at h1
    exact h1.symm
  obtain ⟨m, hm, hmcard⟩ := CFSG.ComponentClassification.SymmetricLocal.card_statedSp_eq_two_pow_mul_odd
    (r := 2) (k := k) hkcard
    (by omega) (by norm_num)
  have hdvd : Nat.card ↥W₁ ∣ 2 ^ (f / 3 * 2 ^ 2) * m := hmcard ▸ Subgroup.card_subgroup_dvd_card W₁
  obtain ⟨j, hj⟩ := hW.exists_card_eq
  rw [← hcard₁] at hj
  rw [hj] at hdvd
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hdvd2 : 2 ^ j ∣ 2 ^ (f / 3 * 2 ^ 2) := hcop.dvd_of_dvd_mul_right hdvd
  have hj' : j ≤ f / 3 * 2 ^ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd2
  rw [← hcard₁, hj, hf]
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem k32InnerBound_sp4 : K32InnerBound (StatedProj (StatedSp 2 F)) (Nat.card F) :=
  k32InnerBound_of_equiv (k32Sp4Equiv F) fun _ hg3 hg1 _ hW hC =>
    k32_sp4_inner_bound hg3 hg1 hW hC

theorem k32OuterBound_sp4 : K32OuterBound (StatedProj (StatedSp 2 F)) (Nat.card F ^ 2) :=
  fun _ hα hD _ hW hfix => k32_sp4_outer_bound hα hD hW hfix

theorem k32ZBound2_sp4 : K32ZBound2 (StatedProj (StatedSp 2 F)) (Nat.card F) (Nat.card F ^ 2) :=
  k32ZBound2_of_inner_outer k32_center_sp4 k32InnerBound_sp4 k32OuterBound_sp4

end Sp4

end CFSG.QuasithinUnique.DoubleA3
