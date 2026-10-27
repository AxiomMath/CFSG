module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false


theorem card_fixSubgroup_fieldActor {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) =
      lieOrderNumerator .G2 0 (ℓ ^ f) :=
  CFSG.HardMathSupport.Lang.Triality.card_fixed_fieldActor_D4_of_frobenius hℓ hf hK σ hσ

theorem three_le_pow_of_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) : 3 ≤ ℓ ^ f := by
  have h3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  calc 3 ≤ ℓ := h3
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

theorem finite_graphFixedRootGroup_D4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  exact Finite.of_injective (fun x => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective

theorem noL2Layer_fieldActor_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) : NoL2Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := finite_graphFixedRootGroup_D4 σ
  have hs := isSimpleGroup_fixSubgroup_fieldActor_D4 ℓ f hℓ hℓ2 K hK σ hσ
  have hnab := nonabelian_fixSubgroup_fieldActor_D4 ℓ f hℓ hℓ2 K hK σ hσ
  refine noL2_of_simple_fixed _ hs hnab fun r hr => ?_
  have hadm : StatedLieAdmissible .G2 0 ℓ f := ⟨hℓ, hf, rfl, three_le_pow_of_odd hℓ hℓ2 hf⟩
  refine not_typeL2_of_order hadm (by decide) (by simp) ?_ (center_eq_bot_of_simple hnab) hr
  rw [card_fixSubgroup_fieldActor hℓ hf hK σ hσ]
  simp [lieOrderDivisor]

theorem simple_fixSubgroup_fieldActor_two {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    IsSimpleGroup (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ∧
      ∃ a b : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ), a * b ≠ b * a := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hcard : Nat.card (fixSubfield σ) = 2 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two (by omega) hK σ hσ
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hcard]
    exact_mod_cast (by omega : 3 ≤ 2 ^ f)
  let e := (fixSubgroupFieldActorEquiv K σ hσ3).trans
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk3)
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := fixSubfield σ)
    (by omega)
  obtain ⟨hs, a, b, hab⟩ := isSimple_of_isQuasisimple_center_bot hq
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  haveI := hs
  refine ⟨e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact this

theorem noL2Layer_fieldActor_two {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    NoL2Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := finite_graphFixedRootGroup_D4 σ
  obtain ⟨hs, hnab⟩ := simple_fixSubgroup_fieldActor_two hf hK σ hσ
  refine noL2_of_simple_fixed _ hs hnab fun r hr => ?_
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .G2 0 2 f := ⟨Nat.prime_two, by omega, rfl, by omega⟩
  refine not_typeL2_of_order hadm (by decide) (by simp) ?_ (center_eq_bot_of_simple hnab) hr
  rw [card_fixSubgroup_fieldActor Nat.prime_two (by omega) hK σ hσ]
  simp [lieOrderDivisor]

theorem noL2Layer_fieldActor_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    NoL2Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := finite_graphFixedRootGroup_D4 σ
  refine noL2Layer_of_card_dvd _ (N := 12096) (by norm_num) ?_ 30 (by norm_num) ?_
  · rw [card_fixSubgroup_fieldActor Nat.prime_two le_rfl hK σ hσ]
    norm_num [lieOrderNumerator]
  · decide +kernel

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
