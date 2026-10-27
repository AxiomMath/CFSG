module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglMain

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley LangTwistedProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)



theorem card_fixedSubgroup_eq_card_autFix {C : Type*} [Group C] (α : MulAut C) :
    Nat.card (fixedSubgroup α) = Nat.card (Sec4.autFix α) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_fixedSubgroup_congr_conj {C : Type*} [Group C] (β α α' : MulAut C)
    (h : α = β * α' * β⁻¹) : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup α') := by
  rw [card_fixedSubgroup_eq_card_autFix, card_fixedSubgroup_eq_card_autFix]
  have e := Sec4.autFixCongrEquiv β α'
  rw [mulAut_congr_eq, ← h] at e
  exact Nat.card_congr e.toEquiv

theorem card_fixedSubgroup_second_class_even_of_conj {f : ℕ} (hf : 1 ≤ f) (hfe : Even f)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy : MulAut.conj y * fieldActor σ σ =
      β * (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) * β⁻¹) :
    Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
  rw [card_fixedSubgroup_congr_conj β _ _ hy, card_fixedSubgroup_eq_card_autFix]
  exact card_autFix_y0_even hf hfe σ hK hσ

theorem card_fixedSubgroup_second_class_even_of_conj_dvd {f : ℕ} (hf : 1 ≤ f) (hfe : Even f)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy : MulAut.conj y * fieldActor σ σ =
      β * (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) * β⁻¹) :
    Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) ∣ CFSG.Open.ordG2 (2 ^ f) := by
  rw [card_fixedSubgroup_second_class_even_of_conj hf hfe σ hK hσ β hy]
  exact pgl_three_card_dvd_ordG2 _

theorem conj_class_dichotomy_even
    {f : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hyσ : fieldActor σ σ y = y) (hy3 : y ^ 3 = 1) :
    (∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        MulAut.conj y * fieldActor σ σ = β * fieldActor σ σ * β⁻¹) ∨
      ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        MulAut.conj y * fieldActor σ σ =
          β * (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) * β⁻¹ := by
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  have hσ₀3 : σ₀ ^ 3 = 1 := fieldActor_pow_three hK hσ
  have hg3 : (MulAut.conj y * σ₀) ^ 3 = 1 := by
    rw [conj_mul_pow_three σ₀ hσ₀3, hyσ, hyσ, ← pow_three', hy3, map_one]
  obtain ⟨h, y', hy', hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds d4SecondCentIrred_holds hK hσ y hg3
  rcases hy' with hy1 | hy0
  · left
    have hy'1 : y' = 1 := Subtype.ext hy1
    refine ⟨MulAut.conj h⁻¹, ?_⟩
    rw [hyy, hy'1, map_one, one_mul]
  · right
    have hy'0 : y' = d4TrialityY0Elt K σ := Subtype.ext hy0
    exact ⟨MulAut.conj h⁻¹, by rw [hyy, hy'0]⟩

theorem card_fixedSubgroup_second_class_even
    {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hyσ : fieldActor σ σ y = y)
    (hy3 : y ^ 3 = 1)
    (h₁ : Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ∣ CFSG.Open.ordG2 (2 ^ f)) :
    Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) ∣ CFSG.Open.ordG2 (2 ^ f) := by
  rcases conj_class_dichotomy_even σ hK hσ hyσ hy3 with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · have hβ' : MulAut.conj y * fieldActor σ σ =
        β * (MulAut.conj (1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) *
          fieldActor σ σ) * β⁻¹ := by
      rw [hβ, map_one, one_mul]
    rw [card_fixedSubgroup_congr_conj β _ _ hβ', map_one, one_mul]
    exact h₁
  · exact card_fixedSubgroup_second_class_even_of_conj_dvd hf hfe σ hK hσ β hβ

end CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl
