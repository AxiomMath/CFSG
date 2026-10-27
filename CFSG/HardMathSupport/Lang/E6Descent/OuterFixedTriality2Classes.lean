module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_dvd_ordG2_of_isoPGUThree {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X]
    (h : IsoPGUThree X (2 ^ n)) : Nat.card X ∣ CFSG.Open.ordG2 (2 ^ n) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Sec4.PiField false 2 n K := ⟨Nat.prime_two, hn, by rw [hK]; rfl⟩
  rw [Nat.card_congr e.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hK',
    Sec13.card_slPi_three hK']
  have hQ : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  generalize (2 : ℕ) ^ n = Q at hQ ⊢
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ
  refine ⟨Q ^ 3 * (Q ^ 3 - 1), ?_⟩
  unfold CFSG.Open.ordG2
  simp only [Bool.cond_false]
  zify [h3, h6, Nat.one_le_pow 2 Q hQ]
  ring

section


theorem card_fixedSubgroup_sigma0 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ σ)) = CFSG.Open.ordG2 (2 ^ n) := by
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨e⟩ := nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hK2
  have h1 : Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ σ)) =
      Nat.card ((fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [h1, Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
    card_fixSubfield_of_cube hn hK hσ]

end

theorem fixedSubgroup_inv {X : Type*} [Group X] (α : MulAut X) :
    fixedSubgroup α⁻¹ = fixedSubgroup α := by
  ext x
  change α⁻¹ x = x ↔ α x = x
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]

theorem autFix_eq_fixedSubgroup {X : Type*} [Group X] (α : MulAut X) :
    Sec4.autFix α = fixedSubgroup α := Subgroup.ext fun _ => Iff.rfl

theorem inv_conj_mul_inv {X : Type*} [Group X] (ρ : MulAut X) (g : X) :
    (MulAut.conj g * ρ⁻¹)⁻¹ = MulAut.conj (ρ g⁻¹) * ρ := by
  rw [mul_inv_rev, inv_inv]
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.mul_apply, map_mul, map_inv]

section Lang


theorem exists_card_eq_class_of_conj_sigma0 {n : ℕ} {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg3 : (MulAut.conj g * fieldActor σ σ) ^ 3 = 1) :
    ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (y = 1 ∨ y = d4TrialityY0Elt K σ) ∧
        Nat.card (fixedSubgroup (MulAut.conj g * fieldActor σ σ)) =
          Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) := by
  obtain ⟨h, y, hy, hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds d4SecondCentIrred_holds hK hσ g hg3
  refine ⟨y, ?_, ?_⟩
  · rcases hy with h1 | h0
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h0)
  · rw [hyy, card_fixedSubgroup_conj]

theorem exists_card_fixedSubgroup_eq_class {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (y = 1 ∨ y = d4TrialityY0Elt K σ) ∧
        Nat.card (fixedSubgroup α) =
          Nat.card (fixedSubgroup (MulAut.conj y * fieldActor σ σ)) := by
  obtain ⟨g, hg | hg⟩ := Item8ModelProof.exists_conj_mul_sigma hn hK hσ hα3 hαin
  · subst hg
    exact exists_card_eq_class_of_conj_sigma0 hK hσ g hα3
  · have hinv : α⁻¹ = MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ := by
      rw [hg, inv_conj_mul_inv]
    have h3 : (MulAut.conj (fieldActor σ σ g⁻¹) * fieldActor σ σ) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    obtain ⟨y, hy, hcard⟩ := exists_card_eq_class_of_conj_sigma0 hK hσ _ h3
    refine ⟨y, hy, ?_⟩
    rw [← hcard, ← hinv, fixedSubgroup_inv]

end Lang

end CFSG.HardMathSupport.Lang.E6Descent
