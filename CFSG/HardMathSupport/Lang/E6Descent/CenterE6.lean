module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeIndex
public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Multiplier
open CFSG.Open (griessHopfMultiplier)
open CFSG.AGLEmbedding.FixedThree (card_mult_zmod)
open TauCeti

theorem card_hopf_dvd_twelve (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel K t n p f)
    (hg : (genericOrders t n p f).1 * (genericOrders t n p f).2 ∣ 3)
    (he : (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 ∣ 4) :
    Nat.card (griessHopfMultiplier K) ∣ 12 := by
  obtain ⟨-, ⟨φ⟩⟩ := hGA K t n p f hm
  rw [Nat.card_congr φ.toEquiv]
  simp only [generic, exceptional, Nat.card_prod, card_mult_zmod]
  exact (mul_dvd_mul hg he)

theorem card_eq_three_of_dvd_twelve {Z : Type} [Group Z] [Finite Z] (hZ : IsPGroup 3 Z)
    (hn : Nontrivial Z) {m : ℕ} (hm : m ∣ 12) (hd : Nat.card Z ∣ m) : Nat.card Z = 3 := by
  obtain ⟨k, hk, hcard⟩ := (hZ.nontrivial_iff_card).1 hn
  have h12 : 3 ^ k ∣ 12 := hcard ▸ hd.trans hm
  have hk1 : k < 2 := by
    by_contra h
    have : 9 ∣ 12 := (pow_dvd_pow 3 (not_lt.1 h) : 3 ^ 2 ∣ 3 ^ k).trans h12
    omega
  have : k = 1 := by omega
  rw [hcard, this]; norm_num

theorem card_center_eq_three_E6
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hZ : IsPGroup 3 (Subgroup.center ↥L)) (hcen : Subgroup.center ↥L ≠ ⊥)
    (hK : (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid),
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) ∧
          3 ∣ q.card - 1) ∨
      (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) ∧
          3 ∣ q.card + 1)) :
    Nat.card (Subgroup.center ↥L) = 3 := by
  have hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  have hnt : Nontrivial ↥(Subgroup.center ↥L) := (Subgroup.nontrivial_iff_ne_bot _).2 hcen
  have key : Nat.card (griessHopfMultiplier (↥L ⧸ Subgroup.center ↥L)) ∣ 12 := by
    rcases hK with ⟨q, hv, ⟨e⟩, -⟩ | ⟨q, hv, ⟨e⟩, -⟩
    · have hm : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .E6 0 q.p q.exponent :=
        CFSG.AGLEmbedding.FixedThree.lieModel_of_names ⟨.E6 q, hv⟩
          ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
      refine card_hopf_dvd_twelve hGA hm ?_ ?_
      · simp [genericOrders]
        exact Nat.gcd_dvd_left _ _
      · simp [exceptionalOrders]
    · have hm : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .twistedE6 0 q.p q.exponent :=
        CFSG.AGLEmbedding.FixedThree.lieModel_of_names ⟨.twistedE6 q, hv⟩
          ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
      refine card_hopf_dvd_twelve hGA hm ?_ ?_
      · simp [genericOrders]
        exact Nat.gcd_dvd_left _ _
      · unfold exceptionalOrders
        split <;> simp_all
  exact card_eq_three_of_dvd_twelve hZ hnt key
    (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl _))

end CFSG.HardMathSupport.Lang.E6Descent
