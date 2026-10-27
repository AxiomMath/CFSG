module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeEvenClassification.Helpers

open scoped MatrixGroups

theorem card_SL3_zmod {p : ℕ} (hp : p.Prime) :
    Nat.card (SL(3, ZMod p)) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod p) (n := 3)
    (by norm_num), Nat.card_zmod]
  norm_num only [show 3 * (3 - 1) / 2 = 3 from rfl]
  rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) from rfl, Finset.prod_pair (by norm_num)]

theorem dvd_p_add_one_of_dvd_card_SL3 {p d : ℕ} (hp : p.Prime) (hd : d.Prime) (hdp : d ≠ p)
    (hdvd : d ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)))
    (h1 : ¬ d ∣ p - 1) (h2 : ¬ d ∣ p ^ 2 + p + 1) : d ∣ p + 1 := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hp1 : 1 ≤ p := hp.one_le
  have hp2 : 1 ≤ p ^ 2 := Nat.succ_le_of_lt (pow_pos hp.pos 2)
  have hp3 : 1 ≤ p ^ 3 := Nat.succ_le_of_lt (pow_pos hp.pos 3)
  have hcast : ((p : ZMod d) ^ 3) * (((p : ZMod d) ^ 2 - 1) * ((p : ZMod d) ^ 3 - 1)) = 0 := by
    have h0 : ((p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) : ℕ) : ZMod d) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp2, Nat.cast_sub hp3, Nat.cast_one]
      using h0
  have hp0 : (p : ZMod d) ≠ 0 := by
    intro h
    exact hdp ((Nat.prime_dvd_prime_iff_eq hd hp).1 ((ZMod.natCast_eq_zero_iff p d).1 h))
  have hp0' : (p : ZMod d) ^ 3 ≠ 0 := pow_ne_zero 3 hp0
  have hfac : ((p : ZMod d) ^ 2 - 1) * ((p : ZMod d) ^ 3 - 1) = 0 := by
    rcases mul_eq_zero.1 hcast with h | h
    · exact absurd h hp0'
    · exact h
  have hconcl : (p : ZMod d) = -1 := by
    rcases mul_eq_zero.1 hfac with hsq | hcube
    · have hsq' : (p : ZMod d) ^ 2 = 1 := sub_eq_zero.1 hsq
      have hprod : ((p : ZMod d) - 1) * ((p : ZMod d) + 1) = 0 := by
        linear_combination hsq'
      rcases mul_eq_zero.1 hprod with hone | hneg
      · exact absurd (by
          have hp_eq : (p : ZMod d) = 1 := sub_eq_zero.1 hone
          have : ((p - 1 : ℕ) : ZMod d) = 0 := by
            rw [Nat.cast_sub hp1, hp_eq, Nat.cast_one, sub_self]
          exact (ZMod.natCast_eq_zero_iff (p - 1) d).1 this) h1
      · rw [eq_neg_iff_add_eq_zero]
        exact hneg
    · have hcube' : (p : ZMod d) ^ 3 = 1 := sub_eq_zero.1 hcube
      have hprod : ((p : ZMod d) - 1) * ((p : ZMod d) ^ 2 + (p : ZMod d) + 1) = 0 := by
        linear_combination hcube'
      rcases mul_eq_zero.1 hprod with hone | hquad
      · exact absurd (by
          have hp_eq : (p : ZMod d) = 1 := sub_eq_zero.1 hone
          have : ((p - 1 : ℕ) : ZMod d) = 0 := by
            rw [Nat.cast_sub hp1, hp_eq, Nat.cast_one, sub_self]
          exact (ZMod.natCast_eq_zero_iff (p - 1) d).1 this) h1
      · exact absurd (by
          have : ((p ^ 2 + p + 1 : ℕ) : ZMod d) = 0 := by
            rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hquad]
          exact (ZMod.natCast_eq_zero_iff _ _).1 this) h2
  have hfin : ((p + 1 : ℕ) : ZMod d) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, hconcl]
    abel
  exact (ZMod.natCast_eq_zero_iff (p + 1) d).1 hfin

theorem dvd_card_SL3_of_isPGroup {p d : ℕ} (hp : p.Prime) (hd : d.Prime) {I : Type} [Group I]
    [Finite I] (hI : IsSLType 3 (ZMod p) I) {D : Subgroup I} (hDne : D ≠ ⊥) (hD : IsPGroup d D) :
    d ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨e⟩ := hI
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hDne ((Subgroup.eq_bot_iff_card D).2 hk)
  have hdD : d ∣ Nat.card D := hk ▸ dvd_pow_self d hk0
  have hdI : d ∣ Nat.card I := by
    refine hdD.trans ?_
    simpa using Subgroup.card_dvd_of_le (H := D) (K := (⊤ : Subgroup I)) le_top
  have hcard : Nat.card I = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv, card_SL3_zmod hp]
  rwa [hcard] at hdI

end CFSG.GroupTheory

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeEvenClassification.Helpers

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

@[expose] def ThreeTenSl3Order (p d : ℕ) : Prop :=
  d ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))

@[expose] def ThreeTenTorusExclusion (p d : ℕ) : Prop :=
  ¬ d ∣ (p - 1) ∧ ¬ d ∣ (p ^ 2 + p + 1)

@[expose] def TwelveThreeYQuotient (G : Type) [Group G] (M H : Subgroup G) (p d : ℕ) : Prop :=
  IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))

theorem threeTenSl3Order_of_isPGroup {p d : ℕ} (hp : p.Prime) (hd : d.Prime)
    {I : Type} [Group I] [Finite I] (hI : IsSLType 3 (ZMod p) I)
    {D : Subgroup I} (hDne : D ≠ ⊥) (hD : IsPGroup d D) : ThreeTenSl3Order p d :=
  CFSG.GroupTheory.dvd_card_SL3_of_isPGroup hp hd hI hDne hD

theorem dvd_p_add_one_of_sl3Data {p d : ℕ} (hp : p.Prime) (hd : d.Prime) (hdp : d ≠ p)
    (hord : ThreeTenSl3Order p d) (htor : ThreeTenTorusExclusion p d) : d ∣ p + 1 :=
  CFSG.GroupTheory.dvd_p_add_one_of_dvd_card_SL3 hp hd hdp hord htor.1 htor.2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
