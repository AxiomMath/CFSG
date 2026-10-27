module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralArith
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.GH74.Orders.LieType
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.HardMathSupport.Dickson.I271.FiveCentralLeaf

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.Models TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem card_of_statedClassicalModel_psu' {X : Type} [Group X] {n p f : ℕ} (hn : 3 ≤ n)
    (hc : StatedClassicalModel X .PSU n p f) :
    Nat.card X = ordTwistedA (n - 1) (p ^ f) := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (by omega) hc]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [ordTwistedA, Nat.add_sub_cancel]
  rw [mul_comm (m + 1) m]

theorem five_dvd_generic {K X : Type} [Group K] [Finite K] [Group X]
    (hGA : GriessAllModelsStatement) (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f) (h5 : 5 ∣ Nat.card (Subgroup.center K)) :
    5 ∣ (genericOrders t n p f).1 := by
  have htab := (h5.trans (center_dvd_table hGA hq e hm))
  obtain ⟨hb1, hb2⟩ := genericOrders_snd_le t n p f
  obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := exceptionalOrders_le t n p f
  have hnd : ∀ x : ℕ, 0 < x → x ≤ 4 → ¬ 5 ∣ x := fun x h0 h4 hx => by
    have := Nat.le_of_dvd h0 hx
    omega
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 htab with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · exact h
    · exact absurd h (hnd _ hb1 (by omega))
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h with h | h
    · exact absurd h (hnd _ hc1 hc2)
    · exact absurd h (hnd _ hd1 hd2)

theorem five_central_leaf (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K)
    (h5 : 5 ∣ Nat.card (Subgroup.center K)) (hM : Nat.card K ∣ monsterOrder) :
    13 * 41 ∣ Nat.card K := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq⟩
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hdvd : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card K :=
    Subgroup.card_quotient_dvd_card _
  rcases centralQuotient_family hq hK with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    have hn := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.five_le_of_centerQuotient hq.1 e
    have h3 := (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.center_facts hn e Nat.prime_five
      (by norm_num)).2 h5
    exact absurd h3.1 (by norm_num)
  · obtain ⟨t, n, p, f, hm⟩ := exists_lieModel d
    have h5g := five_dvd_generic hGA hq' e hm h5
    have hcard : Nat.card (K ⧸ Subgroup.center K) = Nat.card (CFSGIndex.lie d).Group :=
      Nat.card_congr e.toEquiv
    have hOrd : Nat.card (CFSGIndex.lie d).Group ∣ monsterOrder := hcard ▸ hdvd.trans hM
    obtain ⟨hp, hf, hadm⟩ := hm.1
    by_cases hPSL : t = .PSL
    · subst hPSL
      exfalso
      obtain ⟨hn2, -⟩ := hadm
      have h5ng : 5 ∣ Nat.gcd n (p ^ f - 1) := h5g
      have h5n : 5 ∣ n := (Nat.dvd_gcd_iff.1 h5ng).1
      have h5q : 5 ∣ p ^ f - 1 := (Nat.dvd_gcd_iff.1 h5ng).2
      have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSL n p f :=
        hm.2.resolve_right fun h => absurd h.1 (by omega)
      have hbm : CFSG.Blueprint.LieModel (CFSGIndex.lie d).Group .PSL n p f :=
        Or.inl ⟨by decide, hc⟩
      have hord := CFSG.GH74.card_of_lieModel_PSL (by omega) hbm
      refine CFSG.HardMathSupport.Dickson.I271.FiveCentralArith.ordA_five_false hp hf
        (m := n - 1) (by omega) (by omega) h5q ?_
      rwa [hord] at hOrd
    by_cases hPSU : t = .PSU
    · subst hPSU
      obtain ⟨hn3, -⟩ := hadm
      have h5ng : 5 ∣ Nat.gcd n (p ^ f + 1) := h5g
      have h5n : 5 ∣ n := (Nat.dvd_gcd_iff.1 h5ng).1
      have h5q : 5 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.1 h5ng).2
      have hc : StatedClassicalModel (CFSGIndex.lie d).Group .PSU n p f :=
        hm.2.resolve_right fun h => absurd h.1 (by omega)
      have hord := card_of_statedClassicalModel_psu' hn3 hc
      obtain ⟨hp2, hf2, hm4⟩ := CFSG.HardMathSupport.Dickson.I271.FiveCentralArith.ordTwistedA_five
        hp hf (m := n - 1) (by omega) (by omega) h5q (by rwa [hord] at hOrd)
      have hn5 : n = 5 := by omega
      subst hp2 hf2 hn5
      have h2 : Nat.card (K ⧸ Subgroup.center K) = ordTwistedA 4 (2 ^ 2) := hcard.trans hord
      have h3 := hdvd
      rw [h2] at h3
      exact dvd_trans
        CFSG.HardMathSupport.Dickson.I271.FiveCentralArith.thirteen_mul_fortyOne_dvd_ordTwistedA h3
    · exfalso
      have h4 := genericOrders_fst_le_four hPSL hPSU n p f
      have h0 := genericOrders_fst_pos hm.1
      have := Nat.le_of_dvd h0 h5g
      omega
  · exfalso
    have hd := card_center_dvd_twelve hSpM hq s e
    exact absurd (h5.trans hd) (by norm_num)

end CFSG.HardMathSupport.Dickson.I271.FiveCentralLeaf
