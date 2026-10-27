module

public import CFSG.LieType.Chevalley.G2LargeEvenCover
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCover
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCover
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TrialityFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6EvenCover
public import CFSG.LieType.Ree.LargeReeEightCentralTwoCover
public import CFSG.LieType.Multipliers.Tits
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem odd_card_center_of_two_cover_trivial {Q : Type} [Group Q] [Finite Q]
    (hQ : commutator Q = ⊤)
    (hcov : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* Q ⧸ center Q),
      Function.Surjective η → η.ker ≤ center E → IsPGroup 2 η.ker → η.ker = ⊥) :
    Odd (Nat.card (center Q)) := by
  set n := Nat.card Q with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set k := n.factorization 2 with hk
  set o := n / 2 ^ k with ho
  have hno : 2 ^ k * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hoodd : ¬ 2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two hn0
  let O : Subgroup Q :=
    { carrier := {z | z ∈ center Q ∧ z ^ o = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have hab : Commute a b := mem_center_iff.1 hb.1 a
        rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hOZ : O ≤ center Q := fun z hz => hz.1
  have : O.Normal := normal_of_le_center hOZ
  let η : Q ⧸ O →* Q ⧸ center Q := QuotientGroup.map O (center Q) (MonoidHom.id Q) hOZ
  have hη : Function.Surjective η := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(q : Q ⧸ O), rfl⟩
  have hker : ∀ q : Q, (q : Q ⧸ O) ∈ η.ker ↔ q ∈ center Q := by
    intro q
    rw [MonoidHom.mem_ker]
    change ((q : Q) : Q ⧸ center Q) = 1 ↔ _
    exact QuotientGroup.eq_one_iff q
  have hC : η.ker ≤ center (Q ⧸ O) := by
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq := (hker q).1 hx
    rw [mem_center_iff]
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hq r]
  have h2 : IsPGroup 2 η.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq := (hker q).1 hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨pow_mem hq _, ?_⟩
    rw [← pow_mul, hno, hn, pow_card_eq_one']
  have : Group.IsPerfect Q := (Group.isPerfect_def).2 hQ
  have : Group.IsPerfect (Q ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hbot := hcov (Q ⧸ O) η hη hC h2
  have hZO : ∀ z ∈ center Q, z ^ o = 1 := by
    intro z hz
    have h1 : (z : Q ⧸ O) ∈ η.ker := (hker z).2 hz
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at h1
    exact h1.2
  by_contra hne
  have h2d : 2 ∣ Nat.card (center Q) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2 h2d
  have hzo : (z : Q) ^ o = 1 := hZO z z.2
  have h3 : orderOf (z : Q) ∣ o := orderOf_dvd_of_pow_eq_one hzo
  rw [Subgroup.orderOf_coe, hz] at h3
  exact hoodd h3

theorem card_center_dvd_card_hopfMultiplier {S Q : Type} [Group S] [Group Q] [Group.IsPerfect Q]
    (e : Q ⧸ center Q ≃* S) :
    Nat.card (center Q) ∣ Nat.card (RankThree.PerfectCover.hopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [← hker, ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

theorem odd_card_center_of_exc_type
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    (hT : RankTwoExceptionalEvenType (A ⧸ center A))
    (hG2 : ¬ ChevalleyExceptionalModel (A ⧸ center A) .G2 2 2)
    (hF4 : ¬ ChevalleyExceptionalModel (A ⧸ center A) .F4 2 1)
    (hE6 : ¬ ChevalleyExceptionalModel (A ⧸ center A) .twistedE6 2 1) :
    Odd (Nat.card (center A)) := by
  have hlie : ∀ {t : StatedLieTag} {m : ℕ}, t ∈ chevalleyExceptionalTags →
      ChevalleyExceptionalModel (A ⧸ center A) t 2 m → LieModel (A ⧸ center A) t 0 2 m :=
    fun ht h => Or.inr (Or.inl ⟨rfl, ht, h⟩)
  rcases hT with ⟨m, hm, hG⟩ | ⟨t, ht, m, hm, hD⟩ | ⟨m, hm, hR⟩ | hT
  ·
    have hm3 : 3 ≤ m := by
      by_contra h
      obtain rfl : m = 2 := by omega
      exact hG2 hG
    refine odd_card_center_of_two_cover_trivial hA fun E _ _ _ η hη hC h2 => ?_
    exact (LieType.Chevalley.G2_large_even_field_central_two_cover_trivial η hη hC h2 hm3
      (hlie (by decide) hG)).1
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    refine odd_card_center_of_two_cover_trivial hA fun E _ _ _ η hη hC h2 => ?_
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      rcases Nat.lt_or_ge m 2 with h1 | h2'
      · obtain rfl : m = 1 := by omega
        exact (LieType.Chevalley.triality_field_two_central_two_cover_trivial η hη hC h2
          (hlie (by decide) hD)).1
      · exact (LieType.Chevalley.triality_nonprime_even_field_central_two_cover_trivial η hη hC
          h2 h2' (hlie (by decide) hD)).1
    ·
      rcases Nat.lt_or_ge m 3 with h1 | h3
      · have hm2 : m = 2 := by
          by_contra h
          obtain rfl : m = 1 := by omega
          exact hF4 hD
        subst hm2
        exact (LieType.Chevalley.ordinary_exceptional_field_four_central_two_cover_trivial η hη
          hC h2 (Or.inl rfl) (hlie (by decide) hD)).1
      · exact (LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
          η hη hC h2 h3 (Or.inl rfl) (hlie (by decide) hD)).1
    ·
      rcases Nat.lt_or_ge m 3 with h1 | h3
      · rcases Nat.lt_or_ge m 2 with h1' | h2'
        · obtain rfl : m = 1 := by omega
          exact (LieType.Chevalley.simply_laced_exceptional_field_two_central_two_cover_trivial
            η hη hC h2 (Or.inl rfl) (hlie (by decide) hD)).1
        · obtain rfl : m = 2 := by omega
          exact (LieType.Chevalley.ordinary_exceptional_field_four_central_two_cover_trivial η hη
            hC h2 (Or.inr (Or.inl rfl)) (hlie (by decide) hD)).1
      · exact (LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
          η hη hC h2 h3 (Or.inr (Or.inl rfl)) (hlie (by decide) hD)).1
    ·
      have hm2 : 2 ≤ m := by
        by_contra h
        obtain rfl : m = 1 := by omega
        exact hE6 hD
      exact (LieType.Chevalley.twisted_E6_nonprime_even_field_central_two_cover_trivial η hη hC
        h2 hm2 (hlie (by decide) hD)).1
    ·
      rcases Nat.lt_or_ge m 3 with h1 | h3
      · rcases Nat.lt_or_ge m 2 with h1' | h2'
        · obtain rfl : m = 1 := by omega
          exact (LieType.Chevalley.simply_laced_exceptional_field_two_central_two_cover_trivial
            η hη hC h2 (Or.inr (Or.inl rfl)) (hlie (by decide) hD)).1
        · obtain rfl : m = 2 := by omega
          exact (LieType.Chevalley.ordinary_exceptional_field_four_central_two_cover_trivial η hη
            hC h2 (Or.inr (Or.inr (Or.inl rfl))) (hlie (by decide) hD)).1
      · exact (LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
          η hη hC h2 h3 (Or.inr (Or.inr (Or.inl rfl))) (hlie (by decide) hD)).1
    ·
      rcases Nat.lt_or_ge m 3 with h1 | h3
      · rcases Nat.lt_or_ge m 2 with h1' | h2'
        · obtain rfl : m = 1 := by omega
          exact (LieType.Chevalley.simply_laced_exceptional_field_two_central_two_cover_trivial
            η hη hC h2 (Or.inr (Or.inr rfl)) (hlie (by decide) hD)).1
        · obtain rfl : m = 2 := by omega
          exact (LieType.Chevalley.ordinary_exceptional_field_four_central_two_cover_trivial η hη
            hC h2 (Or.inr (Or.inr (Or.inr rfl))) (hlie (by decide) hD)).1
      · exact (LieType.Chevalley.ordinary_exceptional_large_even_field_central_two_cover_trivial
          η hη hC h2 h3 (Or.inr (Or.inr (Or.inr rfl))) (hlie (by decide) hD)).1
  ·
    have hlieR : LieModel (A ⧸ center A) .twistedF4 0 2 (2 * m + 1) :=
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
    refine odd_card_center_of_two_cover_trivial hA fun E _ _ _ η hη hC h2 => ?_
    rcases Nat.lt_or_ge m 2 with h1 | h2'
    · obtain rfl : m = 1 := by omega
      exact (LieType.Ree.large_Ree_field_eight_central_two_cover_trivial η hη hC h2 hlieR).1
    · exact (LieType.Ree.large_Ree_large_even_field_central_two_cover_trivial η hη hC h2
        (by omega) hlieR).1
  ·
    have hlieT : LieModel (A ⧸ center A) .Tits 0 2 1 :=
      Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hT⟩))
    obtain ⟨-, ⟨eM⟩⟩ := LieType.Multipliers.Tits.multiplier_Tits _ hlieT
    have : Group.IsPerfect A := (Group.isPerfect_def).2 hA
    have h1 : Nat.card (RankThree.PerfectCover.hopfMultiplier (A ⧸ center A)) = 1 := by
      rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_unique]
    have h2 := card_center_dvd_card_hopfMultiplier (MulEquiv.refl (A ⧸ center A))
    rw [h1, Nat.dvd_one] at h2
    rw [h2]
    exact odd_one

end CFSG.ComponentClassification.RankTwoExceptional
