module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.AOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiveCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzClass_centralizes_two_A (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (x : ↥(Gx z)) (hx : (x : G) ^ 2 = 1)
    (hcard : Nat.card ↥(CbarCent z x) = 120 ∨ Nat.card ↥(CbarCent z x) = 32) :
    (∃ y : G, IsConj a y ∧ y ∈ Gxy z x) ∧ (IsConj a x ∨ IsConj z x) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar (a := a) h
  have hx2' : x ^ 2 = (1 : ↥(Gx z)) := by
    apply Subtype.ext
    simpa using hx
  have hx2bar : (barOf z x) ^ 2 = 1 := by
    simpa [QuotientGroup.mk_pow] using congrArg (barOf z) hx2'
  have hxbar1 : barOf z x ≠ 1 := by
    apply ne_one_of_card_centralizer_ne e
    change Nat.card ↥(CbarCent z x) ≠ 7200
    rcases hcard with hc | hc <;> rw [hc] <;> norm_num
  have hx1sub : x ≠ 1 := by
    intro h1
    apply hxbar1
    rw [h1]
    simp
  have hx1G : (x : G) ≠ 1 := by
    intro h1
    exact hx1sub (Subtype.ext (by simpa using h1))
  have hdisj : barOf z x ∉ _root_.commutator (Gbar z) ∨
      Nat.card ↥(CbarCent z x) = 32 := by
    rcases hcard with hc | hc
    · left
      rcases involution_cases_of_mulEquiv e hx2bar hxbar1 with h1 | h2 | h3
      · exact h1.1
      · exfalso
        have h240 : Nat.card ↥(CbarCent z x) = 240 := h2.2
        omega
      · exfalso
        have h32 : Nat.card ↥(CbarCent z x) = 32 := h3.2
        omega
    · right
      exact hc
  have hexists : ∃ y : G, IsConj a y ∧ y ∈ Gxy z x := by
    by_contra hno
    have H0 : ∀ y' : G, IsConj a y' →
        ¬ (y' * z = z * y' ∧ y' * (x : G) = (x : G) * y') := by
      intro y' hy' hcomm
      apply hno
      refine ⟨y', hy', ?_⟩
      rw [mem_Gxy]
      constructor
      · rw [mem_Gx]
        exact hcomm.1.symm
      · rw [mem_Gx]
        exact hcomm.2.symm
    have hxA : ¬ IsConj a (x : G) := by
      intro hxA
      apply hno
      refine ⟨(x : G), hxA, ?_⟩
      rw [mem_Gxy]
      constructor
      · rw [mem_Gx]
        exact mem_Gx.1 x.2
      · rw [mem_Gx]
    obtain ⟨v, hv2, hv, hvnot⟩ :=
      exists_outer_involution_mul_of_mulEquiv e hx2bar hxbar1 hdisj
    obtain ⟨y, hyA, hybar⟩ := exists_outer_lift hI hC h hF1 hF2 hF3 hOrb hv2 hv
    have hxz : (x : G) * z = z * (x : G) := (mem_Gx.mp x.2).symm
    have hyz : (y : G) * z = z * (y : G) := (mem_Gx.mp y.2).symm
    obtain ⟨k, hk⟩ := exists_two_pow_orderOf_mul_of_no_two_A (x := (x : G)) (y := (y : G))
      h hF1 hF2 hF3 hx hxz hxA hyA hyz H0
    have hk' : orderOf (x * y) = 2 ^ k := by
      rw [← Subgroup.orderOf_coe (x * y)]
      exact hk
    have hdvd : orderOf (barOf z (x * y)) ∣ 2 ^ k := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) (x * y)
      rw [hk'] at h
      simpa only [QuotientGroup.mk'_apply] using h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hxybar : barOf z (x * y) = barOf z x * v := by
      calc barOf z (x * y) = barOf z x * barOf z y :=
            QuotientGroup.mk_mul (CFSG.pCore 2 ↥(Gx z)) x y
        _ = barOf z x * v := by rw [hybar]
    rw [hxybar] at hj
    exact hvnot j hj
  refine ⟨hexists, ?_⟩
  obtain ⟨y, hyA, hyGxy⟩ := hexists
  have hyx : y ∈ Gx (x : G) := (mem_Gxy.1 hyGxy).2
  exact isConj_of_commute hF1 hF2 hyA (mem_Gx.1 hyx) hx hx1G

end CFSG.EvenSporadicStandard.HNRecog.Section3
