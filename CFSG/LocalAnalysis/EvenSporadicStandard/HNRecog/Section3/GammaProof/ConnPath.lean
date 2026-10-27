module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Common

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_reach_of_common (H : GammaHyps a z) {x y b : G} (hx : IsConj a x)
    (hy : IsConj a y) (hb : b ∈ orb2A a x ∩ orb2A a y) :
    (Gamma a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  have h1 : (Gamma a).Adj ⟨x, hx⟩ ⟨b, hb.1.1⟩ := by
    refine ⟨?_, hb.1.2⟩
    rintro he
    exact H.ne_of_orb2A hx hb.1 (Subtype.ext_iff.mp he).symm
  have h2 : (Gamma a).Adj ⟨b, hb.1.1⟩ ⟨y, hy⟩ := by
    refine ⟨?_, ?_⟩
    · rintro he
      exact H.ne_of_orb2A hy hb.2 (Subtype.ext_iff.mp he)
    · rw [← H.comm_of_orb2A hy hb.2]
      exact hb.2.2
  exact (SimpleGraph.Adj.reachable h1).trans (SimpleGraph.Adj.reachable h2)

theorem gamma_reach_of_even (H : GammaHyps a z) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (he : Even (orderOf (x * y))) : (Gamma a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨b, hb⟩ := gamma_common H hx hy he
  exact gamma_reach_of_common H hx hy hb

private theorem gamma_eq_of_comm_odd {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hcomm : x * y = y * x) (hodd : Odd (orderOf (x * y))) : y = x := by
  have hs2 : (x * y) ^ 2 = 1 := by
    rw [pow_two]
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcomm]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, mul_one]
  have hone : x * y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hs2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      rw [h] at hk
      omega
  calc y = 1 * y := (one_mul y).symm
    _ = (x * x) * y := by rw [hx]
    _ = x * (x * y) := by group
    _ = x * 1 := by rw [hone]
    _ = x := mul_one x

private theorem gamma_reach_of_oddSet (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : IsConj a y) (h : y ∈ oddSet a x) :
    (Gamma a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨-, hyx, hodd, ht⟩ := h
  obtain ⟨t, htA, htxy⟩ := ht
  obtain ⟨htGx, htGy⟩ := mem_Gxy.mp htxy
  have hxt : x * t = t * x := mem_Gx.mp htGx
  have hyt : y * t = t * y := mem_Gx.mp htGy
  have hx2 : x * x = 1 := H.mul_self_a hx
  have hy2 : y * y = 1 := H.mul_self_a hy
  have ht2 : t * t = 1 := H.mul_self_a htA
  have htx_ne : t ≠ x := by
    intro htx
    have hcomm : x * y = y * x := by
      have : x ∈ Gx y := by rw [← htx]; exact htGy
      exact (mem_Gx.mp this).symm
    exact hyx (gamma_eq_of_comm_odd hx2 hy2 hcomm hodd)
  have hty_ne : t ≠ y := by
    intro hty
    have hcomm : x * y = y * x := by
      have : y ∈ Gx x := by rw [← hty]; exact htGx
      exact mem_Gx.mp this
    exact hyx (gamma_eq_of_comm_odd hx2 hy2 hcomm hodd)
  have hxt2 : orderOf (x * t) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two]
      calc (x * t) * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [← hxt]
        _ = (x * x) * (t * t) := by group
        _ = 1 := by rw [hx2, ht2, mul_one]
    · intro h1
      exact htx_ne (by
        calc t = 1 * t := (one_mul t).symm
          _ = (x * x) * t := by rw [hx2]
          _ = x * (x * t) := by group
          _ = x * 1 := by rw [h1]
          _ = x := mul_one x)
  have hty2 : orderOf (t * y) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two]
      calc (t * y) * (t * y) = t * (y * t) * y := by group
        _ = t * (t * y) * y := by rw [hyt]
        _ = (t * t) * (y * y) := by group
        _ = 1 := by rw [ht2, hy2, mul_one]
    · intro h1
      exact hty_ne (by
        calc t = t * 1 := (mul_one t).symm
          _ = t * (y * y) := by rw [hy2]
          _ = (t * y) * y := by group
          _ = 1 * y := by rw [h1]
          _ = y := one_mul y)
  exact (gamma_reach_of_even H hx htA (by rw [hxt2]; decide)).trans
    (gamma_reach_of_even H htA hy (by rw [hty2]; decide))

theorem gamma_reach_of_mem (H : GammaHyps a z) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (hxy : y ∈ gammaSet a z x) : (Gamma a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  rcases gamma_mem_gammaSet_iff.1 hxy with rfl | h | h | h | h | h | h | h | h
  · exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ⟨?_, h.2⟩
    rintro he
    exact H.ne_of_orb2A hx h (Subtype.ext_iff.mp he).symm
  · exact gamma_reach_of_even H hx hy (by rw [H.orderOf_z h.2]; decide)
  · obtain ⟨b, hb⟩ := h.2.2
    exact gamma_reach_of_common H hx hy hb
  · have hF5x : IsF5Type x z := isF5Type_of_isConj H.h hx (IsConj.refl z)
    have h' : y ∈ orb4A x z x := by rwa [gamma_orb4A_eq hx z x]
    have hord : orderOf (x * y) = 4 := tableV_orderOf_orb4A hF5x h'
    exact gamma_reach_of_even H hx hy (by rw [hord]; decide)
  · have hF5x : IsF5Type x z := isF5Type_of_isConj H.h hx (IsConj.refl z)
    have h' : y ∈ orb4B x x := by rwa [gamma_orb4B_eq hx x]
    have hord : orderOf (x * y) = 4 := tableV_orderOf_orb4B hF5x h'
    exact gamma_reach_of_even H hx hy (by rw [hord]; decide)
  · exact gamma_reach_of_oddSet H hx hy h.1
  · exact gamma_reach_of_oddSet H hx hy h.1
  · exact gamma_reach_of_even H hx hy (by rw [h.2.1]; decide)

theorem gamma_reach_of_inv (H : GammaHyps a z) {x y : G} (hx : IsConj a x) (hy : IsConj a y)
    (hs : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxy x y) : (Gamma a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  gamma_reach_of_mem H hx hy ((H.hOdd.self).gamma_of_inv x y hx hy hs)

end CFSG.EvenSporadicStandard.HNRecog.Section3
