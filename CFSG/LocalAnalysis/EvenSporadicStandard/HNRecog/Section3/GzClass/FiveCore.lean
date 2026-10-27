module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.DihedralInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.TwoPowerMul
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvGa

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj_five {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

theorem exists_two_pow_orderOf_mul_of_no_two_A {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) {x y : G} (hx2 : x ^ 2 = 1) (hxz : x * z = z * x)
    (hxA : ¬ IsConj a x) (hyA : IsConj a y) (hyz : y * z = z * y)
    (H0 : ∀ y' : G, IsConj a y' → ¬ (y' * z = z * y' ∧ y' * x = x * y')) :
    ∃ k : ℕ, orderOf (x * y) = 2 ^ k := by
  have hy2 : y ^ 2 = 1 := by
    have h2 : orderOf y = 2 := (orderOf_eq_of_isConj_five hyA).symm.trans h.orderOf_a
    rw [← h2]
    exact pow_orderOf_eq_one y
  have heven : Even (orderOf (x * y)) := by
    rw [← Nat.not_odd_iff_even]
    intro hodd
    exact hxA (hyA.trans (isConj_of_odd_orderOf_mul hx2 hy2 hodd).symm)
  obtain ⟨z₀, ⟨k, hz0pow⟩, hz02, hz01, hz0x, hz0y, hconj_or⟩ :=
    exists_central_involution_of_even_orderOf_mul hx2 hy2 heven
  have hxy_z : Commute (x * y) z := by
    rw [commute_iff_eq]
    calc (x * y) * z = x * (y * z) := mul_assoc x y z
      _ = x * (z * y) := by rw [hyz]
      _ = (x * z) * y := (mul_assoc x z y).symm
      _ = (z * x) * y := by rw [hxz]
      _ = z * (x * y) := mul_assoc z x y
  have hz0z : z₀ * z = z * z₀ := by
    rw [hz0pow]
    exact (hxy_z.pow_left k).eq
  have hz0B : IsConj z z₀ := by
    rcases isConj_of_commute hF1 hF2 hyA hz0y hz02 hz01 with hA | hB
    · exact absurd ⟨hz0z, hz0x⟩ (H0 z₀ hA)
    · exact hB
  have hy_z0y : IsConj y (z₀ * y) := by
    rcases hconj_or with hconj | hconj
    · exact hconj
    · exfalso
      refine H0 (z₀ * x) (hyA.trans hconj) ⟨?_, ?_⟩
      · calc (z₀ * x) * z = z₀ * (x * z) := mul_assoc z₀ x z
          _ = z₀ * (z * x) := by rw [hxz]
          _ = (z₀ * z) * x := (mul_assoc z₀ z x).symm
          _ = (z * z₀) * x := by rw [hz0z]
          _ = z * (z₀ * x) := mul_assoc z z₀ x
      · have h1 : (z₀ * x) * x = z₀ := by
          rw [mul_assoc, ← pow_two, hx2, mul_one]
        have h2 : x * (z₀ * x) = z₀ := by
          rw [← mul_assoc, ← hz0x, mul_assoc, ← pow_two, hx2, mul_one]
        rw [h1, h2]
  have hy_yz0 : IsConj y (y * z₀) := by
    rwa [← hz0y]
  have hyQ : y ∈ Qz z₀ :=
    ((hF3 y z₀ hyA hz0B).shape_2AB z₀ ⟨IsConj.refl z₀, hy_yz0⟩).2
  have hQ2 : IsPGroup 2 ↥(Qz z₀) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx z₀))).map (Gx z₀).subtype
  have hQn : ∀ c ∈ Gx z₀, ∀ q ∈ Qz z₀, c * q * c⁻¹ ∈ Qz z₀ := by
    intro c hc q hq
    have hfix : c * z₀ * c⁻¹ = z₀ := by
      rw [← mem_Gx.mp hc]
      group
    have hmem := Qz_conj_mem (x := z₀) c hq
    rwa [hfix] at hmem
  exact exists_two_pow_orderOf_mul_of_mem hQ2 hQn (mem_Gx.mpr hz0x) hx2 hyQ

end CFSG.EvenSporadicStandard.HNRecog.Section3
