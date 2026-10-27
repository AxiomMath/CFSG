module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Hyps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Elem

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem gamma_isConj_iff {a x : G} (hx : IsConj a x) (b : G) : IsConj x b ↔ IsConj a b :=
  ⟨fun h => hx.trans h, fun h => hx.symm.trans h⟩

theorem gamma_orb2A_eq {a x : G} (hx : IsConj a x) (y : G) : orb2A x y = orb2A a y := by
  ext b
  simp only [orb2A, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_orb2B_eq {a x : G} (hx : IsConj a x) (z y : G) : orb2B x z y = orb2B a z y := by
  ext b
  simp only [orb2B, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_orb3A_eq {a x : G} (hx : IsConj a x) (y : G) : orb3A x y = orb3A a y := by
  ext c
  simp only [orb3A, Set.mem_setOf_eq, gamma_isConj_iff hx, gamma_orb2A_eq hx]

theorem gamma_orb4A_eq {a x : G} (hx : IsConj a x) (z y : G) : orb4A x z y = orb4A a z y := by
  ext c
  simp only [orb4A, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_orb4B_eq {a x : G} (hx : IsConj a x) (y : G) : orb4B x y = orb4B a y := by
  ext c
  simp only [orb4B, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_orb6A_eq {a x : G} (hx : IsConj a x) (y : G) : orb6A x y = orb6A a y := by
  ext c
  simp only [orb6A, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_oddSet_eq {a x : G} (hx : IsConj a x) (y : G) : oddSet x y = oddSet a y := by
  ext c
  simp only [oddSet, Set.mem_setOf_eq, gamma_isConj_iff hx]

theorem gamma_orb5A_eq {a x : G} (hx : IsConj a x) (y : G) : orb5A x y = orb5A a y := by
  ext c
  simp only [orb5A, Set.mem_setOf_eq, gamma_isConj_iff hx, gamma_oddSet_eq hx]

theorem gamma_orb5E_eq {a x : G} (hx : IsConj a x) (y : G) : orb5E x y = orb5E a y := by
  ext c
  simp only [orb5E, Set.mem_setOf_eq, gamma_isConj_iff hx, gamma_oddSet_eq hx]

theorem gamma_gammaSet_eq {a x : G} (hx : IsConj a x) (z y : G) :
    gammaSet x z y = gammaSet a z y := by
  simp only [gammaSet, gamma_orb2A_eq hx, gamma_orb2B_eq hx, gamma_orb3A_eq hx,
    gamma_orb4A_eq hx, gamma_orb4B_eq hx, gamma_orb5A_eq hx, gamma_orb5E_eq hx,
    gamma_orb6A_eq hx]

theorem gamma_mem_gammaSet_iff {a z x y : G} :
    y ∈ gammaSet a z x ↔ y = x ∨ y ∈ orb2A a x ∨ y ∈ orb2B a z x ∨ y ∈ orb3A a x ∨
      y ∈ orb4A a z x ∨ y ∈ orb4B a x ∨ y ∈ orb5A a x ∨ y ∈ orb5E a x ∨ y ∈ orb6A a x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]

theorem GammaHyps.at {a z x : G} (H : GammaHyps a z) (hx : IsConj a x) : GammaHyps x z :=
  H.of_isConj hx (IsConj.refl z)

variable {a z : G}

theorem GammaHyps.orderOf_a (H : GammaHyps a z) {x : G} (hx : IsConj a x) : orderOf x = 2 :=
  perp_orderOf_of_isConj_a H.h hx

theorem GammaHyps.orderOf_z (H : GammaHyps a z) {x : G} (hx : IsConj z x) : orderOf x = 2 :=
  perp_orderOf_of_isConj_z H.h hx

theorem GammaHyps.sq_a (H : GammaHyps a z) {x : G} (hx : IsConj a x) : x ^ 2 = 1 := by
  rw [← H.orderOf_a hx]
  exact pow_orderOf_eq_one x

theorem GammaHyps.sq_z (H : GammaHyps a z) {x : G} (hx : IsConj z x) : x ^ 2 = 1 := by
  rw [← H.orderOf_z hx]
  exact pow_orderOf_eq_one x

theorem GammaHyps.mul_self_a (H : GammaHyps a z) {x : G} (hx : IsConj a x) : x * x = 1 := by
  rw [← pow_two]
  exact H.sq_a hx

theorem GammaHyps.inv_a (H : GammaHyps a z) {x : G} (hx : IsConj a x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (H.mul_self_a hx)

theorem GammaHyps.ne_one_a (H : GammaHyps a z) {x : G} (hx : IsConj a x) : x ≠ 1 := by
  intro h1
  have h2 := H.orderOf_a hx
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem GammaHyps.ne_one_z (H : GammaHyps a z) {x : G} (hx : IsConj z x) : x ≠ 1 := by
  intro h1
  have h2 := H.orderOf_z hx
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem GammaHyps.not_isConj_both (H : GammaHyps a z) {x : G} (hx : IsConj a x)
    (hz : IsConj z x) : False :=
  sixA_not_isConj H.hT5.self (hx.trans hz.symm)

theorem GammaHyps.comm_of_orb2A (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb2A a x) : x * y = y * x :=
  comm_of_sq_mul (H.sq_a hx) (H.sq_a hy.1) (H.sq_a hy.2)

theorem GammaHyps.comm_of_orb2B (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb2B a z x) : x * y = y * x :=
  comm_of_sq_mul (H.sq_a hx) (H.sq_a hy.1) (H.sq_z hy.2)

theorem GammaHyps.orb2A_symm (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb2A a x) : x ∈ orb2A a y := by
  refine ⟨hx, ?_⟩
  rw [← H.comm_of_orb2A hx hy]
  exact hy.2

theorem GammaHyps.ne_of_orb2A (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb2A a x) : y ≠ x := by
  rintro rfl
  have h1 := hy.2
  rw [H.mul_self_a hx] at h1
  exact H.ne_one_a h1 rfl

theorem GammaHyps.self_mem_Gxyz (H : GammaHyps a z) {x y t : G} (hy : IsConj a y)
    (hxy : x * y = y * x) (ht : t ∈ orb2A a y) : y ∈ Gxyz x y t := by
  rw [mem_Gxyz, mem_Gx, mem_Gx, mem_Gx]
  exact ⟨hxy, rfl, (H.comm_of_orb2A hy ht).symm⟩

theorem GammaHyps.mul_mem_orb2A (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb2A a x) : x * y ∈ orb2A a x ∩ orb2A a y := by
  have hxx : x * x = 1 := H.mul_self_a hx
  have hc : x * y = y * x := H.comm_of_orb2A hx hy
  refine ⟨⟨hy.2, ?_⟩, ⟨hy.2, ?_⟩⟩
  · rw [← mul_assoc, hxx, one_mul]
    exact hy.1
  · rw [hc, ← mul_assoc, H.mul_self_a hy.1, one_mul]
    exact hx

theorem GammaHyps.sq_mem_orb2A (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb4B a x) : orderOf (x * y) = 4 ∧ (x * y) ^ 2 ∈ orb2A a x ∩ orb2A a y := by
  have h4 : orderOf (x * y) = 2 * 2 := perp_orderOf_eq_four (H.orderOf_a hy.2)
  obtain ⟨-, -, h1, h2⟩ := tableV_dihedral (H.sq_a hx) (H.sq_a hy.1) (hx.symm.trans hy.1) h4
  exact ⟨h4, ⟨hy.2, hx.trans h1⟩, ⟨hy.2, hx.trans h2⟩⟩

theorem GammaHyps.cube_mem_orb2A (H : GammaHyps a z) {x y : G} (hx : IsConj a x)
    (hy : y ∈ orb6A a x) : (x * y) ^ 3 ∈ orb2A a x ∩ orb2A a y := by
  have h6 : orderOf (x * y) = 2 * 3 := hy.2.1
  obtain ⟨-, -, h1, h2⟩ := tableV_dihedral (H.sq_a hx) (H.sq_a hy.1) (hx.symm.trans hy.1) h6
  exact ⟨⟨hy.2.2, hx.trans h1⟩, ⟨hy.2.2, hx.trans h2⟩⟩

theorem gamma_orb2A_conj (g : G) {x y : G} (hy : y ∈ orb2A a x) :
    g * y * g⁻¹ ∈ orb2A a (g * x * g⁻¹) := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨h1.trans (isConj_iff.mpr ⟨g, rfl⟩), ?_⟩
  have e : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  rw [e]
  exact h2.trans (isConj_iff.mpr ⟨g, rfl⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
