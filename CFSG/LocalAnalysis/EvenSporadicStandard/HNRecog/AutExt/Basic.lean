module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

structure IsIsoOn {G G' : Type} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    (f : G → G') : Prop where
  map_mul : ∀ x ∈ H, ∀ y ∈ H, f (x * y) = f x * f y
  mem : ∀ x ∈ H, f x ∈ H'
  injOn : ∀ x ∈ H, ∀ y ∈ H, f x = f y → x = y
  surjOn : ∀ y ∈ H', ∃ x ∈ H, f x = y

@[expose] def InvIn {G : Type} [Group G] (K : Subgroup G) : Set G := {t | t ∈ K ∧ orderOf t = 2}

structure F5Base {G : Type} [Group G] (a z : G) : Prop where
  typ : IsF5Type a z
  loc : F5Local G a z
  iface : TwoHSInterface

structure AutExtOpen : Prop where
  x_inner : XInnerFacts
  x_cent : XCentFacts

structure F5Std {G : Type} [Group G] (a z : G) : Prop extends F5Base a z where
  inp : AutExtOpen

theorem F5Base.finite {G : Type} [Group G] {a z : G} (h : F5Base a z) : Finite G :=
  Nat.finite_of_card_ne_zero (by rw [h.loc.order.card_eq]; norm_num)

theorem F5Std.finite {G : Type} [Group G] {a z : G} (h : F5Std a z) : Finite G :=
  h.toF5Base.finite

theorem F5Base.of_isConj {G : Type} [Group G] {a z x w : G} (h : F5Base a z) (hx : IsConj a x)
    (hw : IsConj z w) : F5Base x w :=
  ⟨isF5Type_of_isConj h.typ hx hw, h.loc.of_isConj hx hw, h.iface⟩

theorem F5Std.of_isConj {G : Type} [Group G] {a z x w : G} (h : F5Std a z) (hx : IsConj a x)
    (hw : IsConj z w) : F5Std x w :=
  ⟨h.toF5Base.of_isConj hx hw, h.inp⟩

theorem F5Base.orderOf_eq_two {G : Type} [Group G] {a z : G} (h : F5Base a z) {x : G}
    (hx : IsConj a x ∨ IsConj z x) : orderOf x = 2 := by
  rcases hx with hx | hx
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).trans h.typ.orderOf_a
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) z).trans h.typ.orderOf_z

theorem F5Base.mul_comm {G : Type} [Group G] {a z : G} (h : F5Base a z) {x y : G}
    (hx : IsConj a x ∨ IsConj z x) (hy : IsConj a y ∨ IsConj z y)
    (hxy : IsConj a (x * y) ∨ IsConj z (x * y)) : x * y = y * x := by
  have hx2 : x ^ 2 = 1 := by simpa [h.orderOf_eq_two hx] using pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by simpa [h.orderOf_eq_two hy] using pow_orderOf_eq_one y
  have hxy2 : (x * y) ^ 2 = 1 := by simpa [h.orderOf_eq_two hxy] using pow_orderOf_eq_one (x * y)
  have e1 : x * x = 1 := by rwa [← pow_two]
  have e2 : y * y = 1 := by rwa [← pow_two]
  have e3 : (x * y) * (x * y) = 1 := by rwa [← pow_two]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right e1
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right e2
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right e3
  rw [mul_inv_rev, hxi, hyi] at hxyi
  exact hxyi.symm

theorem F5Std.orderOf_eq_two {G : Type} [Group G] {a z : G} (h : F5Std a z) {x : G}
    (hx : IsConj a x ∨ IsConj z x) : orderOf x = 2 :=
  h.toF5Base.orderOf_eq_two hx

theorem F5Std.mul_comm {G : Type} [Group G] {a z : G} (h : F5Std a z) {x y : G}
    (hx : IsConj a x ∨ IsConj z x) (hy : IsConj a y ∨ IsConj z y)
    (hxy : IsConj a (x * y) ∨ IsConj z (x * y)) : x * y = y * x :=
  h.toF5Base.mul_comm hx hy hxy

theorem F5Std.mem_Gx_of_orb2A {G : Type} [Group G] {a z : G} (h : F5Std a z) {x b : G}
    (hx : IsConj a x) (hb : b ∈ orb2A a x) : b ∈ Gx x :=
  mem_Gx.2 (h.mul_comm (Or.inl hx) (Or.inl hb.1) (Or.inl hb.2))

theorem F5Std.mem_Gx_of_orb2B {G : Type} [Group G] {a z : G} (h : F5Std a z) {x b : G}
    (hx : IsConj a x) (hb : b ∈ orb2B a z x) : b ∈ Gx x :=
  mem_Gx.2 (h.mul_comm (Or.inl hx) (Or.inl hb.1) (Or.inr hb.2))

theorem F5Std.mem_Gx_of_orb2AB {G : Type} [Group G] {a z : G} (h : F5Std a z) {x w : G}
    (hx : IsConj a x) (hw : w ∈ orb2AB a z x) : w ∈ Gx x :=
  mem_Gx.2 (h.mul_comm (Or.inl hx) (Or.inr hw.1) (Or.inl hw.2))

theorem F5Std.mem_Gx_of_orb2BB {G : Type} [Group G] {a z : G} (h : F5Std a z) {x w : G}
    (hx : IsConj a x) (hw : w ∈ orb2BB a z x) : w ∈ Gx x :=
  mem_Gx.2 (h.mul_comm (Or.inl hx) (Or.inr hw.1) (Or.inr hw.2))

end CFSG.EvenSporadicStandard.HNRecog.Section4
