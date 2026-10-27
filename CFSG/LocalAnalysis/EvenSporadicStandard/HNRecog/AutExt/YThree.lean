module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8Three
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaA8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem mul_self_of_comm {M : Type} [Semigroup M] {x y : M} (hxy : x * y = y * x) :
    (x * y) * (x * y) = (x * x) * (y * y) :=
  Commute.mul_mul_mul_comm hxy.symm x y

private theorem mul_self_of_class (h : F5Base a z) {x : G} (hx : IsConj a x ∨ IsConj z x) :
    x * x = 1 := by
  have h2 : x ^ 2 = 1 := by simpa [h.orderOf_eq_two hx] using pow_orderOf_eq_one x
  rwa [pow_two] at h2

theorem exists_order_three_Gxyz (h : F5Base a z) {b w t : G} (hb : IsConj a b)
    (ht : t ∈ orb2A a b) (hw : w ∈ Gxy b t) (hw2 : w * w = 1) :
    ∃ ε ∈ Gxyz b w t, orderOf ε = 3 := by
  classical
  have hFb : F5Base b z := h.of_isConj hb (IsConj.refl z)
  have htb : t ∈ orb2A b b := ⟨hb.symm.trans ht.1, hb.symm.trans ht.2⟩
  have hb2 : b * b = 1 := mul_self_of_class h (Or.inl hb)
  have ht2 : t * t = 1 := mul_self_of_class h (Or.inl ht.1)
  have hbt : b * t = t * b := h.mul_comm (Or.inl hb) (Or.inl ht.1) (Or.inl ht.2)
  have hbX : b ∈ Gxy b t := mem_Gxy.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hbt.symm⟩
  have htX : t ∈ Gxy b t := mem_Gxy.mpr ⟨mem_Gx.mpr hbt, mem_Gx.mpr rfl⟩
  have hb_comm : ∀ y ∈ Gxy b t, b * y = y * b := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).1
  have ht_comm : ∀ y ∈ Gxy b t, t * y = y * t := fun y hy => mem_Gx.mp (mem_Gxy.mp hy).2
  have hbt_comm : ∀ y ∈ Gxy b t, (b * t) * y = y * (b * t) := by
    intro y hy
    rw [mul_assoc, ht_comm y hy, ← mul_assoc, hb_comm y hy, mul_assoc]
  have hcent : ∀ u : G, (u = 1 ∨ u = b ∨ u = t ∨ u = b * t) →
      ∀ y ∈ Gxy b t, u * y = y * u := by
    rintro u (rfl | rfl | rfl | rfl) y hy
    · rw [one_mul, mul_one]
    · exact hb_comm y hy
    · exact ht_comm y hy
    · exact hbt_comm y hy
  have hu2 : ∀ u : G, (u = 1 ∨ u = b ∨ u = t ∨ u = b * t) → u * u = 1 := by
    rintro u (rfl | rfl | rfl | rfl)
    · rw [one_mul]
    · exact hb2
    · exact ht2
    · rw [mul_self_of_comm hbt, hb2, ht2, mul_one]
  obtain ⟨n, hnA, hwn⟩ := decomp_2A_of_base hFb htb w hw
  obtain ⟨u, hu, hwu⟩ : ∃ u : G, (u = 1 ∨ u = b ∨ u = t ∨ u = b * t) ∧ w = u * n := by
    rcases hwn with h' | h' | h' | h'
    · exact ⟨1, Or.inl rfl, by rw [h', one_mul]⟩
    · exact ⟨b, Or.inr (Or.inl rfl), h'⟩
    · exact ⟨t, Or.inr (Or.inr (Or.inl rfl)), h'⟩
    · exact ⟨b * t, Or.inr (Or.inr (Or.inr rfl)), h'⟩
  have hnX : n ∈ Gxy b t := derivedOf_le _ hnA
  have hnn : n * n = 1 := by
    have h' := hw2
    rw [hwu, mul_self_of_comm (hcent u hu n hnX), hu2 u hu, one_mul] at h'
    exact h'
  obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
    (hFb.loc.fusion3.self.shape_2A t htb)
  set s8 : alternatingGroup (Fin 8) := e.symm ⟨n, hnA⟩ with hs8def
  have hs8 : ((e s8 : ↥(derivedOf (Gxy b t))) : G) = n := by
    rw [hs8def, MulEquiv.apply_symm_apply]
  have hs2 : s8 ^ 2 = 1 := by
    have hnn' : (⟨n, hnA⟩ : ↥(derivedOf (Gxy b t))) * ⟨n, hnA⟩ = 1 := Subtype.ext hnn
    rw [pow_two, hs8def, ← map_mul, hnn', map_one]
  obtain ⟨ε₀, hε₀, hε₀3, hε₀1, hε₀c⟩ := exists_three_cent_alt_eight (s := (s8 : Equiv.Perm (Fin 8)))
    s8.2 (by simpa using congrArg Subtype.val hs2)
  set ε8 : alternatingGroup (Fin 8) := ⟨ε₀, hε₀⟩ with hε8def
  have hε8c : ε8 * s8 = s8 * ε8 := Subtype.ext hε₀c
  have hε83 : ε8 ^ 3 = 1 := Subtype.ext (by simpa using hε₀3)
  have hε81 : ε8 ≠ 1 := fun h1 => hε₀1 (congrArg Subtype.val h1)
  have hεA : ((e ε8 : ↥(derivedOf (Gxy b t))) : G) ∈ derivedOf (Gxy b t) := (e ε8).2
  have hεX : ((e ε8 : ↥(derivedOf (Gxy b t))) : G) ∈ Gxy b t := derivedOf_le _ hεA
  have hε3 : ((e ε8 : ↥(derivedOf (Gxy b t))) : G) ^ 3 = 1 := by
    have h' : (e ε8) ^ 3 = 1 := by rw [← map_pow, hε83, map_one]
    simpa using congrArg Subtype.val h'
  have hε1 : ((e ε8 : ↥(derivedOf (Gxy b t))) : G) ≠ 1 := by
    intro h1
    apply hε81
    have h2 : e ε8 = 1 := Subtype.ext h1
    exact e.injective (h2.trans (map_one e).symm)
  have hεn : ((e ε8 : ↥(derivedOf (Gxy b t))) : G) * n =
      n * ((e ε8 : ↥(derivedOf (Gxy b t))) : G) := by
    have h' : e ε8 * e s8 = e s8 * e ε8 := by rw [← map_mul, ← map_mul, hε8c]
    have h'' := congrArg Subtype.val h'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs8] at h''
    exact h''
  refine ⟨((e ε8 : ↥(derivedOf (Gxy b t))) : G), mem_Gxyz.mpr ⟨(mem_Gxy.mp hεX).1, ?_,
    (mem_Gxy.mp hεX).2⟩, orderOf_eq_prime hε3 hε1⟩
  refine mem_Gx.mpr ?_
  calc w * ((e ε8 : ↥(derivedOf (Gxy b t))) : G)
      = u * (n * ((e ε8 : ↥(derivedOf (Gxy b t))) : G)) := by rw [hwu, mul_assoc]
    _ = u * (((e ε8 : ↥(derivedOf (Gxy b t))) : G) * n) := by rw [hεn]
    _ = (u * ((e ε8 : ↥(derivedOf (Gxy b t))) : G)) * n := by rw [mul_assoc]
    _ = (((e ε8 : ↥(derivedOf (Gxy b t))) : G) * u) * n := by rw [hcent u hu _ hεX]
    _ = ((e ε8 : ↥(derivedOf (Gxy b t))) : G) * w := by rw [hwu, mul_assoc]

end CFSG.EvenSporadicStandard.HNRecog.Section4
