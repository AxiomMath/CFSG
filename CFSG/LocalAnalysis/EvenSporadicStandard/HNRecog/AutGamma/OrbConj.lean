module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

private theorem orderOf_conj (g w : G) : orderOf (g * w * g⁻¹) = orderOf w := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) w
  rwa [MulAut.conj_apply] at h

private theorem conj_mem_Gx' (g : G) {x t : G} :
    g * t * g⁻¹ ∈ Gx (g * x * g⁻¹) ↔ t ∈ Gx x := by
  rw [mem_Gx, mem_Gx]
  constructor
  · intro h
    have h' : g * (x * t) * g⁻¹ = g * (t * x) * g⁻¹ := by
      calc g * (x * t) * g⁻¹ = (g * x * g⁻¹) * (g * t * g⁻¹) := by group
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := h
        _ = g * (t * x) * g⁻¹ := by group
    exact conj_injective (x := g) h'
  · intro h
    show (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹)
    rw [show (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ by group,
      show (g * t * g⁻¹) * (g * x * g⁻¹) = g * (t * x) * g⁻¹ by group, h]

private theorem conj_mem_Gxy' (g : G) {x c t : G} :
    g * t * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) ↔ t ∈ Gxy x c := by
  rw [mem_Gxy, mem_Gxy]
  rw [conj_mem_Gx' (g := g) (x := x) (t := t), conj_mem_Gx' (g := g) (x := c) (t := t)]

private theorem conj_mem_Gxyz' (g : G) {x y w t : G} :
    g * t * g⁻¹ ∈ Gxyz (g * x * g⁻¹) (g * y * g⁻¹) (g * w * g⁻¹) ↔
      t ∈ Gxyz x y w := by
  rw [mem_Gxyz, mem_Gxyz]
  rw [conj_mem_Gx' (g := g) (x := x) (t := t), conj_mem_Gx' (g := g) (x := y) (t := t),
    conj_mem_Gx' (g := g) (x := w) (t := t)]

private theorem map_Gxyz_conj (g x t c : G) :
    (Gxyz x t c).map (MulAut.conj g).toMonoidHom =
      Gxyz (g * x * g⁻¹) (g * t * g⁻¹) (g * c * g⁻¹) := by
  ext d
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have h := conj_mem_Gxyz' (g := g) (x := x) (y := t) (w := c) (t := g⁻¹ * d * g)
  rw [show g * (g⁻¹ * d * g) * g⁻¹ = d by group] at h
  exact h.symm

private noncomputable def conjGxyzMulEquiv (g x t c : G) :
    ↥(Gxyz x t c) ≃* ↥(Gxyz (g * x * g⁻¹) (g * t * g⁻¹) (g * c * g⁻¹)) :=
  ((Gxyz x t c).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (map_Gxyz_conj g x t c))

private theorem conj_isNonsplitDoubleCoverOfS5 (g : G) {x t c : G}
    (h : IsNonsplitDoubleCoverOfS5 ↥(Gxyz x t c)) :
    IsNonsplitDoubleCoverOfS5 ↥(Gxyz (g * x * g⁻¹) (g * t * g⁻¹) (g * c * g⁻¹)) :=
  IsNonsplitDoubleCoverOfS5.of_mulEquiv (conjGxyzMulEquiv g x t c) h

private theorem conj_nonempty_mulEquiv (g : G) {x t c : G} (D : Type*) [Group D]
    (h : Nonempty (↥(Gxyz x t c) ≃* D)) :
    Nonempty (↥(Gxyz (g * x * g⁻¹) (g * t * g⁻¹) (g * c * g⁻¹)) ≃* D) :=
  ⟨(conjGxyzMulEquiv g x t c).symm.trans h.some⟩

theorem isConj_conj_iff (g : G) {x : G} : IsConj a (g * x * g⁻¹) ↔ IsConj a x := by
  constructor
  · intro h
    exact h.trans (IsConj.symm (isConj_iff.2 ⟨g, rfl⟩))
  · intro h
    exact h.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem conj_mem_orb2A (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb2A a (g * x * g⁻¹) ↔ c ∈ orb2A a x := by
  simp only [orb2A, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group]
  exact and_congr (isConj_conj_iff (x := c) g) (isConj_conj_iff (x := x * c) g)

theorem conj_mem_orb2B (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb2B a z (g * x * g⁻¹) ↔ c ∈ orb2B a z x := by
  simp only [orb2B, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group]
  exact and_congr (isConj_conj_iff (a := a) (x := c) g) (isConj_conj_iff (a := z) (x := x * c) g)

theorem conj_mem_orb3A (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb3A a (g * x * g⁻¹) ↔ c ∈ orb3A a x := by
  have aux : ((orb2A a (g * x * g⁻¹)) ∩ (orb2A a (g * c * g⁻¹))).Nonempty ↔
      (orb2A a x ∩ orb2A a c).Nonempty := by
    constructor
    · rintro ⟨d, hd1, hd2⟩
      refine ⟨g⁻¹ * d * g, ?_, ?_⟩
      · have h := (conj_mem_orb2A (a := a) (g := g⁻¹) (x := g * x * g⁻¹) (c := d)).mpr hd1
        rw [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h
        simpa only [inv_inv] using h
      · have h := (conj_mem_orb2A (a := a) (g := g⁻¹) (x := g * c * g⁻¹) (c := d)).mpr hd2
        rw [show g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c by group] at h
        simpa only [inv_inv] using h
    · rintro ⟨d, hd1, hd2⟩
      exact ⟨g * d * g⁻¹, (conj_mem_orb2A (a := a) (g := g) (x := x) (c := d)).mpr hd1,
        (conj_mem_orb2A (a := a) (g := g) (x := c) (c := d)).mpr hd2⟩
  simp only [orb3A, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, orderOf_conj g (x * c)]
  exact and_congr (isConj_conj_iff (x := c) g) (and_congr Iff.rfl aux)

theorem conj_mem_orb4A (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb4A a z (g * x * g⁻¹) ↔ c ∈ orb4A a z x := by
  simp only [orb4A, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, conj_pow]
  exact and_congr (isConj_conj_iff (a := a) (x := c) g)
    (isConj_conj_iff (a := z) (x := (x * c) ^ 2) g)

theorem conj_mem_orb4B (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb4B a (g * x * g⁻¹) ↔ c ∈ orb4B a x := by
  simp only [orb4B, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, conj_pow]
  exact and_congr (isConj_conj_iff (x := c) g) (isConj_conj_iff (x := (x * c) ^ 2) g)

theorem conj_mem_orb6A (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb6A a (g * x * g⁻¹) ↔ c ∈ orb6A a x := by
  simp only [orb6A, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group,
    orderOf_conj g (x * c), conj_pow]
  exact and_congr (isConj_conj_iff (x := c) g)
    (and_congr Iff.rfl (isConj_conj_iff (x := (x * c) ^ 3) g))

theorem conj_mem_oddSet (g : G) {x c : G} :
    g * c * g⁻¹ ∈ oddSet a (g * x * g⁻¹) ↔ c ∈ oddSet a x := by
  simp only [oddSet, Set.mem_setOf_eq]
  rw [show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, orderOf_conj g (x * c)]
  refine and_congr (isConj_conj_iff (x := c) g) (and_congr ?_ (and_congr Iff.rfl ?_))
  · exact (conj_injective (x := g)).ne_iff
  · constructor
    · rintro ⟨t, ht, hmem⟩
      refine ⟨g⁻¹ * t * g, ?_, ?_⟩
      · have h := (isConj_conj_iff (a := a) (g := g⁻¹) (x := t)).2 ht
        rwa [inv_inv] at h
      · have hL : g * (g⁻¹ * t * g) * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) := by
          rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
        exact (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := g⁻¹ * t * g)).mp hL
    · rintro ⟨t, ht, hmem⟩
      exact ⟨g * t * g⁻¹, (isConj_conj_iff (a := a) (x := t) g).2 ht,
        (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := t)).mpr hmem⟩

theorem conj_mem_orb5A (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb5A a (g * x * g⁻¹) ↔ c ∈ orb5A a x := by
  simp only [orb5A, Set.mem_setOf_eq]
  rw [conj_mem_oddSet (g := g) (x := x) (c := c),
    show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, orderOf_conj g (x * c)]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h t ht hmem
    have ht' : IsConj a (g * t * g⁻¹) := (isConj_conj_iff (a := a) (x := t) g).2 ht
    have hmem' : g * t * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) :=
      (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := t)).mpr hmem
    have hsrc := h (g * t * g⁻¹) ht' hmem'
    have hbig := conj_isNonsplitDoubleCoverOfS5 (g := g⁻¹) (x := g * x * g⁻¹)
      (t := g * t * g⁻¹) (c := g * c * g⁻¹) hsrc
    rw [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group,
      show g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t by group,
      show g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c by group] at hbig
    exact hbig
  · intro h t ht hmem
    have ht' : IsConj a (g⁻¹ * t * g) := by
      have h := (isConj_conj_iff (a := a) (g := g⁻¹) (x := t)).2 ht
      rwa [inv_inv] at h
    have hmem' : g⁻¹ * t * g ∈ Gxy x c := by
      have hL : g * (g⁻¹ * t * g) * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) := by
        rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := g⁻¹ * t * g)).mp hL
    have hsrc := h (g⁻¹ * t * g) ht' hmem'
    have hbig := conj_isNonsplitDoubleCoverOfS5 (g := g) (x := x) (t := g⁻¹ * t * g)
      (c := c) hsrc
    rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at hbig

theorem conj_mem_orb5E (g : G) {x c : G} :
    g * c * g⁻¹ ∈ orb5E a (g * x * g⁻¹) ↔ c ∈ orb5E a x := by
  simp only [orb5E, Set.mem_setOf_eq]
  rw [conj_mem_oddSet (g := g) (x := x) (c := c),
    show (g * x * g⁻¹) * (g * c * g⁻¹) = g * (x * c) * g⁻¹ by group, orderOf_conj g (x * c)]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h t ht hmem
    have ht' : IsConj a (g * t * g⁻¹) := (isConj_conj_iff (a := a) (x := t) g).2 ht
    have hmem' : g * t * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) :=
      (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := t)).mpr hmem
    have hsrc := h (g * t * g⁻¹) ht' hmem'
    have hbig := conj_nonempty_mulEquiv (g := g⁻¹) (x := g * x * g⁻¹) (t := g * t * g⁻¹)
      (c := g * c * g⁻¹) (Multiplicative (ZMod 2) × DihedralGroup 5) hsrc
    rw [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group,
      show g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t by group,
      show g⁻¹ * (g * c * g⁻¹) * (g⁻¹)⁻¹ = c by group] at hbig
    exact hbig
  · intro h t ht hmem
    have ht' : IsConj a (g⁻¹ * t * g) := by
      have h := (isConj_conj_iff (a := a) (g := g⁻¹) (x := t)).2 ht
      rwa [inv_inv] at h
    have hmem' : g⁻¹ * t * g ∈ Gxy x c := by
      have hL : g * (g⁻¹ * t * g) * g⁻¹ ∈ Gxy (g * x * g⁻¹) (g * c * g⁻¹) := by
        rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact (conj_mem_Gxy' (g := g) (x := x) (c := c) (t := g⁻¹ * t * g)).mp hL
    have hsrc := h (g⁻¹ * t * g) ht' hmem'
    have hbig := conj_nonempty_mulEquiv (g := g) (x := x) (t := g⁻¹ * t * g) (c := c)
      (Multiplicative (ZMod 2) × DihedralGroup 5) hsrc
    rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at hbig

theorem conj_mem_orbitOf (g : G) (k : OrbitKind) {x c : G} :
    g * c * g⁻¹ ∈ orbitOf a z (g * x * g⁻¹) k ↔ c ∈ orbitOf a z x k := by
  cases k
  · simpa only [orbitOf] using conj_mem_orb2A (a := a) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb2B (a := a) (z := z) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb3A (a := a) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb4A (a := a) (z := z) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb4B (a := a) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb5A (a := a) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb5E (a := a) (g := g) (x := x) (c := c)
  · simpa only [orbitOf] using conj_mem_orb6A (a := a) (g := g) (x := x) (c := c)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
