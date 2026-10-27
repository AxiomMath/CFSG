module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableA

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HChar

open CFSG.GH74.QTGen4.Recog.G23.HCharData

namespace TabHyp

open Classical

variable {X : Type} [Group X] [Fintype X] {z : X} {rep : Fin 20 → X}

theorem central (h : TabHyp X z rep) (c : X) : c * z * c⁻¹ = z := by
  have hcard : Nat.card {x : X // IsConj (rep 1) x} = 1 := by
    rw [h.card_class 1]
    decide
  have hmem1 : IsConj (rep 1) z := by rw [h.rep_one]
  have hmem2 : IsConj (rep 1) (c * z * c⁻¹) := by
    rw [h.rep_one]
    exact isConj_iff.2 ⟨c, rfl⟩
  have := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact congrArg Subtype.val (this.elim ⟨c * z * c⁻¹, hmem2⟩ ⟨z, hmem1⟩)

theorem orderOf_conj_eq (c x : X) : orderOf (c * x * c⁻¹) = orderOf x := by
  have := (MulAut.conj c).orderOf_eq x
  simpa [MulAut.conj_apply] using this

theorem orderOf_eq_ord (h : TabHyp X z rep) (y : X) : orderOf y = hcOrd (h.cls y) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj_cls y)
  have := orderOf_conj_eq c (rep (h.cls y))
  rw [hc] at this
  rw [this, h.order_rep]

theorem inD_conj (h : TabHyp X z rep) (c x : X) : InD z (c * x * c⁻¹) ↔ InD z x := by
  have hone : ∀ a : X, c * a * c⁻¹ = 1 ↔ a = 1 := fun a => by
    constructor
    · intro hh
      calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
        _ = 1 := by rw [hh]; group
    · rintro rfl
      group
  have hz : ∀ a : X, c * a * c⁻¹ = z ↔ a = z := fun a => by
    constructor
    · intro hh
      calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
        _ = z := by rw [hh]; simpa using h.central c⁻¹
    · rintro rfl
      exact h.central c
  unfold InD
  simp only [conj_pow, ne_eq, hone, hz, orderOf_conj_eq]

theorem inD_iff (h : TabHyp X z rep) (y : X) : InD z y ↔ hcDfl (h.cls y) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj_cls y)
  have := h.inD_conj c (rep (h.cls y))
  rw [hc] at this
  rw [this, h.dflag]

theorem eq_z_iff (h : TabHyp X z rep) (y : X) : y = z ↔ h.cls y = 1 := by
  rw [h.cls_eq_iff, h.rep_one]
  constructor
  · rintro rfl
    exact IsConj.refl _
  · intro hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    rw [← hc, h.central]

theorem ct_val (h : TabHyp X z rep) (y : X) :
    Nat.card {u : X // orderOf u = 2 ∧ (if y = z then u ≠ z else u * y * u⁻¹ = y⁻¹)} =
      hcCt (h.cls y) := by
  by_cases hy : y = z
  · have : h.cls y = 1 := (h.eq_z_iff y).1 hy
    rw [this]
    simp only [hy, if_true]
    exact h.ct_z
  · have hne : h.cls y ≠ 1 := fun e => hy ((h.eq_z_iff y).2 e)
    simp only [hy, if_false]
    rw [← h.ct_other _ hne]
    obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj_cls y)
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c⁻¹).toEquiv fun u => ?_)
    show orderOf u = 2 ∧ u * y * u⁻¹ = y⁻¹ ↔
      orderOf (c⁻¹ * u * c⁻¹⁻¹) = 2 ∧ (c⁻¹ * u * c⁻¹⁻¹) * rep (h.cls y) * (c⁻¹ * u * c⁻¹⁻¹)⁻¹ =
        (rep (h.cls y))⁻¹
    rw [orderOf_conj_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hh
      rw [← hc] at hh
      calc (c⁻¹ * u * c⁻¹⁻¹) * rep (h.cls y) * (c⁻¹ * u * c⁻¹⁻¹)⁻¹
          = c⁻¹ * (u * (c * rep (h.cls y) * c⁻¹) * u⁻¹) * c := by group
        _ = c⁻¹ * (c * rep (h.cls y) * c⁻¹)⁻¹ * c := by rw [hh]
        _ = (rep (h.cls y))⁻¹ := by group
    · intro hh
      rw [← hc]
      calc u * (c * rep (h.cls y) * c⁻¹) * u⁻¹
          = c * ((c⁻¹ * u * c⁻¹⁻¹) * rep (h.cls y) * (c⁻¹ * u * c⁻¹⁻¹)⁻¹) * c⁻¹ := by group
        _ = c * (rep (h.cls y))⁻¹ * c⁻¹ := by rw [hh]
        _ = (c * rep (h.cls y) * c⁻¹)⁻¹ := by group

theorem card_filter_cls (h : TabHyp X z rep) (P : Fin 20 → Prop) [DecidablePred P] :
    (Finset.univ.filter fun y : X => P (h.cls y)).card = ∑ j, if P j then hcSize j else 0 := by
  rw [Finset.card_filter]
  have := h.sum_cls (fun j => if P j then (1 : ℕ) else 0)
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

end TabHyp

end CFSG.GH74.QTGen4.Recog.G23.P7.HChar
