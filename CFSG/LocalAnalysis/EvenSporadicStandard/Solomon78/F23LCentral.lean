module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {a a' b b' : G}
    (h1 : Commute b a') (h2 : Commute b' a) (h3 : Commute b b') :
    ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ := by
  have h2' : Commute b' a⁻¹ := Commute.inv_right h2
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * b * (a' * b') * (b⁻¹ * a⁻¹) * (b'⁻¹ * a'⁻¹)
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by simp only [mul_assoc]
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [Commute.eq h1]
    _ = a * a' * (b * b' * b⁻¹) * a⁻¹ * b'⁻¹ * a'⁻¹ := by simp only [mul_assoc]
    _ = a * a' * b' * a⁻¹ * b'⁻¹ * a'⁻¹ := by
        rw [Commute.eq h3, mul_assoc b' b b⁻¹, mul_inv_cancel, mul_one]
    _ = a * a' * (b' * a⁻¹) * b'⁻¹ * a'⁻¹ := by simp only [mul_assoc]
    _ = a * a' * (a⁻¹ * b') * b'⁻¹ * a'⁻¹ := by rw [Commute.eq h2']
    _ = a * a' * a⁻¹ * a'⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]

structure Setting612 (G : Type) [Group G] (L : Subgroup G) (t : G) : Prop where
  t_mem : t ∈ centralizer (L : Set G)
  t_order : orderOf t = 2
  cent : centralizer ({t} : Set G) = L ⊔ zpowers t
  disjoint : Disjoint L (zpowers t)
  perfect : ∀ w ∈ L, orderOf w = 2 →
    w ∈ ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆

namespace Setting612

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem t_sq (h : Setting612 G L t) : t * t = 1 :=
  mul_self_eq_one_of_orderOf_eq_two h.t_order

theorem t_ne (h : Setting612 G L t) : t ≠ 1 := ne_one_of_orderOf_eq_two h.t_order

theorem zpowers_le (h : Setting612 G L t) : zpowers t ≤ centralizer (L : Set G) :=
  Subgroup.zpowers_le.2 h.t_mem

theorem comm_of_mem (h : Setting612 G L t) {a : G} (ha : a ∈ L) : a * t = t * a :=
  mem_centralizer_iff.1 h.t_mem a ha

theorem not_mem_of (h : Setting612 G L t) : t ∉ L := fun htL =>
  h.t_ne (mem_bot.1 (h.disjoint.le_bot ⟨htL, mem_zpowers t⟩))

theorem exists_eq_mul (h : Setting612 G L t) {x : G} (hx : x ∈ centralizer ({t} : Set G)) :
    ∃ a ∈ L, x = a ∨ x = a * t := by
  rw [h.cent] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rcases zpow_eq_one_or_self_of_orderOf_eq_two h.t_order k with h1 | h1
  · exact ⟨a, ha, Or.inl (by rw [h1, mul_one])⟩
  · exact ⟨a, ha, Or.inr (by rw [h1])⟩

theorem commutator_le (h : Setting612 G L t) :
    ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := h.exists_eq_mul hx
  obtain ⟨a', ha', hya⟩ := h.exists_eq_mul hy
  have ht1 : Commute t a' := (h.comm_of_mem ha').symm
  have ht2 : Commute t a := (h.comm_of_mem ha).symm
  have hone1 : Commute (1 : G) a' := Commute.one_left a'
  have hone2 : Commute (1 : G) a := Commute.one_left a
  have key : ∀ b b' : G, (b = 1 ∨ b = t) → (b' = 1 ∨ b' = t) →
      ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ := by
    intro b b' hb hb'
    apply commutatorElement_mul_mul_of_commute
    · rcases hb with rfl | rfl
      · exact hone1
      · exact ht1
    · rcases hb' with rfl | rfl
      · exact hone2
      · exact ht2
    · rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;>
        first | exact Commute.refl _ | exact Commute.one_left _ | exact Commute.one_right _
  have hmain : ⁅x, y⁆ = ⁅a, a'⁆ := by
    rcases hxa with hxa | hxa <;> rcases hya with hya | hya
    · rw [hxa, hya]
    · have := key 1 t (Or.inl rfl) (Or.inr rfl)
      rw [mul_one] at this
      rw [hxa, hya, this]
    · have := key t 1 (Or.inr rfl) (Or.inl rfl)
      rw [mul_one] at this
      rw [hxa, hya, this]
    · rw [hxa, hya]
      exact key t t (Or.inr rfl) (Or.inr rfl)
  rw [hmain, commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem ha ha') (L.inv_mem ha)) (L.inv_mem ha')

theorem conj_not_mem (h : Setting612 G L t) (g : G) : g * t * g⁻¹ ∉ L := by
  intro hs
  set s : G := g * t * g⁻¹ with hsdef
  have hs2 : orderOf s = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) t
    rw [MulAut.conj_apply] at this
    rw [hsdef, this, h.t_order]
  have h1 := h.perfect s hs hs2
  have h2 : s ∈ ⁅centralizer ({s} : Set G), centralizer ({s} : Set G)⁆ :=
    commutator_mono inf_le_right inf_le_right h1
  have h3 : t ∈ ⁅(centralizer ({s} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom,
      (centralizer ({s} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    refine ⟨s, h2, ?_⟩
    simp [hsdef, mul_assoc]
  have h4 : (centralizer ({s} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * s = s * x := mem_centralizer_singleton_iff.1 hx
    refine mem_centralizer_singleton_iff.2 ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [← hsdef, hx']
      _ = t * (g⁻¹ * x * g) := by group
  have h5 : t ∈ L := h.commutator_le (commutator_mono h4 h4 h3)
  exact h.not_mem_of h5

theorem inv_mul_mul_of_mem (h : Setting612 G L t) {l : G} (hl : l ∈ L) : l⁻¹ * t * l = t := by
  rw [mul_assoc, ← h.comm_of_mem hl, ← mul_assoc, inv_mul_cancel, one_mul]

theorem isConj_mul_conj (h : Setting612 G L t) {u : G} (hu : IsConj t (t * u)) {l : G}
    (hl : l ∈ L) : IsConj t (t * (l * u * l⁻¹)) := by
  refine hu.trans (isConj_iff.2 ⟨l, ?_⟩)
  calc l * (t * u) * l⁻¹ = (l * t * l⁻¹) * (l * u * l⁻¹) := by group
    _ = t * (l * u * l⁻¹) := by rw [h.comm_of_mem hl, mul_inv_cancel_right]

variable [Finite G]

end Setting612

end CFSG.EvenSporadicStandard.Solomon78
