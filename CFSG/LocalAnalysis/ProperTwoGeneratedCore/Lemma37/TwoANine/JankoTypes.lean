module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

private theorem odd_three : Odd 3 :=
  ⟨1, rfl⟩

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem orderOf_liftOdd_sbar₁ : orderOf (liftOdd e Janko.sbar₁) = 3 := by
  rw [hJ.orderOf_liftOdd e (by rw [Janko.orderOf_sbar₁]; exact odd_three), Janko.orderOf_sbar₁]

theorem orderOf_liftOdd_sbar₂ : orderOf (liftOdd e Janko.sbar₂) = 3 := by
  rw [hJ.orderOf_liftOdd e (by rw [Janko.orderOf_sbar₂]; exact odd_three), Janko.orderOf_sbar₂]

theorem orderOf_liftOdd_sbar₃ : orderOf (liftOdd e Janko.sbar₃) = 3 := by
  rw [hJ.orderOf_liftOdd e (by rw [Janko.orderOf_sbar₃]; exact odd_three), Janko.orderOf_sbar₃]

private theorem card_centralizer_liftOdd {g : alternatingGroup (Fin 9)} (hg : orderOf g = 3) :
    Nat.card (centralizer ({liftOdd e g} : Set J)) =
      2 * Nat.card (centralizer ({g} : Set (alternatingGroup (Fin 9)))) := by
  have hgo : Odd (orderOf g) := by rw [hg]; exact odd_three
  rw [hJ.card_centralizer_of_odd e (hJ.odd_orderOf_liftOdd e hgo), hJ.proj_liftOdd e hgo]

theorem card_centralizer_liftOdd_sbar₁ :
    Nat.card (centralizer ({liftOdd e Janko.sbar₁} : Set J)) = 2160 := by
  rw [hJ.card_centralizer_liftOdd e Janko.orderOf_sbar₁, Janko.card_centralizer_sbar₁]

theorem card_centralizer_liftOdd_sbar₂ :
    Nat.card (centralizer ({liftOdd e Janko.sbar₂} : Set J)) = 108 := by
  rw [hJ.card_centralizer_liftOdd e Janko.orderOf_sbar₂, Janko.card_centralizer_sbar₂]

theorem card_centralizer_liftOdd_sbar₃ :
    Nat.card (centralizer ({liftOdd e Janko.sbar₃} : Set J)) = 162 := by
  rw [hJ.card_centralizer_liftOdd e Janko.orderOf_sbar₃, Janko.card_centralizer_sbar₃]

theorem orderOf_eq_three_of_pow_three {x : J} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    orderOf x = 3 ∧ proj e x ^ 3 = 1 ∧ proj e x ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨ho, by rw [← map_pow, hx3, map_one], fun h => hx1 ?_⟩
  exact hJ.eq_one_of_mem_center_of_odd ((proj_eq_one_iff e).mp h) (by rw [ho]; exact odd_three)

private theorem exists_conj_of_isConj {x : J} {g : alternatingGroup (Fin 9)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hg : orderOf g = 3) (hxg : IsConj g (proj e x)) :
    ∃ h : J, h * x * h⁻¹ = liftOdd e g := by
  have hxo : Odd (orderOf x) := by
    rw [(hJ.orderOf_eq_three_of_pow_three e hx3 hx1).1]
    exact odd_three
  exact hJ.exists_conj_eq_liftOdd e hxo (by rw [hg]; exact odd_three) hxg.symm

theorem exists_conj_liftOdd_sbar {x : J} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ h : J, h * x * h⁻¹ = liftOdd e Janko.sbar₁ ∨ h * x * h⁻¹ = liftOdd e Janko.sbar₂ ∨
      h * x * h⁻¹ = liftOdd e Janko.sbar₃ := by
  obtain ⟨-, h3, h1⟩ := hJ.orderOf_eq_three_of_pow_three e hx3 hx1
  rcases Janko.isConj_sbar_of_pow_three_eq_one h3 h1 with h | h | h
  · obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₁ h
    exact ⟨u, Or.inl hu⟩
  · obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₂ h
    exact ⟨u, Or.inr (Or.inl hu)⟩
  · obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₃ h
    exact ⟨u, Or.inr (Or.inr hu)⟩

theorem card_centralizer_of_cycleType_eq_three {x : J} (hx3 : x ^ 3 = 1)
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType = {3}) :
    Nat.card (centralizer ({x} : Set J)) = 2160 := by
  have hx1 : x ≠ 1 := fun h => ne_one_of_cycleType_eq hx (by decide) (by rw [h, map_one])
  obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₁ (Janko.isConj_sbar₁ hx)
  rw [← Janko.card_centralizer_conj u x, hu, hJ.card_centralizer_liftOdd_sbar₁ e]

theorem card_centralizer_of_cycleType_eq_three_three {x : J} (hx3 : x ^ 3 = 1)
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType = {3, 3}) :
    Nat.card (centralizer ({x} : Set J)) = 108 := by
  have hx1 : x ≠ 1 := fun h => ne_one_of_cycleType_eq hx (by decide) (by rw [h, map_one])
  obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₂ (Janko.isConj_sbar₂ hx)
  rw [← Janko.card_centralizer_conj u x, hu, hJ.card_centralizer_liftOdd_sbar₂ e]

theorem card_centralizer_of_cycleType_eq_three_three_three {x : J} (hx3 : x ^ 3 = 1)
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)).cycleType = {3, 3, 3}) :
    Nat.card (centralizer ({x} : Set J)) = 162 := by
  have hx1 : x ≠ 1 := fun h => ne_one_of_cycleType_eq hx (by decide) (by rw [h, map_one])
  obtain ⟨u, hu⟩ := hJ.exists_conj_of_isConj e hx3 hx1 Janko.orderOf_sbar₃ (Janko.isConj_sbar₃ hx)
  rw [← Janko.card_centralizer_conj u x, hu, hJ.card_centralizer_liftOdd_sbar₃ e]

private theorem exists_invert_of {g b : alternatingGroup (Fin 9)} (hg : orderOf g = 3)
    (hb : (b : Equiv.Perm (Fin 9)).cycleType = {2, 2, 2, 2}) (hbg : b * g * b⁻¹ = g⁻¹) :
    ∃ u : J, orderOf u = 2 ∧ u * liftOdd e g * u⁻¹ = (liftOdd e g)⁻¹ := by
  have hb' : ((proj e (someLift e b) : alternatingGroup (Fin 9)) :
      Equiv.Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
    rw [proj_someLift]
    exact hb
  have hgo : Odd (orderOf g) := by
    rw [hg]
    exact odd_three
  refine ⟨someLift e b, (hJ.orderOf_eq_two_of_cycleType_two_two_two_two e hb').1, ?_⟩
  exact hJ.conj_liftOdd_eq_inv e hgo (by rw [proj_someLift]; exact hbg)

theorem exists_invert_liftOdd_sbar₁ : ∃ u : J, orderOf u = 2 ∧
    u * liftOdd e Janko.sbar₁ * u⁻¹ = (liftOdd e Janko.sbar₁)⁻¹ :=
  hJ.exists_invert_of e Janko.orderOf_sbar₁ Janko.cycleType_bbar₁ Janko.bbar₁_conj_sbar₁

theorem exists_invert_liftOdd_sbar₂ : ∃ u : J, orderOf u = 2 ∧
    u * liftOdd e Janko.sbar₂ * u⁻¹ = (liftOdd e Janko.sbar₂)⁻¹ :=
  hJ.exists_invert_of e Janko.orderOf_sbar₂ Janko.cycleType_bbar₂ Janko.bbar₂_conj_sbar₂

theorem exists_invert_liftOdd_sbar₃ : ∃ u : J, orderOf u = 2 ∧
    u * liftOdd e Janko.sbar₃ * u⁻¹ = (liftOdd e Janko.sbar₃)⁻¹ :=
  hJ.exists_invert_of e Janko.orderOf_sbar₃ Janko.cycleType_bbar₃ Janko.bbar₃_conj_sbar₃

end IsTwoANine

namespace Janko

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))
include hH

theorem orderOf_s₁ : orderOf (s₁ e) = 3 := by
  rw [s₁, Subgroup.orderOf_coe, hH.orderOf_liftOdd_sbar₁ e]

theorem orderOf_s₂ : orderOf (s₂ e) = 3 := by
  rw [s₂, Subgroup.orderOf_coe, hH.orderOf_liftOdd_sbar₂ e]

theorem orderOf_s₃ : orderOf (s₃ e) = 3 := by
  rw [s₃, Subgroup.orderOf_coe, hH.orderOf_liftOdd_sbar₃ e]

theorem card_centralizer_s₁ :
    Nat.card (centralizer ({s₁ e} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 2160 := by
  rw [s₁, card_centralizer_inf_eq, hH.card_centralizer_liftOdd_sbar₁ e]

theorem card_centralizer_s₂ :
    Nat.card (centralizer ({s₂ e} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 108 := by
  rw [s₂, card_centralizer_inf_eq, hH.card_centralizer_liftOdd_sbar₂ e]

theorem card_centralizer_s₃ :
    Nat.card (centralizer ({s₃ e} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 := by
  rw [s₃, card_centralizer_inf_eq, hH.card_centralizer_liftOdd_sbar₃ e]

theorem exists_conj : ∀ x ∈ centralizer ({z} : Set G), x ^ 3 = 1 → x ≠ 1 →
    ∃ h ∈ centralizer ({z} : Set G), h * x * h⁻¹ = s₁ e ∨ h * x * h⁻¹ = s₂ e ∨
      h * x * h⁻¹ = s₃ e := by
  intro x hx hx3 hx1
  obtain ⟨h, hh⟩ := hH.exists_conj_liftOdd_sbar e (x := ⟨x, hx⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact hx3))
    (fun h => hx1 (congrArg Subtype.val h))
  refine ⟨h, h.2, ?_⟩
  rcases hh with hh | hh | hh
  · exact Or.inl (congrArg Subtype.val hh)
  · exact Or.inr (Or.inl (congrArg Subtype.val hh))
  · exact Or.inr (Or.inr (congrArg Subtype.val hh))

theorem exists_invert : ∀ s ∈ ({s₁ e, s₂ e, s₃ e} : Set G),
    ∃ b ∈ centralizer ({z} : Set G), orderOf b = 2 ∧ b * s * b⁻¹ = s⁻¹ := by
  have key : ∀ y : centralizer ({z} : Set G),
      (∃ u : centralizer ({z} : Set G), orderOf u = 2 ∧ u * y * u⁻¹ = y⁻¹) →
      ∃ b ∈ centralizer ({z} : Set G), orderOf b = 2 ∧ b * (y : G) * b⁻¹ = (y : G)⁻¹ := by
    rintro y ⟨u, hu, huy⟩
    exact ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu], congrArg Subtype.val huy⟩
  rintro s (rfl | rfl | rfl)
  · exact key _ (hH.exists_invert_liftOdd_sbar₁ e)
  · exact key _ (hH.exists_invert_liftOdd_sbar₂ e)
  · exact key _ (hH.exists_invert_liftOdd_sbar₃ e)

omit hH in
theorem t_ne : t e ≠ z := by
  intro h
  have hz : (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set G)) ∈
      center (centralizer ({z} : Set G)) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have h1 := congrArg (proj e) (Subtype.ext h :
    someLift e tbar = (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set G)))
  rw [proj_someLift, (proj_eq_one_iff e).mpr hz] at h1
  exact ne_one_of_cycleType_eq cycleType_tbar (by decide) h1

theorem orderOf_t : orderOf (t e) = 2 := by
  have ht : ((proj e (someLift e tbar) : alternatingGroup (Fin 9)) :
      Equiv.Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
    rw [proj_someLift]
    exact cycleType_tbar
  rw [t, Subgroup.orderOf_coe]
  exact (hH.orderOf_eq_two_of_cycleType_two_two_two_two e ht).1

theorem t_mul_s₁ : t e * s₁ e * (t e)⁻¹ = (s₁ e)⁻¹ := by
  have hodd : Odd (orderOf sbar₁) := by
    rw [orderOf_sbar₁]
    exact odd_three
  exact congrArg Subtype.val (hH.conj_liftOdd_eq_inv e hodd (u := someLift e tbar)
    (by rw [proj_someLift]; exact tbar_conj_sbar₁))

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
