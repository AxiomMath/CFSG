module

public import CFSG.CharacterTheory.DihedralTIFusion.ClassSquareKernel
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.GH74.GLS.Stage4.Q9

theorem card_involutions_eq_card_div_centralizer {G : Type*} [Group G] [Fintype G] {z : G}
    (hz : orderOf z = 2) (hconj : ∀ u : G, orderOf u = 2 → IsConj z u) :
    (Finset.univ.filter (fun g : G => orderOf g = 2)).card =
      Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  classical
  have hmem : ∀ u : G, u ∈ (ConjClasses.mk z).carrier ↔ orderOf u = 2 := by
    intro u
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := h
      rw [hc.orderOf_eq (c : G)]
      exact hz
    · intro h
      exact (hconj u h).symm
  have h1 : Fintype.card (ConjClasses.mk z).carrier =
      Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) z) :=
    ConjClasses.card_carrier z
  have h2 : Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Fintype.card (MulAction.stabilizer (ConjAct G) z) := by
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  have h3 : Fintype.card (ConjClasses.mk z).carrier =
      (Finset.univ.filter (fun g : G => orderOf g = 2)).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hmem)
  rw [← h3, h1, h2, Nat.card_eq_fintype_card]

theorem sum_irr_invol_products_filter {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) {z : G} (hz : orderOf z = 2)
    (hconj : ∀ u : G, orderOf u = 2 → IsConj z u) :
    ∑ x ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ y ∈ Finset.univ.filter (fun g : G => orderOf g = 2), χ (x * y) =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 * χ z ^ 2 /
        χ 1 := by
  classical
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  have hC : Finset.univ.filter (IsConj z) = Finset.univ.filter (fun g : G => orderOf g = 2) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := h
      rw [← hc.orderOf_eq (c : G)]
      exact hz
    · exact hconj u
  have h := CFSG.DihedralTIFusion.class_sum_square_trace ρ hirr z
  rw [hC, card_involutions_eq_card_div_centralizer hz hconj] at h
  have hne : ρ.character 1 ≠ 0 := by
    have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    rw [Representation.char_one]
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  rw [eq_div_iff hne, h]
  ring

theorem sum_irr_invol_products {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ BlocksIrr G) {z : G} (hz : orderOf z = 2)
    (hconj : ∀ u : G, orderOf u = 2 → IsConj z u) :
    ∑ x : G, ∑ y : G, (if orderOf x = 2 ∧ orderOf y = 2 then χ (x * y) else 0) =
      ((Nat.card G / Nat.card (Subgroup.centralizer ({z} : Set G)) : ℕ) : ℂ) ^ 2 * χ z ^ 2 /
        χ 1 := by
  rw [← sum_irr_invol_products_filter hχ hz hconj, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_filter]
  by_cases hx : orderOf x = 2
  · simp [hx]
  · simp [hx]

end CFSG.GH74.GLS.Stage4.Q9
