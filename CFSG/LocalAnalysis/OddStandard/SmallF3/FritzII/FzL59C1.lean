module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

theorem fzl59c_conj_closure {S : Set G} {F : Subgroup G} {g : G}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ F) : ∀ y ∈ closure S, g * y * g⁻¹ ∈ F := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simpa using F.one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact F.mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact F.inv_mem hx

theorem fzl59c_conj_sup {P Q F : Subgroup G} {g : G} (hP : ∀ x ∈ P, g * x * g⁻¹ ∈ F)
    (hQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ F) : ∀ x ∈ P ⊔ Q, g * x * g⁻¹ ∈ F := by
  intro x hx
  have h : P ⊔ Q ≤ F.comap (MulAut.conj g).toMonoidHom := sup_le hP hQ
  exact h hx

theorem fzl59c_mem_normalizer_of_sq {M : Subgroup G} {g : G} (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, g ^ 2 * m = m * g ^ 2) : g ∈ normalizer M := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => h1 m hm, fun hm => ?_⟩
  have hc := h2 (g * m * g⁻¹) hm
  have hm2 : g ^ 2 * m = m * g ^ 2 := by
    have e1 : g ^ 2 * m = g⁻¹ * (g ^ 2 * (g * m * g⁻¹)) * g := by
      simp only [sq]
      group
    have e2 : g⁻¹ * ((g * m * g⁻¹) * g ^ 2) * g = m * g ^ 2 := by
      simp only [sq]
      group
    rw [e1, hc, e2]
  have e : g * (g * m * g⁻¹) * g⁻¹ = m := by
    have e3 : g * (g * m * g⁻¹) * g⁻¹ = (g ^ 2 * m) * (g ^ 2)⁻¹ := by
      simp only [sq]
      group
    have e4 : (m * g ^ 2) * (g ^ 2)⁻¹ = m := by simp
    rw [e3, hm2, e4]
  have := h1 _ hm
  rwa [e] at this

def fzl59c_modCent (M : Subgroup G) (X : Set G) : Subgroup G where
  carrier := {g | g ∈ normalizer M ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ M}
  one_mem' := ⟨one_mem _, fun x _ => by simpa using M.one_mem⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgx⟩ ⟨hg', hgx'⟩
    refine ⟨mul_mem hg hg', fun x hx => ?_⟩
    have e : g * g' * x * (g * g')⁻¹ * x⁻¹ =
        g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e]
    refine M.mul_mem ?_ (hgx x hx)
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp (hgx' x hx)
  inv_mem' := by
    rintro g ⟨hg, hgx⟩
    refine ⟨inv_mem hg, fun x hx => ?_⟩
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem hg) _).mp (M.inv_mem (hgx x hx))

theorem fzl59c_mem_modCent {M : Subgroup G} {X : Set G} {g : G} :
    g ∈ fzl59c_modCent M X ↔ g ∈ normalizer M ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ M :=
  Iff.rfl

theorem fzl59c_mem_sup_zpowers {H : Subgroup G} {a : G} (hc : ∀ h ∈ H, a * h = h * a)
    (ha : a ^ 2 ∈ H) {x : G} (hx : x ∈ H ⊔ zpowers a) : x ∈ H ∨ ∃ h ∈ H, x = h * a := by
  let P : Subgroup G :=
    { carrier := {x | x ∈ H ∨ ∃ h ∈ H, x = h * a}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro x y (hx | ⟨h, hh, rfl⟩) (hy | ⟨h', hh', rfl⟩)
        · exact Or.inl (H.mul_mem hx hy)
        · exact Or.inr ⟨x * h', H.mul_mem hx hh', by rw [mul_assoc]⟩
        · refine Or.inr ⟨h * y, H.mul_mem hh hy, ?_⟩
          rw [mul_assoc, hc y hy, ← mul_assoc]
        · refine Or.inl ?_
          have e : h * a * (h' * a) = (h * h') * a ^ 2 := by
            calc h * a * (h' * a) = h * (a * h') * a := by group
              _ = h * (h' * a) * a := by rw [hc h' hh']
              _ = (h * h') * a ^ 2 := by
                simp only [sq]
                group
          rw [e]
          exact H.mul_mem (H.mul_mem hh hh') ha
      inv_mem' := by
        rintro x (hx | ⟨h, hh, rfl⟩)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ⟨h⁻¹ * (a ^ 2)⁻¹, H.mul_mem (H.inv_mem hh) (H.inv_mem ha), ?_⟩
          have e : a⁻¹ * h⁻¹ = h⁻¹ * a⁻¹ := by
            calc a⁻¹ * h⁻¹ = a⁻¹ * (h⁻¹ * a) * a⁻¹ := by group
              _ = a⁻¹ * (a * h⁻¹) * a⁻¹ := by rw [hc h⁻¹ (H.inv_mem hh)]
              _ = h⁻¹ * a⁻¹ := by group
          calc (h * a)⁻¹ = a⁻¹ * h⁻¹ := by group
            _ = h⁻¹ * a⁻¹ := e
            _ = h⁻¹ * (a ^ 2)⁻¹ * a := by
              simp only [sq]
              group }
  have hle : H ⊔ zpowers a ≤ P :=
    sup_le (fun x hx => Or.inl hx) (zpowers_le.mpr (Or.inr ⟨1, H.one_mem, by simp⟩))
  exact hle hx

theorem fzl59c_card_sup_zpowers [Finite G] {H : Subgroup G} {a : G}
    (hc : ∀ h ∈ H, a * h = h * a) (ha : a ^ 2 ∈ H) (hna : a ∉ H) :
    Nat.card ↥(H ⊔ zpowers a) = 2 * Nat.card ↥H := by
  have haK : a ∈ H ⊔ zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hHK : H ≤ H ⊔ zpowers a := le_sup_left
  have hidx : (H.subgroupOf (H ⊔ zpowers a)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haK⟩, ?_⟩
    rintro ⟨x, hxK⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases fzl59c_mem_sup_zpowers hc ha hxK with hx | ⟨h, hh, rfl⟩
    · right
      refine ⟨hx, fun hxa => hna ?_⟩
      have := H.mul_mem (H.inv_mem hx) hxa
      simpa using this
    · left
      refine ⟨?_, fun hx => hna ?_⟩
      · have e : h * a * a = h * a ^ 2 := by
          simp only [sq]
          group
        rw [e]
        exact H.mul_mem hh ha
      · have := H.mul_mem (H.inv_mem hh) hx
        simpa using this
  have h := Subgroup.relIndex_mul_card H (H ⊔ zpowers a)
  rw [Subgroup.relIndex, hidx, inf_eq_left.mpr hHK] at h
  exact h.symm

theorem fzl59c_card_orbit_mul [Finite G] (H : Subgroup G) (x : G) :
    Nat.card {y : G | ∃ g ∈ H, g * x * g⁻¹ = y} *
      Nat.card ↥(H ⊓ centralizer ({x} : Set G)) = Nat.card ↥H := by
  letI : MulAction ↥H G :=
    { smul := fun g y => (g : G) * y * (g : G)⁻¹
      one_smul := fun y => by
        show ((1 : ↥H) : G) * y * ((1 : ↥H) : G)⁻¹ = y
        simp
      mul_smul := fun g g' y => by
        show ((g * g' : ↥H) : G) * y * ((g * g' : ↥H) : G)⁻¹ =
          (g : G) * ((g' : G) * y * (g' : G)⁻¹) * (g : G)⁻¹
        simp [mul_assoc] }
  have hsub : (centralizer ({x} : Set G)).subgroupOf H = MulAction.stabilizer ↥H x := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      MulAction.mem_stabilizer_iff]
    change (g : G) * x = x * (g : G) ↔ (g : G) * x * (g : G)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
  have hset : {y : G | ∃ g ∈ H, g * x * g⁻¹ = y} = MulAction.orbit ↥H x := by
    ext y
    simp only [Set.mem_setOf_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  have h1 := Subgroup.relIndex_mul_card (centralizer ({x} : Set G)) H
  rw [Subgroup.relIndex, hsub, MulAction.index_stabilizer, inf_comm] at h1
  rw [hset, Nat.card_coe_set_eq]
  exact h1

end CFSG.OddStandard.SmallF3.FritzII
