module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec1Kind

public section

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Cfg

variable {d : Datum A} (K : Cfg d)

include K

theorem elemAb32_le_S {E : Subgroup G} (hE : E ≤ d.X) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 32) : E ≤ d.S := by
  by_contra hnot
  obtain ⟨e, heE, heS⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have heX : e ∈ d.X := hE heE
  have heQS : e ∉ d.QS := fun h => heS (K.c.involutions_in_S K.h K.sf K.hc h (h2 e heE))
  set E₀ : Subgroup G := d.QS ⊓ E with hE₀
  have hE₀S : E₀ ≤ d.S := fun x hx => K.c.involutions_in_S K.h K.sf K.hc hx.1 (h2 x hx.2)
  let Fk : Kind → Set G := fun k =>
    {x | x ∈ E ∧ x ∉ d.QS ∧ ∃ y, K.c.rep k = some y ∧ ∃ a ∈ d.QS, x = a * y}
  have hFk : ∀ k, (Fk k).ncard ≤ Nat.card E₀ := by
    intro k
    by_cases hne : (Fk k).Nonempty
    · obtain ⟨x₀, hx₀E, hx₀Q, y₀, hy₀, a₀, ha₀, rfl⟩ := hne
      have hy₀X : y₀ ∈ d.X := (K.c.rep_mem k y₀ hy₀).1
      have hsub : Fk k ⊆ (fun t => (a₀ * y₀) * t) '' (E₀ : Set G) := by
        rintro x ⟨hxE, hxQ, y, hy, a, ha, rfl⟩
        have hyy : y = y₀ := Option.some.inj (hy.symm.trans hy₀)
        subst hyy
        refine ⟨(a₀ * y)⁻¹ * (a * y), ⟨?_, E.mul_mem (E.inv_mem hx₀E) hxE⟩, by group⟩
        have := ChartShape.conj_inv_mem_QS d hy₀X (d.QS.mul_mem (d.QS.inv_mem ha₀) ha)
        simpa [mul_assoc] using this
      calc (Fk k).ncard ≤ ((fun t => (a₀ * y₀) * t) '' (E₀ : Set G)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (E₀ : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
        _ = Nat.card E₀ := (Nat.card_coe_set_eq _).symm
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
  have hcover : (E : Set G) ⊆ (E₀ : Set G) ∪ Fk Kind.field ∪ Fk Kind.graph ∪ Fk Kind.unitary := by
    intro x hx
    by_cases hxQ : x ∈ d.QS
    · exact Or.inl (Or.inl (Or.inl ⟨hxQ, hx⟩))
    · obtain ⟨k, y, hy, a, ha, rfl⟩ := K.c.cover x (hE hx) hxQ
      cases k
      · exact Or.inl (Or.inl (Or.inr ⟨hx, hxQ, y, hy, a, ha, rfl⟩))
      · exact Or.inl (Or.inr ⟨hx, hxQ, y, hy, a, ha, rfl⟩)
      · exact Or.inr ⟨hx, hxQ, y, hy, a, ha, rfl⟩
  have hcnt : 32 ≤ Nat.card E₀ + (Fk Kind.field).ncard + (Fk Kind.graph).ncard +
      (Fk Kind.unitary).ncard := by
    have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
    have h2 := Set.ncard_union_le ((E₀ : Set G) ∪ Fk Kind.field ∪ Fk Kind.graph) (Fk Kind.unitary)
    have h3 := Set.ncard_union_le ((E₀ : Set G) ∪ Fk Kind.field) (Fk Kind.graph)
    have h4 := Set.ncard_union_le (E₀ : Set G) (Fk Kind.field)
    have e0 : (E : Set G).ncard = 32 := by rw [← hcard]; exact (Nat.card_coe_set_eq _).symm
    have e1 : (E₀ : Set G).ncard = Nat.card E₀ := (Nat.card_coe_set_eq _).symm
    omega
  have hE₀cd : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => hab x hx.2 y hy.2
  have hE₀sq : ∀ x ∈ E₀, x * x = 1 := fun x hx => h2 x hx.2
  obtain ⟨k, p, hp, hact⟩ := K.exists_pure_conj heX heQS (h2 e heE)
  have hle8 : Nat.card E₀ ≤ 8 :=
    (K.elemAb_bound heX hp hact hE₀S hE₀cd hE₀sq (fun x hx => hab e heE x hx.2)).1
  have hf := hFk Kind.field
  have hg := hFk Kind.graph
  have hu := hFk Kind.unitary
  have h8 : Nat.card E₀ = 8 := by omega
  have hFu : (Fk Kind.unitary).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    omega
  obtain ⟨x, hxE, hxQ, y, hy, a, ha, rfl⟩ := hFu
  obtain ⟨hyX, -, hacty⟩ := K.c.rep_mem Kind.unitary y hy
  obtain ⟨u, hu', s₀, hs₀, rfl⟩ := d.mem_QS_iff.1 ha
  obtain ⟨p', hp', hact'⟩ := K.gi_of_kind hyX hacty hu' hs₀ rfl (h2 _ hxE)
  have := (K.elemAb_bound (hE hxE) hp' hact' hE₀S hE₀cd hE₀sq
    (fun z hz => hab _ hxE z hz.2)).2 rfl
  omega

theorem elemAb32 {E : Subgroup G} (hE : E ≤ d.X) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 32) : E = K.c.R1 ∨ E = K.c.R2 :=
  K.sf.elemAb_32 E (K.elemAb32_le_S hE hab h2 hcard) hab h2 hcard

end Cfg

end CFSG.OddStandard.ChengHeld.Sec1
