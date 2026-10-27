module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Rank
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup

variable {G : Type*} [Group G]

theorem card_centralizer_conj (c r : G) :
    Nat.card ↥(centralizer ({c * r * c⁻¹} : Set G)) = Nat.card ↥(centralizer ({r} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x * c, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun x => ⟨c * x * c⁻¹, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc c⁻¹ * (x : G) * c * r = c⁻¹ * ((x : G) * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * (x : G)) * c := by rw [h]
      _ = r * (c⁻¹ * (x : G) * c) := by group
  · have h := Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc c * (x : G) * c⁻¹ * (c * r * c⁻¹) = c * ((x : G) * r) * c⁻¹ := by group
      _ = c * (r * (x : G)) * c⁻¹ := by rw [h]
      _ = c * r * c⁻¹ * (c * (x : G) * c⁻¹) := by group

section Finite

variable [Finite G]

theorem card_orbit_conj_eq (r : G) :
    Nat.card (MulAction.orbit (ConjAct G) r) =
      Nat.card G / Nat.card (Subgroup.centralizer ({r} : Set G)) := by
  rw [Nat.card_coe_set_eq]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) r)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have hpos : 0 < Nat.card (Subgroup.centralizer ({r} : Set G)) := Nat.card_pos
  exact (Nat.div_eq_of_eq_mul_right hpos h1.symm).symm

theorem cover_by_classes {α : Type*} (X : Set G)
    (hX : ∀ c g, g ∈ X → c * g * c⁻¹ ∈ X) {k : ℕ} (r : Fin k → G) (hr : ∀ j, r j ∈ X)
    (inv : G → α) (hinv : ∀ c g, inv (c * g * c⁻¹) = inv g)
    (hdist : ∀ j j', inv (r j) = inv (r j') → j = j')
    (hsum : ∑ j, Nat.card G / Nat.card (Subgroup.centralizer ({r j} : Set G)) = Nat.card X) :
    ∀ g ∈ X, ∃ j, ∃ c : G, g = c * r j * c⁻¹ := by
  have hmem : ∀ j, ∀ x ∈ MulAction.orbit (ConjAct G) (r j), x ∈ X := by
    intro j x hx
    obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.1 hx
    rw [ConjAct.smul_def]
    exact hX _ _ (hr j)
  have hcard : Nat.card (Σ j : Fin k, MulAction.orbit (ConjAct G) (r j)) = Nat.card X := by
    rw [Nat.card_sigma, ← hsum]
    exact Finset.sum_congr rfl fun j _ => card_orbit_conj_eq (r j)
  let φ : (Σ j : Fin k, MulAction.orbit (ConjAct G) (r j)) → X :=
    fun p => ⟨p.2.1, hmem p.1 p.2.1 p.2.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨j, x, hx⟩ ⟨j', y, hy⟩ hxy
    have hxy' : x = y := congrArg Subtype.val hxy
    subst hxy'
    have h1 : inv x = inv (r j) := by
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hx
      rw [← hc, ConjAct.smul_def, hinv]
    have h2 : inv x = inv (r j') := by
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hy
      rw [← hc, ConjAct.smul_def, hinv]
    obtain rfl := hdist j j' (h1.symm.trans h2)
    rfl
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  intro g hg
  obtain ⟨⟨j, x, hx⟩, hp⟩ := hbij.2 ⟨g, hg⟩
  have hxg : x = g := congrArg Subtype.val hp
  subst hxg
  obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.1 hx
  exact ⟨j, ConjAct.ofConjAct c, by rw [← hc, ConjAct.smul_def]⟩

theorem card_orbit_subgroup_mul (H : Subgroup G) (r : G) :
    Nat.card {x : G // ∃ h ∈ H, x = h * r * h⁻¹} * Nat.card ↥(H ⊓ centralizer ({r} : Set G)) =
      Nat.card ↥H := by
  letI : MulAction ↥H G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have hsmul : ∀ (h : ↥H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun h x => rfl
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (↥H) r)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
  have e1 : Nat.card (MulAction.orbit (↥H) r) = Nat.card {x : G // ∃ h ∈ H, x = h * r * h⁻¹} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h r).symm ▸ rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have e2 : Nat.card (MulAction.stabilizer (↥H) r) = Nat.card ↥(H ⊓ centralizer ({r} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun h => ⟨(h.1 : G), h.1.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
        left_inv := fun h => rfl
        right_inv := fun x => rfl }
    · have h2 : (h.1 • r : G) = r := h.2
      rw [hsmul] at h2
      calc (h.1 : G) * r = ((h.1 : G) * r * (h.1 : G)⁻¹) * (h.1 : G) := by group
        _ = r * (h.1 : G) := by rw [h2]
    · show (⟨x.1, _⟩ : ↥H) • r = r
      rw [hsmul]
      have h3 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2
      calc (x : G) * r * (x : G)⁻¹ = (r * (x : G)) * (x : G)⁻¹ := by rw [h3]
        _ = r := by group
  rw [e1, e2] at h1
  rw [mul_comm]
  exact h1

theorem single_orbit (H : Subgroup G) (X : Set G) (hX : ∀ h ∈ H, ∀ g ∈ X, h * g * h⁻¹ ∈ X)
    {r : G} (hr : r ∈ X)
    (hcard : Nat.card ↥H = Nat.card X * Nat.card ↥(H ⊓ centralizer ({r} : Set G))) :
    ∀ g ∈ X, ∃ h ∈ H, g = h * r * h⁻¹ := by
  have hpos : 0 < Nat.card ↥(H ⊓ centralizer ({r} : Set G)) := Nat.card_pos
  have h1 := card_orbit_subgroup_mul H r
  set O : Set G := {x : G | ∃ h ∈ H, x = h * r * h⁻¹} with hO
  have hOX : O ⊆ X := by
    rintro _ ⟨h, hh, rfl⟩
    exact hX h hh r hr
  have hcardO : Nat.card O = Nat.card X := by
    have e : Nat.card O = Nat.card {x : G // ∃ h ∈ H, x = h * r * h⁻¹} := rfl
    rw [e] at *
    have : Nat.card {x : G // ∃ h ∈ H, x = h * r * h⁻¹} *
        Nat.card ↥(H ⊓ centralizer ({r} : Set G)) =
        Nat.card X * Nat.card ↥(H ⊓ centralizer ({r} : Set G)) := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hfin : X.Finite := Set.toFinite X
  have hsub : X ⊆ O := by
    have h2 : O.ncard = X.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardO
    exact (Set.eq_of_subset_of_ncard_le hOX h2.ge hfin).ge
  intro g hg
  exact hsub hg

end Finite

end CFSG.EvenSporadicStandard.Fin76b.U16
