module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

variable {m : ℕ}

@[expose] def fixingMoved (π : Perm (Fin m)) : Subgroup (Perm (Fin m)) where
  carrier := {g | ∀ x, π x ≠ x → g x = x}
  mul_mem' := by
    intro a b ha hb x hx
    rw [Perm.mul_apply, hb x hx, ha x hx]
  one_mem' := fun x _ => rfl
  inv_mem' := by
    intro a ha x hx
    rw [Perm.inv_eq_iff_eq]
    exact (ha x hx).symm

@[expose] def altFixingMoved (π : Perm (Fin m)) : Subgroup (Perm (Fin m)) :=
  alternatingGroup (Fin m) ⊓ fixingMoved π

theorem mem_altFixingMoved {π g : Perm (Fin m)} :
    g ∈ altFixingMoved π ↔ g ∈ alternatingGroup (Fin m) ∧ ∀ x, π x ≠ x → g x = x := Iff.rfl

theorem card_fixed_add_two_mul_card_cycleType {π : Perm (Fin m)} (hπ : π * π = 1) :
    Fintype.card {x : Fin m // π x = x} + 2 * Multiset.card π.cycleType = m := by
  have hfix : Fintype.card {x : Fin m // π x = x} = m - π.support.card := by
    have h1 : Fintype.card {x : Fin m // π x = x} =
        Fintype.card (Function.fixedPoints π) := rfl
    rw [h1, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, Fintype.card_fin]
  have hsup := card_support_eq_two_mul_card_cycleType hπ
  have hle : π.support.card ≤ m := by
    simpa using Finset.card_le_univ π.support
  omega

theorem fixingMoved_le_centralizer {π : Perm (Fin m)} (hπ : π * π = 1) :
    fixingMoved π ≤ centralizer ({π} : Set (Perm (Fin m))) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : π x = x
  · have hgx : π (g x) = g x := by
      by_contra hne
      have hfix : g (g x) = g x := hg (g x) hne
      have hgx_id : g x = x := g.injective hfix
      exact hne (by rw [hgx_id, hx])
    rw [hx, hgx]
  · have hgx : g x = x := hg x hx
    have hpx : π (π x) ≠ π x := by
      rw [apply_apply_of_mul_self hπ x]
      exact fun h => hx h.symm
    have hgpx : g (π x) = π x := hg (π x) hpx
    rw [hgx, hgpx]

theorem conj_mem_fixingMoved {π : Perm (Fin m)} {g n : Perm (Fin m)}
    (hg : g ∈ centralizer ({π} : Set (Perm (Fin m)))) (hn : n ∈ fixingMoved π) :
    g * n * g⁻¹ ∈ fixingMoved π := by
  intro x hx
  simp only [Perm.mul_apply]
  have hgcomm : g * π = π * g := mem_centralizer_singleton_iff.mp hg
  have hgx : π (g⁻¹ x) ≠ g⁻¹ x := by
    intro h
    have h1 : g (π (g⁻¹ x)) = x := by rw [h]; simp
    have h2 : g (π (g⁻¹ x)) = π x := by
      have := congrArg (fun f : Perm (Fin m) => f (g⁻¹ x)) hgcomm
      simpa using this
    rw [h2] at h1
    exact hx h1
  rw [hn (g⁻¹ x) hgx]
  simp

theorem card_fixingMoved {π : Perm (Fin m)} :
    Nat.card (fixingMoved π) = (Fintype.card {x : Fin m // π x = x}).factorial := by
  classical
  have h1 : Nat.card (fixingMoved π) =
      Nat.card {f : Perm (Fin m) // ∀ a, ¬ (π a = a) → f a = a} :=
    Nat.card_congr (Equiv.refl _)
  rw [h1, ← Nat.card_congr (Perm.subtypeEquivSubtypePerm (fun x : Fin m => π x = x)),
    Nat.card_perm, Nat.card_eq_fintype_card]

private theorem two_mul_card_inf_alt_of_neg_one {H : Subgroup (Perm (Fin m))} {s : H}
    (hs : Equiv.Perm.sign (s : Perm (Fin m)) = -1) :
    2 * Nat.card (alternatingGroup (Fin m) ⊓ H : Subgroup (Perm (Fin m))) = Nat.card H := by
  classical
  let φ : H →* ℤˣ := (Equiv.Perm.sign : Perm (Fin m) →* ℤˣ).comp H.subtype
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · exact ⟨s, by change Equiv.Perm.sign (s : Perm (Fin m)) = -1; exact hs⟩
  have hker : Nat.card φ.ker * Nat.card ℤˣ = Nat.card H :=
    Subgroup.card_ker_mul_card_of_surjective (f := φ) hsurj
  have hker_eq : φ.ker = (alternatingGroup (Fin m)).subgroupOf H := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup, φ,
      MonoidHom.comp_apply]
  have hcard_eq : Nat.card (alternatingGroup (Fin m) ⊓ H : Subgroup (Perm (Fin m))) =
      Nat.card ((alternatingGroup (Fin m)).subgroupOf H) := by
    rw [← Subgroup.inf_subgroupOf_right (alternatingGroup (Fin m)) H]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show (alternatingGroup (Fin m)) ⊓ H ≤ H from inf_le_right)).toEquiv).symm
  have hZ : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  rw [hker_eq, ← hcard_eq, hZ] at hker
  calc 2 * Nat.card (alternatingGroup (Fin m) ⊓ H : Subgroup (Perm (Fin m))) =
        Nat.card (alternatingGroup (Fin m) ⊓ H : Subgroup (Perm (Fin m))) * 2 :=
      Nat.mul_comm _ _
    _ = Nat.card H := hker

theorem two_mul_card_altFixingMoved {π : Perm (Fin m)}
    (hf : 2 ≤ Fintype.card {x : Fin m // π x = x}) :
    2 * Nat.card (altFixingMoved π) = (Fintype.card {x : Fin m // π x = x}).factorial := by
  classical
  have htwo : 1 < Fintype.card {x : Fin m // π x = x} := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card htwo
  have hab' : (a : Fin m) ≠ (b : Fin m) := fun h => hab (Subtype.ext h)
  let s : fixingMoved π :=
    ⟨Equiv.swap a.1 b.1, fun x hx =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hx (by rw [h, a.2]))
        (fun h => hx (by rw [h, b.2]))⟩
  have hsign : Equiv.Perm.sign (s : Perm (Fin m)) = -1 := by
    show Equiv.Perm.sign (Equiv.swap a.1 b.1) = -1
    exact Equiv.Perm.sign_swap hab'
  have h := two_mul_card_inf_alt_of_neg_one (H := fixingMoved π) (s := s) hsign
  rw [card_fixingMoved] at h
  simpa [altFixingMoved] using h

theorem two_mul_card_alt_inf_centralizer {π : Perm (Fin m)} (hπ : π * π = 1) (h1 : π ≠ 1) :
    2 * Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
        Subgroup (Perm (Fin m))) =
      (Fintype.card {x : Fin m // π x = x}).factorial * 2 ^ Multiset.card π.cycleType *
        (Multiset.card π.cycleType).factorial := by
  classical
  have hex : ∃ x, π x ≠ x := by
    by_contra h
    exact h1 (Equiv.ext fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hex
  let s : centralizer ({π} : Set (Perm (Fin m))) :=
    ⟨Equiv.swap x (π x), by
      rw [mem_centralizer_singleton_iff]
      have hcomm : π * Equiv.swap x (π x) = Equiv.swap x (π x) * π := by
        calc π * Equiv.swap x (π x)
            = Equiv.swap (π x) (π (π x)) * π := mul_swap_eq_swap_mul π x (π x)
          _ = Equiv.swap (π x) x * π := by rw [apply_apply_of_mul_self hπ x]
          _ = Equiv.swap x (π x) * π := by rw [swap_comm]
      exact hcomm.symm⟩
  have hsign : Equiv.Perm.sign (s : Perm (Fin m)) = -1 := by
    show Equiv.Perm.sign (Equiv.swap x (π x)) = -1
    exact Equiv.Perm.sign_swap hx.symm
  have h := two_mul_card_inf_alt_of_neg_one
    (H := centralizer ({π} : Set (Perm (Fin m)))) (s := s) hsign
  rw [nat_card_centralizer_of_mul_self hπ] at h
  simp only [Fintype.card_fin] at h
  have hfk : m - 2 * Multiset.card π.cycleType = Fintype.card {x : Fin m // π x = x} := by
    have hcard := card_fixed_add_two_mul_card_cycleType hπ
    omega
  rw [hfk] at h
  exact h

end CFSG.OddStandard.AltStdSec.SwapPartner
