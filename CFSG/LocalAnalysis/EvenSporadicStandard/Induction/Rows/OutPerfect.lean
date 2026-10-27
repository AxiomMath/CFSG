module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSOutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSTransport

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {Y Y' : Type} [Group Y] [Group Y'] {LY E : Subgroup Y} {φ : ↥E →* Y'}
  {D : Subgroup Y'} {tY : Y}

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.OutRowModel.perfect_le_of_fields [Finite ↥E]
    (M : OutRowModel LY E φ D tY) {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hu : u ∈ L) (hKL : K ≤ L) (hKcen : u ∈ centralizer (K : Set G))
    (Ψ : ↥L →* Y) (hΨ : Function.Injective Ψ) (hΨL : ∀ x, Ψ x ∈ LY) (hΨu : Ψ ⟨u, hu⟩ = tY)
    (hKperf : Group.IsPerfect K) (hKcard : Nat.card K = Nat.card D) :
    ∀ P : Subgroup G, P ≤ L ⊓ centralizer ({u} : Set G) → Group.IsPerfect ↥P → P ≤ K := by
  have hq := M.quot
  have := hKperf
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hKcen k hk
  have key : ∀ (S : Subgroup G), S ≤ L → (∀ s ∈ S, s * u = u * s) →
      (S.subgroupOf L).map Ψ ≤ E := by
    rintro S hSL hSu _ ⟨s, hs, rfl⟩
    refine (M.E_iff _).2 ⟨hΨL _, ?_⟩
    rw [← hΨu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hSu s (Subgroup.mem_subgroupOf.1 hs))
  let KE : Subgroup ↥E := ((K.subgroupOf L).map Ψ).subgroupOf E
  have hKE : (K.subgroupOf L).map Ψ ≤ E := key K hKL hKu
  have hKEperf : Group.IsPerfect KE := by
    have : Group.IsPerfect (K.subgroupOf L) := isPerfect_subgroupOf_of_le hKL hKperf
    have : Group.IsPerfect ((K.subgroupOf L).map Ψ) := Group.IsPerfect.map _
    exact isPerfect_subgroupOf_of_le hKE inferInstance
  have hKEcard : Nat.card KE = Nat.card D := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv,
      Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
    exact hKcard
  intro P hP hPperf
  have hPL : P ≤ L := fun x hx => (hP hx).1
  have hPu : ∀ s ∈ P, s * u = u * s := fun s hs => mem_centralizer_singleton_iff.1 (hP hs).2
  have hPE : (P.subgroupOf L).map Ψ ≤ E := key P hPL hPu
  let PE : Subgroup ↥E := ((P.subgroupOf L).map Ψ).subgroupOf E
  have hPEperf : Group.IsPerfect PE := by
    have : Group.IsPerfect (P.subgroupOf L) := isPerfect_subgroupOf_of_le hPL hPperf
    have : Group.IsPerfect ((P.subgroupOf L).map Ψ) := Group.IsPerfect.map _
    exact isPerfect_subgroupOf_of_le hPE inferInstance
  have hle : PE ≤ KE := hq.le_of_perfect hKEperf hKEcard hPEperf
  intro x hx
  have hxE : Ψ ⟨x, hPL hx⟩ ∈ E := hPE ⟨⟨x, hPL hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hxPE : (⟨Ψ ⟨x, hPL hx⟩, hxE⟩ : ↥E) ∈ PE :=
    Subgroup.mem_subgroupOf.2 ⟨⟨x, hPL hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_subgroupOf.1 (hle hxPE)
  have : k = ⟨x, hPL hx⟩ := hΨ hkx
  rw [this] at hk
  exact Subgroup.mem_subgroupOf.1 hk

end CFSG.EvenSporadicStandard.Induction
