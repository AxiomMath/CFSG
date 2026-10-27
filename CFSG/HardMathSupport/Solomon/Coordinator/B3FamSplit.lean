module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def Input14_5Alt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 → ∀ K : Subgroup Y,
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    (∃ (n : ℕ) (hn : 5 ≤ n),
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.alternating n hn).Group)) →
    ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ p} : Set Y) →
        ∀ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Y)) J →
          CFSG.Open.IsQuasisimple ↥J

@[expose] def Input14_5Spor : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 → ∀ K : Subgroup Y,
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    (∃ name : TauCeti.SporadicName,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.sporadic name).Group)) →
    ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ p} : Set Y) →
        ∀ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Y)) J →
          CFSG.Open.IsQuasisimple ↥J

@[expose] def Input14_5Lie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 → ∀ K : Subgroup Y,
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    (∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ p} : Set Y) →
        ∀ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Y)) J →
          CFSG.Open.IsQuasisimple ↥J

theorem input14_5_of_families_of_alt (hA : Input14_5Alt) (hS : Input14_5Spor)
    (hL : Input14_5Lie) : UniquenessMaximal.Input14_5 := by
  intro Y _ _ p hp hp2 K hq hK x hx hnc hxp J hJ
  obtain ⟨hnab, i, ⟨e⟩⟩ := I1420.catalog_of_quasisimple hq hK
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact hA Y p hp hp2 K hq hK ⟨n, hn, ⟨e⟩⟩ x hx hnc hxp J hJ
  | lie idx => exact hL Y p hp hp2 K hq hK ⟨idx, ⟨e⟩⟩ x hx hnc hxp J hJ
  | sporadic name => exact hS Y p hp hp2 K hq hK ⟨name, ⟨e⟩⟩ x hx hnc hxp J hJ

end CFSG.HardMathSupport.Solomon.Coordinator
