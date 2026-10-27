module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenC66b
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem core66 (hΩ : HypOmegaGen Ω) : Core66 Ω := by
  intro S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne hAorb hBorb
  by_contra hnc
  obtain ⟨K, hK, J, hJ, hKJ, hAK, hBJ⟩ := hpair A hA B hB hne
  obtain ⟨z, hz⟩ := exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := exists_uniqueInvolution hΩ hJ
  have hzt : z ≠ t := by
    intro hzt
    have hzJ : IsUniqueInvolution J z := by rw [hzt]; exact ht
    exact hnc (commutes_of_twin_of_isPGroup hΩ hK hJ hKJ hz hzJ hAK hBJ
      (hS.to_le (sup_le (hΔS A hA) (hΔS B hB))))
  have c : C66Data Ω S Δ A B K J z t :=
    ⟨hS, hΔS, hΔinv, hcyc, hpair, hA, hB, hAorb, hBorb, hAK, hBJ, ⟨hK, hJ, hz, ht, hzt⟩, hnc⟩
  by_cases hAt : conjSub t A = A
  · exact c.caseI hΩ hAt
  · exact c.caseII hΩ hAt

theorem cyc66_of_core66 (hΩ : HypOmegaGen Ω) (hcore : Core66 Ω) : Cyc66 Ω := by
  have key : ∀ n : ℕ, ∀ S : Subgroup G, Nat.card S = n → IsPGroup 2 S →
      ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) → (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) →
        (∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) →
        (∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J') →
          ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro S hSn hS Δ hΔS hΔinv hcyc hpair A hA B hB hne
    have hlt : ∀ A B : Subgroup G, A ∈ Δ → B ∈ Δ → A ≠ B → A < S := by
      intro A B hA hB hne
      refine lt_of_le_of_ne (hΔS A hA) ?_
      intro hAS
      obtain ⟨J, hJ, J', hJ', hJJ', hAJ, hBJ'⟩ := hpair A hA B hB hne
      have hBA : B ≤ A := hAS ▸ hΔS B hB
      have hBJ : B ≤ J := hBA.trans hAJ
      have hB2 : IsPGroup 2 ↥B := (hS.to_le (hΔS B hB))
      exact hJJ' (eq_of_le_of_le hΩ hJ hJ' hB2 (hcyc B hB).2 hBJ hBJ')
    have hAS := hlt A B hA hB hne
    have hBS := hlt B A hB hA (Ne.symm hne)
    refine hcore S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne ?_ ?_
    · exact orbit_commutes_cyc ih hSn hS hΔinv hcyc hpair hA hAS
    · exact orbit_commutes_cyc ih hSn hS hΔinv hcyc hpair hB hBS
  intro S hS Δ hΔS hΔinv hcyc hpair A hA B hB hne
  exact key _ S rfl hS Δ hΔS hΔinv hcyc hpair A hA B hB hne

theorem cyc66 (hΩ : HypOmegaGen Ω) : Cyc66 Ω :=
  cyc66_of_core66 hΩ (core66 hΩ)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
