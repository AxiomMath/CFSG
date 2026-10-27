module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.GSThmB.NFAlt

open Equiv Subgroup
open scoped Pointwise

theorem eq_of_maximal_alternating {n : ℕ} {G H E V : Subgroup (Perm (Fin n))}
    {σ : Perm (Fin n)} (hG2 : IsPGroup 2 G) (hHG : H ≤ G) (hVH : V ≤ H)
    (hGσ : G ≤ centralizer ({σ} : Set (Perm (Fin n))))
    (hVA : V ≤ alternatingGroup (Fin n))
    (hVmax : ∀ Q : Subgroup (Perm (Fin n)), Q ≤ centralizer ({σ} : Set (Perm (Fin n))) ⊓
      alternatingGroup (Fin n) → IsPGroup 2 Q → V ≤ Q → Q = V)
    (hEF : ∀ e ∈ E, ∀ x, σ x = x → e x = x) (hF : ∃ x y : Fin n, x ≠ y ∧ σ x = x ∧ σ y = y)
    (hN : ∀ π ∈ G, (∀ e ∈ E, π * e * π⁻¹ ∈ E) → π ∈ H) : G = H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({σ} : Set (Perm (Fin n))) with hCdef
  set A := alternatingGroup (Fin n) with hAdef
  have hGA : G ⊓ A = V :=
    hVmax _ (inf_le_inf_right _ hGσ) (hG2.to_le inf_le_left) (le_inf (hVH.trans hHG) hVA)
  have hGAH : ∀ g ∈ G, g ∈ A → g ∈ H := fun g hg hgA => hVH (hGA ▸ mem_inf.mpr ⟨hg, hgA⟩)
  have hodd : ∀ τ ∈ G, τ ∉ A → τ ∈ H → G = H := by
    intro τ hτG hτA hτH
    refine le_antisymm (fun g hg => ?_) hHG
    by_cases hgA : g ∈ A
    · exact hGAH g hg hgA
    · have h1 : g * τ⁻¹ ∈ A := by
        rw [Perm.mem_alternatingGroup] at hgA hτA ⊢
        rcases Int.units_eq_one_or (Perm.sign g) with h | h
        · exact absurd h hgA
        rcases Int.units_eq_one_or (Perm.sign τ) with h' | h'
        · exact absurd h' hτA
        rw [Perm.sign_mul, Perm.sign_inv, h, h']
        decide
      have h2 := hGAH _ (G.mul_mem hg (G.inv_mem hτG)) h1
      simpa using H.mul_mem h2 hτH
  by_cases hGA' : G ≤ A
  · exact le_antisymm (fun g hg => hGAH g hg (hGA' hg)) hHG
  rw [IsConcreteLE.not_le_iff_exists] at hGA'
  obtain ⟨g₀, hg₀G, hg₀A⟩ := hGA'
  have hG2' : IsPGroup 2 (G.subgroupOf C) := hG2.comap_subtype
  obtain ⟨S, hGS⟩ := hG2'.exists_le_sylow
  set S' : Subgroup (Perm (Fin n)) := (S : Subgroup ↥C).map C.subtype with hS'def
  have hS'C : S' ≤ C := map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.2.map _
  have hGS' : G ≤ S' := fun g hg => ⟨⟨g, hGσ hg⟩, hGS hg, rfl⟩
  have hS'A : S' ⊓ A = V :=
    hVmax _ (inf_le_inf_right _ hS'C) (hS'2.to_le inf_le_left)
      (le_inf ((hVH.trans hHG).trans hGS') hVA)
  have hS'G : S' = G := by
    refine le_antisymm (fun s hs => ?_) hGS'
    by_cases hsA : s ∈ A
    · exact (hVH.trans hHG) (hS'A ▸ mem_inf.mpr ⟨hs, hsA⟩)
    · have h1 : s * g₀⁻¹ ∈ A := by
        rw [Perm.mem_alternatingGroup] at hsA hg₀A ⊢
        rcases Int.units_eq_one_or (Perm.sign s) with h | h
        · exact absurd h hsA
        rcases Int.units_eq_one_or (Perm.sign g₀) with h' | h'
        · exact absurd h' hg₀A
        rw [Perm.sign_mul, Perm.sign_inv, h, h']
        decide
      have h2 : s * g₀⁻¹ ∈ V := hS'A ▸ mem_inf.mpr ⟨S'.mul_mem hs (S'.inv_mem (hGS' hg₀G)), h1⟩
      simpa using G.mul_mem ((hVH.trans hHG) h2) hg₀G
  obtain ⟨x, y, hxy, hx, hy⟩ := hF
  have htC : swap x y ∈ C := by
    rw [mem_centralizer_singleton_iff]
    have h1 := swap_apply_apply σ x y
    rw [hx, hy] at h1
    calc swap x y * σ = σ * swap x y * σ⁻¹ * σ := by rw [← h1]
      _ = σ * swap x y := by group
  set t : ↥C := ⟨swap x y, htC⟩ with htdef
  have ht2 : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_eq_prime
    · rw [sq]
      exact Subtype.ext (swap_mul_self x y)
    · intro h
      have := congrArg (fun z : ↥C => (z : Perm (Fin n)) x) h
      simp [htdef, swap_apply_left] at this
      exact hxy this.symm
  obtain ⟨P, hP⟩ := ht2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) P S
  have hctS : c * t * c⁻¹ ∈ (S : Subgroup ↥C) := by
    have hsmul : (MulAut.conj c) t ∈ (MulAut.conj c) • (P : Set ↥C) :=
      Set.smul_mem_smul_set (hP (mem_zpowers t))
    have hSset : (MulAut.conj c) • (P : Set ↥C) = (S : Set ↥C) := by
      rw [← Sylow.coe_smul, hc]
    rw [hSset] at hsmul
    exact hsmul
  set τ : Perm (Fin n) := (c : Perm (Fin n)) * swap x y * (c : Perm (Fin n))⁻¹ with hτdef
  have hτG : τ ∈ G := by
    rw [← hS'G]
    exact ⟨_, hctS, rfl⟩
  have hτ : τ = swap ((c : Perm (Fin n)) x) ((c : Perm (Fin n)) y) := (swap_apply_apply _ x y).symm
  have hcx : σ ((c : Perm (Fin n)) x) = (c : Perm (Fin n)) x := by
    have h1 := mem_centralizer_singleton_iff.mp c.2
    have h2 := congrArg (fun z : Perm (Fin n) => z x) h1
    simp only [Perm.mul_apply, hx] at h2
    exact h2.symm
  have hcy : σ ((c : Perm (Fin n)) y) = (c : Perm (Fin n)) y := by
    have h1 := mem_centralizer_singleton_iff.mp c.2
    have h2 := congrArg (fun z : Perm (Fin n) => z y) h1
    simp only [Perm.mul_apply, hy] at h2
    exact h2.symm
  have hτE : ∀ e ∈ E, τ * e * τ⁻¹ ∈ E := by
    intro e he
    have h1 : e * τ * e⁻¹ = τ := by
      rw [hτ, ← swap_apply_apply, hEF e he _ hcx, hEF e he _ hcy]
    have hcomm : e * τ = τ * e := by
      calc e * τ = e * τ * e⁻¹ * e := by group
        _ = τ * e := by rw [h1]
    have h2 : τ * e * τ⁻¹ = e := by
      rw [← hcomm]
      group
    rw [h2]
    exact he
  have hτA : τ ∉ A := by
    rw [hτ, Perm.mem_alternatingGroup, Perm.sign_swap]
    · decide
    · intro h
      exact hxy ((c : Perm (Fin n)).injective h)
  exact hodd τ hτG hτA (hN τ hτG hτE)


end CFSG.ComponentClassification.GSThmB.NFAlt
