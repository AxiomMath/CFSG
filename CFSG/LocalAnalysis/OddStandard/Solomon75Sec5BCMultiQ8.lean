module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Q8

variable {n : ℕ}

private theorem bcdQ8_apply_mem_support_iff {τ g : Perm (Fin n)} (hg : g * τ = τ * g)
    (x : Fin n) : g x ∈ τ.support ↔ x ∈ τ.support := by
  have h : τ (g x) = g (τ x) := by
    simpa using (congrArg (fun h : Perm (Fin n) => h x) hg).symm
  simp only [Equiv.Perm.mem_support, h]
  exact not_congr g.injective.eq_iff

theorem q8_support_card_eq (hn : n < 16) {τ : Perm (Fin n)} {W : Subgroup (Perm (Fin n))}
    (hτ : τ ≠ 1) (hW8 : Nat.card ↥W = 8) (hWτ : ∀ g ∈ W, g ≠ 1 → τ ∈ zpowers g)
    (hWc : ∀ g ∈ W, g * τ = τ * g) : τ.support.card = 8 := by
  have h8 := eight_dvd_card_support hτ hW8 hWτ hWc
  have hpos : 0 < τ.support.card := by
    rw [Finset.card_pos, Finset.nonempty_iff_ne_empty, Ne, Equiv.Perm.support_eq_empty_iff]
    exact hτ
  have hle : τ.support.card ≤ n := by simpa using Finset.card_le_univ τ.support
  obtain ⟨k, hk⟩ := h8
  omega

theorem eq_of_commute_of_fixCount (hn : n < 16) {τ σ : Perm (Fin n)}
    {W : Subgroup (Perm (Fin n))} (hτ2 : τ * τ = 1) (hτW : τ ∈ W) (h8 : τ.support.card = 8)
    (hW8 : Nat.card ↥W = 8) (hWτ : ∀ g ∈ W, g ≠ 1 → τ ∈ zpowers g) (hσ2 : σ * σ = 1)
    (hσW : ∀ g ∈ W, g * σ = σ * g) (hfix : fixCount σ = n - 8) : σ = τ := by
  classical
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h] at h8
    simp at h8
  have hn8 : 8 ≤ n := by
    have := Finset.card_le_univ τ.support
    simp only [Fintype.card_fin] at this
    omega
  have hWc : ∀ g ∈ W, g * τ = τ * g := by
    intro g hg
    by_cases hg1 : g = 1
    · simp [hg1]
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hWτ g hg hg1)
      rw [← hj]
      exact ((Commute.refl g).zpow_right j).eq
  have hfree : ∀ g ∈ W, ∀ p ∈ τ.support, g p = p → g = 1 := by
    intro g hg p hp hgp
    by_contra hg1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hWτ g hg hg1)
    have h2 : (g ^ j) p = p := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hgp j
    rw [hj] at h2
    exact (Equiv.Perm.mem_support.1 hp) h2
  have hreg : ∀ p ∈ τ.support, ∀ q ∈ τ.support, ∃ w ∈ W, w p = q := by
    intro p hp q hq
    let f : W → {x // x ∈ τ.support} := fun g =>
      ⟨(g : Perm (Fin n)) p, (bcdQ8_apply_mem_support_iff (hWc g g.2) p).2 hp⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have hab' : (a : Perm (Fin n)) p = (b : Perm (Fin n)) p := congrArg Subtype.val hab
      have h1 : ((b : Perm (Fin n))⁻¹ * (a : Perm (Fin n))) p = p := by
        rw [Perm.mul_apply, hab']
        simp
      have hbW : ((b : Perm (Fin n))⁻¹ * (a : Perm (Fin n))) ∈ W :=
        W.mul_mem (W.inv_mem b.2) a.2
      have h2 := hfree _ hbW p hp h1
      exact Subtype.ext (inv_mul_eq_one.1 h2).symm
    have hcard : Nat.card {x // x ∈ τ.support} ≤ Nat.card W := by
      rw [hW8, Nat.card_eq_fintype_card, Fintype.card_coe, h8]
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard
    obtain ⟨g, hg⟩ := hbij.2 ⟨q, hq⟩
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  have hσc : σ * τ = τ * σ := (hσW τ hτW).symm
  have hσmem : ∀ x, σ x ∈ τ.support ↔ x ∈ τ.support := bcdQ8_apply_mem_support_iff hσc
  have hne : τ.support.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨w₀, hw₀W, hw₀⟩ := hreg p₀ hp₀ (σ p₀) ((hσmem p₀).2 hp₀)
  have hσw : ∀ w ∈ W, σ (w p₀) = (w * w₀) p₀ := by
    intro w hw
    have h1 : σ (w p₀) = w (σ p₀) := by
      have := congrArg (fun h : Perm (Fin n) => h p₀) (hσW w hw)
      simpa [Perm.mul_apply] using this.symm
    rw [h1, ← hw₀]
    rfl
  have hw₀sq : w₀ * w₀ = 1 := by
    have h1 : σ (σ p₀) = p₀ := by
      have := congrArg (fun h : Perm (Fin n) => h p₀) hσ2
      simpa [Perm.mul_apply] using this
    have h2 : (w₀ * w₀) p₀ = p₀ := by
      rw [← hσw w₀ hw₀W, hw₀, h1]
    exact hfree _ (W.mul_mem hw₀W hw₀W) p₀ hp₀ h2
  have hw₀cases : w₀ = 1 ∨ w₀ = τ := by
    by_cases h1 : w₀ = 1
    · exact Or.inl h1
    · right
      have hw2 : orderOf w₀ = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hw₀sq) h1
      rcases zpowers_eq_of_orderOf_two hw2 τ (hWτ w₀ hw₀W h1) with h3 | h3
      · exact absurd h3 hτ1
      · exact h3.symm
  have hfixCount : fixCount σ = (Finset.univ.filter fun i => σ i = i).card := rfl
  rcases hw₀cases with h1 | h1
  ·
    exfalso
    have hsub : τ.support ⊆ Finset.univ.filter fun i => σ i = i := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hreg p₀ hp₀ q hq
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hσw w hw, h1]
      simp
    have := Finset.card_le_card hsub
    rw [h8, ← hfixCount, hfix] at this
    omega
  ·
    have hστ : ∀ q ∈ τ.support, σ q = τ q := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := hreg p₀ hp₀ q hq
      rw [hσw w hw, h1]
      have := congrArg (fun h : Perm (Fin n) => h p₀) (hWc w hw)
      simpa [Perm.mul_apply] using this
    have hsub : (Finset.univ.filter fun i => σ i = i) ⊆ τ.supportᶜ := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_compl]
      intro hxs
      have := hστ x hxs
      rw [hx.2] at this
      exact (Equiv.Perm.mem_support.1 hxs) this.symm
    have hcard : (τ.supportᶜ).card ≤ (Finset.univ.filter fun i => σ i = i).card := by
      rw [Finset.card_compl, ← hfixCount, hfix, h8]
      simp
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ τ.support
    · exact hστ x hx
    · have hx' : x ∈ (Finset.univ.filter fun i => σ i = i) := by
        rw [heq, Finset.mem_compl]
        exact hx
      rw [Finset.mem_filter] at hx'
      rw [hx'.2]
      exact (Equiv.Perm.notMem_support.1 hx).symm

end Q8

section PermData

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem q8_perm_data_range (hn : 8 ≤ n) {B : Subgroup X} (M : AhatModel X n B) {Q : Subgroup X}
    (hQB : Q ≤ normalizer (B : Set X)) (hQ8 : Nat.card ↥Q = 8) {u : X} (huQ : u ∈ Q)
    (hQpow : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) (hu2 : u * u = 1)
    (hτ : M.perm u (hQB huQ) ≠ 1) :
    ∃ W : Subgroup (Perm (Fin n)), Nat.card ↥W = 8 ∧ M.perm u (hQB huQ) ∈ W ∧
      (∀ g ∈ W, g ≠ 1 → M.perm u (hQB huQ) ∈ zpowers g) ∧
      (∀ g ∈ W, g * M.perm u (hQB huQ) = M.perm u (hQB huQ) * g) ∧
      (∀ (q : X) (hq : q ∈ Q), M.perm q (hQB hq) ∈ W) ∧
      ∀ g ∈ W, ∃ (q : X) (hq : q ∈ Q), M.perm q (hQB hq) = g := by
  classical
  let ψ : ↥Q →* Perm (Fin n) := (M.permHom hn).comp (Subgroup.inclusion hQB)
  have hψ : ∀ q : ↥Q, ψ q = M.perm (q : X) (hQB q.2) := fun q => rfl
  have hpow : ∀ q : ↥Q, q ≠ 1 → ∃ j : ℤ, q ^ j = ⟨u, huQ⟩ := by
    intro q hq
    have hq1 : (q : X) ≠ 1 := fun h => hq (Subtype.ext h)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hQpow (q : X) q.2 hq1)
    refine ⟨j, Subtype.ext ?_⟩
    simpa using hj
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    by_contra hq1
    obtain ⟨j, hj⟩ := hpow q hq1
    apply hτ
    have : ψ ⟨u, huQ⟩ = 1 := by
      rw [← hj, map_zpow, hq, one_zpow]
    simpa [hψ] using this
  refine ⟨ψ.range, ?_, ⟨⟨u, huQ⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hQ8]
  · rintro g ⟨q, rfl⟩ hg1
    have hq1 : q ≠ 1 := fun h => hg1 (by rw [h, map_one])
    obtain ⟨j, hj⟩ := hpow q hq1
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [← map_zpow, hj]
    rfl
  · rintro g ⟨q, rfl⟩
    by_cases hq1 : q = 1
    · simp [hq1]
    · obtain ⟨j, hj⟩ := hpow q hq1
      have : ψ q * ψ ⟨u, huQ⟩ = ψ ⟨u, huQ⟩ * ψ q := by
        rw [← hj, ← map_mul, ← map_mul]
        exact congrArg ψ ((Commute.refl q).zpow_right j).eq
      simpa [hψ] using this
  · intro q hq
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro g ⟨q, rfl⟩
    exact ⟨(q : X), q.2, rfl⟩

theorem q8_perm_data (hn : 8 ≤ n) {B : Subgroup X} (M : AhatModel X n B) {Q : Subgroup X}
    (hQB : Q ≤ normalizer (B : Set X)) (hQ8 : Nat.card ↥Q = 8) {u : X} (huQ : u ∈ Q)
    (hQpow : ∀ q ∈ Q, q ≠ 1 → u ∈ zpowers q) (hu2 : u * u = 1)
    (hτ : M.perm u (hQB huQ) ≠ 1) :
    ∃ W : Subgroup (Perm (Fin n)), Nat.card ↥W = 8 ∧ M.perm u (hQB huQ) ∈ W ∧
      (∀ g ∈ W, g ≠ 1 → M.perm u (hQB huQ) ∈ zpowers g) ∧
      (∀ g ∈ W, g * M.perm u (hQB huQ) = M.perm u (hQB huQ) * g) ∧
      ∀ (q : X) (hq : q ∈ Q), M.perm q (hQB hq) ∈ W := by
  obtain ⟨W, h1, h2, h3, h4, h5, -⟩ := q8_perm_data_range hn M hQB hQ8 huQ hQpow hu2 hτ
  exact ⟨W, h1, h2, h3, h4, h5⟩

end PermData

end CFSG.OddStandard.Solomon75
