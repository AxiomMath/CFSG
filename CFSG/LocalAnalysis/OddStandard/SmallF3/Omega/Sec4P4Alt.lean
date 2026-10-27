module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4P4Lift
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverLift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ} {N : Type*} [Group N]

private theorem carmichaelPerm_apply_of_ne_val (k : CarmichaelIndex n) (q : Fin n)
    (h0 : (q : ℕ) ≠ 0) (h1 : (q : ℕ) ≠ 1) (hk : (q : ℕ) ≠ (k.1 : ℕ)) :
    carmichaelPerm k q = q := by
  rw [carmichaelPerm_apply, if_neg h0, if_neg h1, if_neg fun h => hk (congrArg Fin.val h)]

private theorem carmichaelPerm_mul_apply_of_ne_val (i j : CarmichaelIndex n) (q : Fin n)
    (h0 : (q : ℕ) ≠ 0) (h1 : (q : ℕ) ≠ 1) (hi : (q : ℕ) ≠ (i.1 : ℕ))
    (hj : (q : ℕ) ≠ (j.1 : ℕ)) : (carmichaelPerm i * carmichaelPerm j) q = q := by
  rw [Perm.mul_apply, carmichaelPerm_apply_of_ne_val j q h0 h1 hj,
    carmichaelPerm_apply_of_ne_val i q h0 h1 hi]

theorem sec4P4_exists_fixed_carmichael (hn : 5 ≤ n) (i j : CarmichaelIndex n) :
    ∃ q : Fin n, (carmichaelPerm i * carmichaelPerm j) q = q := by
  by_cases h2 : (2 : ℕ) = (i.1 : ℕ) ∨ (2 : ℕ) = (j.1 : ℕ)
  · by_cases h3 : (3 : ℕ) = (i.1 : ℕ) ∨ (3 : ℕ) = (j.1 : ℕ)
    · refine ⟨⟨4, by omega⟩, ?_⟩
      have h4i : (4 : ℕ) ≠ (i.1 : ℕ) := by
        rcases h2 with h | h <;> rcases h3 with h' | h' <;> omega
      have h4j : (4 : ℕ) ≠ (j.1 : ℕ) := by
        rcases h2 with h | h <;> rcases h3 with h' | h' <;> omega
      exact carmichaelPerm_mul_apply_of_ne_val i j ⟨4, by omega⟩
        (by show (4 : ℕ) ≠ 0; norm_num) (by show (4 : ℕ) ≠ 1; norm_num) h4i h4j
    · simp only [not_or] at h3
      refine ⟨⟨3, by omega⟩, ?_⟩
      exact carmichaelPerm_mul_apply_of_ne_val i j ⟨3, by omega⟩
        (by show (3 : ℕ) ≠ 0; norm_num) (by show (3 : ℕ) ≠ 1; norm_num) h3.1 h3.2
  · simp only [not_or] at h2
    refine ⟨⟨2, by omega⟩, ?_⟩
    exact carmichaelPerm_mul_apply_of_ne_val i j ⟨2, by omega⟩
      (by show (2 : ℕ) ≠ 0; norm_num) (by show (2 : ℕ) ≠ 1; norm_num) h2.1 h2.2

theorem sec4P4_alt_core (hn : 5 ≤ n) (ρ : N →* Perm (Fin n))
    (hρ : ∀ a ∈ alternatingGroup (Fin n), ∃ y : N, ρ y = a) (hC : ρ.ker ≤ Subgroup.center N)
    (h2 : ∀ k ∈ ρ.ker, k ^ 2 = 1) (p : Fin n)
    (hp : ∀ b ∈ alternatingGroup (Fin n), b p = p → b ^ 2 = 1 → ∃ y : N, ρ y = b ∧ y ^ 2 = 1) :
    ∃ σ : alternatingGroup (Fin n) →* N, ∀ a, ρ (σ a) = a := by
  have hlift : ∀ k : CarmichaelIndex n, ∃ y : N, ρ y = carmichaelPerm k ∧ y ^ 3 = 1 := by
    intro k
    obtain ⟨y, hy⟩ := hρ (carmichaelPerm k) (carmichaelPerm_mem k)
    have hperm3 : carmichaelPerm k ^ 3 = 1 := by
      rw [← (carmichaelPerm_isThreeCycle k).orderOf]
      exact pow_orderOf_eq_one _
    have hy3 : ρ y ^ 3 = 1 := by rw [hy, hperm3]
    obtain ⟨z, hzρ, hz3⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.exists_lift_pow_three_eq_one hC
        (sec4P4_isPGroup_ker ρ h2) (y := y) hy3
    exact ⟨z, hzρ.trans hy, hz3⟩
  choose x hxρ hx3 using hlift
  have hxx : ∀ i j : CarmichaelIndex n, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    have ha2 : (carmichaelPerm i * carmichaelPerm j) ^ 2 = 1 := by
      simpa [carmichaelCycle, Subgroup.coe_pow, Subgroup.coe_mul] using
        congrArg Subtype.val (carmichaelCycle_mul_sq i j hij)
    obtain ⟨q, hq⟩ := sec4P4_exists_fixed_carmichael hn i j
    have hcard : 3 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    haveI : MulAction.IsPretransitive (alternatingGroup (Fin n)) (Fin n) :=
      alternatingGroup.isPretransitive_of_three_le_card (Fin n) hcard
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) q p
    have hgp : (g : Perm (Fin n)) q = p := by
      simpa [MulAction.subgroup_smul_def, Perm.smul_def] using hg
    have hgA : (g : Perm (Fin n)) ∈ alternatingGroup (Fin n) := g.2
    have haA : carmichaelPerm i * carmichaelPerm j ∈ alternatingGroup (Fin n) :=
      Subgroup.mul_mem _ (carmichaelPerm_mem i) (carmichaelPerm_mem j)
    have hb : (g : Perm (Fin n)) * (carmichaelPerm i * carmichaelPerm j) *
        (g : Perm (Fin n))⁻¹ ∈ alternatingGroup (Fin n) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA haA) (Subgroup.inv_mem _ hgA)
    have hginv : (g : Perm (Fin n))⁻¹ p = q := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hgp.symm
    have hbp : ((g : Perm (Fin n)) * (carmichaelPerm i * carmichaelPerm j) *
        (g : Perm (Fin n))⁻¹) p = p := by
      rw [Perm.mul_apply, hginv, Perm.mul_apply, hq, hgp]
    have hb2 : ((g : Perm (Fin n)) * (carmichaelPerm i * carmichaelPerm j) *
        (g : Perm (Fin n))⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ha2, mul_one, mul_inv_cancel]
    obtain ⟨y, hyρ, hy2⟩ := hp _ hb hbp hb2
    obtain ⟨w, hw⟩ := hρ (g : Perm (Fin n)) g.2
    have hconj : ρ (w * (x i * x j) * w⁻¹) =
        (g : Perm (Fin n)) * (carmichaelPerm i * carmichaelPerm j) *
          (g : Perm (Fin n))⁻¹ := by
      simp only [map_mul, map_inv, hw, hxρ i, hxρ j]
    exact sec4P4_sq_eq_one_of_map_conj ρ hC h2 (z := x i * x j) (w := w) (y := y)
      (hyρ.trans hconj.symm) hy2
  obtain ⟨σ, hσ⟩ := exists_hom_carmichaelCycle (by omega : 3 ≤ n) x hx3 hxx
  have hsec : ρ.comp σ = (alternatingGroup (Fin n)).subtype :=
    hom_ext_carmichaelCycle (by omega : 3 ≤ n) fun k => by
      rw [MonoidHom.comp_apply, hσ k, hxρ k]
      rfl
  exact ⟨σ, fun a => by simpa using DFunLike.congr_fun hsec a⟩

theorem sec4P4_alt_hom_eq (hn : 3 ≤ n) {G : Type*} [Group G] (π : N →* G)
    (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    {σ₁ σ₂ : alternatingGroup (Fin n) →* N} (h : ∀ a, π (σ₁ a) = π (σ₂ a)) : σ₁ = σ₂ := by
  refine hom_ext_carmichaelCycle hn fun k => ?_
  refine CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq hC
    (sec4P4_isPGroup_ker π h2) ?_ ?_ (h _)
  · rw [← map_pow, carmichaelCycle_pow_three, map_one]
  · rw [← map_pow, carmichaelCycle_pow_three, map_one]

end CFSG.OddStandard.SmallF3.Omega
