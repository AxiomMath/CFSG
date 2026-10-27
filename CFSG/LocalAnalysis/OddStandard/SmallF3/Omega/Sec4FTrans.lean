module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4F_exists_alt (i j : Fin 7) : ∃ σ ∈ alternatingGroup (Fin 7), σ i = j := by
  by_cases hij : i = j
  · exact ⟨1, one_mem _, by simp [hij]⟩
  · have hex : ∀ i j : Fin 7, ∃ k l : Fin 7, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l := by
      decide +kernel
    obtain ⟨k, l, hki, hkj, hli, hlj, hkl⟩ := hex i j
    refine ⟨Equiv.swap i j * Equiv.swap k l, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
        Equiv.Perm.sign_swap hkl]
      decide
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki.symm hli.symm,
        Equiv.swap_apply_left]

theorem Sec4FSetup.exists_realizes_alt (h : Sec4FSetup t L S z A B φ) {σ : Equiv.Perm (Fin 7)}
    (hσ : σ ∈ alternatingGroup (Fin 7)) :
    ∃ m ∈ normalizer (A : Set G), Sec4MRealizes t φ m (Equiv.optionCongr σ) := by
  obtain ⟨u, ⟨huL, huB⟩, huv⟩ := h.data.bdata.perm.2.2.2.2 σ hσ
  have hfwd : ∀ u : G, u ∈ L → u ∈ normalizer (B : Set G) → ∀ x ∈ A, u * x * u⁻¹ ∈ A := by
    intro u huL huB x hx
    obtain ⟨b, hb, hxb⟩ := h.mem_A_cases hx
    have hub : u * b * u⁻¹ ∈ B := (Subgroup.mem_set_normalizer_iff.mp huB b).mp hb
    have hut : u * t * u⁻¹ = t := by
      rw [show u * t = t * u from (h.t_cent_L huL).symm]
      group
    rcases hxb with rfl | rfl
    · exact h.B_le_A hub
    · have hsplit : u * (b * t) * u⁻¹ = (u * b * u⁻¹) * (u * t * u⁻¹) := by group
      rw [hsplit, hut]
      exact A.mul_mem (h.B_le_A hub) h.t_mem_A
  have huN : u ∈ normalizer (A : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    refine ⟨hfwd u huL huB x, fun hx => ?_⟩
    have h2 := hfwd u⁻¹ (L.inv_mem huL) ((normalizer (B : Set G)).inv_mem huB) _ hx
    have h3 : u⁻¹ * (u * x * u⁻¹) * u = x := by group
    rwa [inv_inv, h3] at h2
  refine ⟨u, huN, ?_⟩
  have hconj_t : u * t * u⁻¹ = t := by
    rw [show u * t = t * u from (h.t_cent_L huL).symm]
    group
  intro p
  calc u * sec4MPt t φ p * u⁻¹
      = (u * t * u⁻¹) * (u * φ (sec4MV p) * u⁻¹) := by
        rw [sec4MPt]; group
    _ = t * (u * φ (sec4MV p) * u⁻¹) := by rw [hconj_t]
    _ = t * φ (permVec σ (sec4MV p)) := by rw [huv (sec4MV p) (sec4MV_even p)]
    _ = sec4MPt t φ (Equiv.optionCongr σ p) := by rw [permVec_sec4MV]; rfl

theorem Sec4FSetup.exists_move_pt (h : Sec4FSetup t L S z A B φ) (r : Option (Fin 7)) :
    ∃ (m : G) (ν : Equiv.Perm (Option (Fin 7))), m ∈ normalizer (A : Set G) ∧
      Sec4MRealizes t φ m ν ∧ ν none = r := by
  obtain ⟨n, hnN, hnpt⟩ := h.exists_conj_pt r
  obtain ⟨ν, hν⟩ := h.exists_realizes hnN
  refine ⟨n, ν, hnN, hν, ?_⟩
  have h1 := hν none
  have h2 : sec4MPt t φ (ν none) = sec4MPt t φ r := by rw [← h1, hnpt, h.pt_none]
  exact sec4MPt_injective h.data h2

theorem Sec4FSetup.exists_two_trans (h : Sec4FSetup t L S z A B φ)
    {p q p' q' : Option (Fin 7)} (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ (m : G) (ν : Equiv.Perm (Option (Fin 7))), m ∈ normalizer (A : Set G) ∧
      Sec4MRealizes t φ m ν ∧ ν p' = p ∧ ν q' = q := by
  obtain ⟨m₁, ν₁, hm₁, hν₁, hν₁0⟩ := h.exists_move_pt p'
  obtain ⟨m₂, ν₂, hm₂, hν₂, hν₂0⟩ := h.exists_move_pt p
  have hinv1 : ν₁⁻¹ p' = none := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact hν₁0.symm
  have hinv2 : ν₂⁻¹ p = none := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact hν₂0.symm
  have hq1 : ν₁⁻¹ q' ≠ none := by
    intro h0
    apply hpq'
    rw [← hinv1] at h0
    exact (ν₁⁻¹).injective h0.symm
  have hq2 : ν₂⁻¹ q ≠ none := by
    intro h0
    apply hpq
    rw [← hinv2] at h0
    exact (ν₂⁻¹).injective h0.symm
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hq1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hq2
  obtain ⟨σ, hσ, hσab⟩ := sec4F_exists_alt a b
  obtain ⟨m₃, hm₃, hν₃⟩ := h.exists_realizes_alt hσ
  refine ⟨m₂ * m₃ * m₁⁻¹, ν₂ * Equiv.optionCongr σ * ν₁⁻¹,
    (normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).mul_mem hm₂ hm₃)
      ((normalizer (A : Set G)).inv_mem hm₁),
    Sec4MRealizes.mul (Sec4MRealizes.mul hν₂ hν₃) (Sec4MRealizes.inv hν₁), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv1]
    simpa using hν₂0
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha]
    have hb' : ν₂ (some b) = q := by
      rw [← hb]; simp
    simpa [hσab] using hb'

end CFSG.OddStandard.SmallF3.Omega
