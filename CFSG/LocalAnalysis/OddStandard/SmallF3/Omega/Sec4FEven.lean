module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.even_or_outer (h : Sec4FSetup t L S z A B φ) {s : G}
    (hs : ∃ g : G, s = g⁻¹ * t * g) (hsN : s ∈ normalizer (A : Set G)) (hst : s * t = t * s) :
    (∃ σ : Equiv.Perm (Option (Fin 7)), Sec4MRealizes t φ s σ ∧ Equiv.Perm.sign σ = 1) ∨
      InducesTypeSome L s 7 1 6 1 := by
  by_cases hse : s = t
  · subst hse
    exact Or.inl ⟨1, h.realizes_of_mem_A h.t_mem_A, by simp⟩
  have hsc : s ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  rcases sec4_conj_tri h.inputs.h36 h.inputs.h39 h.inputs.h42 h.inputs.h43 h.inputs.hf43c
    h.inputs.hf214 h.inputs.hin6 h.inputs.hk6 h.ctx hs hsc hse with
    hz | ⟨u', hu'L, -, -, hsu'⟩ | hs6
  · exact absurd hz h.not_tz
  · left
    have hu'_eq_ts : u' = t * s := by
      rw [hsu', ← mul_assoc, h.t_sq, one_mul]
    have htN : t ∈ normalizer (A : Set G) := Subgroup.le_normalizer h.t_mem_A
    have hu'N : u' ∈ normalizer (A : Set G) := by
      rw [hu'_eq_ts]
      exact (normalizer (A : Set G)).mul_mem htN hsN
    have hu'Lnorm : u' ∈ normalizer (L : Set G) := Subgroup.le_normalizer hu'L
    have hu'B : u' ∈ normalizer (B : Set G) := by
      rw [← h.data.B_eq, Subgroup.mem_set_normalizer_iff]
      intro x
      rw [SetLike.mem_coe, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_set_normalizer_iff.mp hu'N x)
        (Subgroup.mem_set_normalizer_iff.mp hu'Lnorm x)
    obtain ⟨σ', hσ'mem, hσ'v⟩ := h.data.bdata.perm.2.2.2.1 u' ⟨hu'L, hu'B⟩
    have hconj_t : u' * t * u'⁻¹ = t := by
      rw [← h.t_cent_L hu'L]; group
    have hu'real : Sec4MRealizes t φ u' (Equiv.optionCongr σ') := by
      intro p
      calc u' * sec4MPt t φ p * u'⁻¹
          = (u' * t * u'⁻¹) * (u' * φ (sec4MV p) * u'⁻¹) := by
            rw [sec4MPt]; group
        _ = t * (u' * φ (sec4MV p) * u'⁻¹) := by rw [hconj_t]
        _ = t * φ (permVec σ' (sec4MV p)) := by rw [hσ'v (sec4MV p) (sec4MV_even p)]
        _ = sec4MPt t φ (Equiv.optionCongr σ' p) := by rw [permVec_sec4MV]; rfl
    refine ⟨Equiv.optionCongr σ', ?_, ?_⟩
    · rw [hsu']
      simpa using Sec4MRealizes.mul (h.realizes_of_mem_A h.t_mem_A) hu'real
    · rw [Equiv.optionCongr_sign, Equiv.Perm.mem_alternatingGroup.mp hσ'mem]
  · exact Or.inr hs6

theorem Sec4FSetup.outer_of_odd (h : Sec4FSetup t L S z A B φ) {s : G}
    (hs : ∃ g : G, s = g⁻¹ * t * g) (hsN : s ∈ normalizer (A : Set G)) (hst : s * t = t * s)
    {σ : Equiv.Perm (Option (Fin 7))} (hσ : Sec4MRealizes t φ s σ)
    (hodd : Equiv.Perm.sign σ = -1) : InducesTypeSome L s 7 1 6 1 := by
  rcases h.even_or_outer hs hsN hst with ⟨σ', hσ', hsign⟩ | h6
  · exfalso
    have hσσ : σ = σ' := Sec4MRealizes.unique h.pt_injective hσ hσ'
    rw [hσσ, hsign] at hodd
    exact absurd hodd (by decide)
  · exact h6

theorem Sec4FSetup.exists_move_fixed (h : Sec4FSetup t L S z A B φ) {y : G}
    {σ : Equiv.Perm (Option (Fin 7))} (hσ : Sec4MRealizes t φ y σ) {r : Option (Fin 7)}
    (hr : σ r = r) :
    ∃ (m : G) (ν : Equiv.Perm (Option (Fin 7))), m ∈ normalizer (A : Set G) ∧
      Sec4MRealizes t φ m ν ∧ ν none = r ∧ (m⁻¹ * y * m) * t = t * (m⁻¹ * y * m) ∧
        Sec4MRealizes t φ (m⁻¹ * y * m) (ν⁻¹ * σ * ν) := by
  obtain ⟨n, hnN, hnpt⟩ := h.exists_conj_pt r
  obtain ⟨ν, hν⟩ := h.exists_realizes hnN
  refine ⟨n, ν, hnN, hν, ?_, ?_, ?_⟩
  · have h1 := hν none
    have h2 : sec4MPt t φ (ν none) = sec4MPt t φ r := by
      rw [← h1, hnpt, h.pt_none]
    exact sec4MPt_injective h.data h2
  · have h1 : y * sec4MPt t φ r * y⁻¹ = sec4MPt t φ r := by rw [hσ r, hr]
    rw [hnpt] at h1
    have key : (n⁻¹ * y * n) * t * (n⁻¹ * y * n)⁻¹ = t := by
      calc (n⁻¹ * y * n) * t * (n⁻¹ * y * n)⁻¹
          = n⁻¹ * (y * (n * t * n⁻¹) * y⁻¹) * n := by group
        _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [h1]
        _ = t := by group
    calc (n⁻¹ * y * n) * t
        = ((n⁻¹ * y * n) * t * (n⁻¹ * y * n)⁻¹) * (n⁻¹ * y * n) := by group
      _ = t * (n⁻¹ * y * n) := by rw [key]
  · exact Sec4MRealizes.mul (Sec4MRealizes.mul (Sec4MRealizes.inv hν) hσ) hν

end CFSG.OddStandard.SmallF3.Omega
