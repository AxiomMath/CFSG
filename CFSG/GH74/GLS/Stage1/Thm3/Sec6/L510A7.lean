module

public import CFSG.GH74.GLS.IVK.Lifted.Out

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted
  CFSG.GH74.GLS.Stage1.Thm2.Recip

section A7

variable {Q : Type} [Group Q] [Finite Q]

theorem a7_iface (h2A7 : II4_2A7) (hO : HatOK Q) (h7 : IsDoubleCoverOfAlt Q 7)
    (M : Subgroup (MulAut Q)) (hM : IsPGroup 2 ↥M) (P : Sylow 2 Q)
    (hDM : (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (φ₀ : MulAut Q) (hφ₀M : φ₀ ∈ M) (hφ₀F : IsFAutomorphism Q φ₀) (hφ₀2 : φ₀ * φ₀ = 1)
    (hφ₀1 : φ₀ ≠ 1) :
    ((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ⊔ Subgroup.zpowers φ₀ = M) ∧
    ((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ⊓ Subgroup.zpowers φ₀ = ⊥) ∧
    (∀ φ ∈ M, φ * φ = 1 → φ ≠ 1 → IsFAutomorphism Q φ →
      ∃ d ∈ (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q), φ = d * φ₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, c4, -, -, -⟩ := h2A7 Q h7
  have hInnN : (innOf Q).Normal := innOf_normal Q
  set D : Subgroup (MulAut Q) := (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) with hD
  have hDInn : D ≤ innOf Q := Subgroup.map_le_range _ _
  have hnotInn : ∀ φ : MulAut Q, IsFAutomorphism Q φ → φ ≠ 1 → φ ∉ innOf Q := by
    rintro φ hφ hφ1 ⟨c, hc⟩
    have hcz := dict_inner h2A7 hO.sl2 c (hc ▸ hφ)
    exact hφ1 (hc ▸ conj_eq_one_of_mem_center hcz)
  let f : Q →* ↥(innOf Q) := (MulAut.conj : Q →* MulAut Q).rangeRestrict
  have hf : Function.Surjective f := (MulAut.conj : Q →* MulAut Q).rangeRestrict_surjective
  let P'' : Sylow 2 ↥(innOf Q) := P.mapSurjective hf
  have h3 : (P'' : Subgroup ↥(innOf Q)) = (P : Subgroup Q).map f := Sylow.coe_mapSurjective _ _
  have hDP'' : D = (P'' : Subgroup ↥(innOf Q)).map (innOf Q).subtype := by
    rw [h3, hD, Subgroup.map_map]
    rfl
  have hMinn : M ⊓ innOf Q = D := by
    apply le_antisymm
    · have hp2 : IsPGroup 2 ↥((M ⊓ innOf Q).subgroupOf (innOf Q)) :=
        (hM.to_inf_left).of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right :
          M ⊓ innOf Q ≤ innOf Q)).symm
      have hle : (P'' : Subgroup ↥(innOf Q)) ≤ (M ⊓ innOf Q).subgroupOf (innOf Q) := by
        intro x hx
        have hx1 : ((x : ↥(innOf Q)) : MulAut Q) ∈ D := by
          rw [hDP'']
          exact ⟨x, hx, rfl⟩
        exact Subgroup.mem_subgroupOf.2 ⟨hDM hx1, x.2⟩
      have hEq := P''.is_maximal' hp2 hle
      intro x hx
      have hx' : (⟨x, hx.2⟩ : ↥(innOf Q)) ∈ (M ⊓ innOf Q).subgroupOf (innOf Q) := hx
      rw [hEq] at hx'
      rw [hDP'']
      exact ⟨_, hx', rfl⟩
    · exact le_inf hDM hDInn
  have hrel : (D.subgroupOf M).index = 2 := by
    have h1 : D.relIndex M = (innOf Q).relIndex M := by
      rw [← hMinn, inf_comm, Subgroup.inf_relIndex_right]
    have h2 : (innOf Q).relIndex M ∣ (innOf Q).index := Subgroup.relIndex_dvd_index_of_normal _ _
    rw [c4] at h2
    have h3' : (innOf Q).relIndex M ≠ 1 := by
      intro h
      exact hnotInn φ₀ hφ₀F hφ₀1 (Subgroup.relIndex_eq_one.1 h hφ₀M)
    have h4 := (Nat.dvd_prime Nat.prime_two).1 h2
    show D.relIndex M = 2
    rw [h1]
    exact h4.resolve_left h3'
  have hφ₀D : φ₀ ∉ D := fun hh => hnotInn φ₀ hφ₀F hφ₀1 (hDInn hh)
  have hφ₀inv : φ₀⁻¹ = φ₀ := inv_eq_of_mul_eq_one_right hφ₀2
  have hcos : ∀ m ∈ M, m ∉ D → m * φ₀⁻¹ ∈ D := by
    intro m hm hmD
    have key := Subgroup.mul_mem_iff_of_index_two hrel (a := (⟨m, hm⟩ : M))
      (b := (⟨φ₀⁻¹, M.inv_mem hφ₀M⟩ : M))
    have h1 : (⟨m, hm⟩ : M) ∉ D.subgroupOf M := hmD
    have h2 : (⟨φ₀⁻¹, M.inv_mem hφ₀M⟩ : M) ∉ D.subgroupOf M := fun hh =>
      hφ₀D (by simpa using D.inv_mem (Subgroup.mem_subgroupOf.1 hh))
    exact Subgroup.mem_subgroupOf.1 (key.2 (iff_of_false h1 h2))
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm (sup_le hDM (zpowers_le.2 hφ₀M))
    intro m hm
    by_cases hmD : m ∈ D
    · exact mem_sup_left hmD
    · have h1 := hcos m hm hmD
      have : m = (m * φ₀⁻¹) * φ₀ := by group
      rw [this]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers φ₀))
  · apply le_bot_iff.1
    intro x hx
    obtain ⟨hxD, hxz⟩ := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
    have hφ2' : φ₀ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hφ₀2
    rw [Subgroup.mem_bot]
    subst hk
    rw [zpow_eq_zpow_emod k hφ2'] at hxD ⊢
    rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
    · rw [hk2, zpow_zero]
    · exfalso
      rw [hk2, zpow_one] at hxD
      exact hφ₀D hxD
  · intro φ hφM hφ2 hφ1 hφF
    have hφD : φ ∉ D := fun hh => hnotInn φ hφF hφ1 (hDInn hh)
    refine ⟨φ * φ₀⁻¹, hcos φ hφM hφD, ?_⟩
    group

end A7

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L510
