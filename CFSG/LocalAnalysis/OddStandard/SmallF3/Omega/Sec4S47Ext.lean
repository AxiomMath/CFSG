module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4P4Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm

private abbrev s47e : Option (Fin 7) ≃ Fin 8 := (finSuccEquiv 7).symm

private lemma s47e_none : s47e none = (0 : Fin 8) := finSuccEquiv_symm_none

private lemma sec4S47_alt_le_permCongr {N : Type*} [Group N] (ρ : N →* Perm (Option (Fin 7)))
    (hA : alternatingGroup (Option (Fin 7)) ≤ ρ.range) :
    alternatingGroup (Fin 8) ≤ (s47e.permCongrHom.toMonoidHom.comp ρ).range := by
  intro a ha
  have ha' : s47e.permCongrHom.symm a ∈ alternatingGroup (Option (Fin 7)) := by
    rw [Equiv.Perm.mem_alternatingGroup] at ha ⊢
    rw [Equiv.permCongrHom_symm]
    change Equiv.Perm.sign (s47e.symm.permCongr a) = 1
    rw [Equiv.Perm.sign_permCongr]
    exact ha
  obtain ⟨y, hy⟩ := hA ha'
  exact ⟨y, by
    show s47e.permCongrHom (ρ y) = a
    rw [hy, MulEquiv.apply_symm_apply]⟩

private lemma sec4S47_lift_permCongr {N : Type*} [Group N]
    (ρ : N →* Perm (Option (Fin 7)))
    (hlift : ∀ b ∈ ρ.range, b none = none → b ^ 2 = 1 → ∃ y : N, ρ y = b ∧ y ^ 2 = 1) :
    ∀ b ∈ (s47e.permCongrHom.toMonoidHom.comp ρ).range, b 0 = 0 → b ^ 2 = 1 →
      ∃ y : N, (s47e.permCongrHom.toMonoidHom.comp ρ) y = b ∧ y ^ 2 = 1 := by
  intro b hb hb0 hb2
  have hb' : s47e.permCongrHom.symm b ∈ ρ.range := by
    obtain ⟨y, hy⟩ := hb
    refine ⟨y, ?_⟩
    rw [← hy]
    exact (MulEquiv.symm_apply_apply s47e.permCongrHom (ρ y)).symm
  have hb'0 : s47e.permCongrHom.symm b none = none := by
    change s47e.symm.permCongr b none = none
    rw [Equiv.permCongr_apply, Equiv.symm_symm, s47e_none, hb0]
    exact finSuccEquiv_zero
  have hb'2 : (s47e.permCongrHom.symm b) ^ 2 = 1 := by
    rw [← map_pow, hb2, map_one]
  obtain ⟨y, hy, hy2⟩ := hlift _ hb' hb'0 hb'2
  exact ⟨y, by
    show s47e.permCongrHom (ρ y) = b
    rw [hy, MulEquiv.apply_symm_apply], hy2⟩

private theorem sec4S47_compl_fin8 {N : Type*} [Group N] (π : N →* Perm (Fin 8))
    (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    (hA : alternatingGroup (Fin 8) ≤ π.range)
    (hlift : ∀ b ∈ π.range, b 0 = 0 → b ^ 2 = 1 → ∃ y : N, π y = b ∧ y ^ 2 = 1) :
    ∃ K : Subgroup N, K ⊓ π.ker = ⊥ ∧ K ⊔ π.ker = ⊤ := by
  obtain ⟨σ, hσ⟩ := sec4P4_alt_core (by norm_num : 5 ≤ 8) π
    (fun a ha => hA ha) hC h2 0 (fun b hb hb0 hb2 => hlift b (hA hb) hb0 hb2)
  by_cases hodd : ∃ y : N, Perm.sign (π y) = -1
  · obtain ⟨y₀, hy₀⟩ := hodd
    set t : Perm (Fin 8) := Equiv.swap 1 2 with ht_def
    have ht_mem : t ∈ π.range := by
      have hb₀ : π y₀ ∈ π.range := ⟨y₀, rfl⟩
      have hbt : (π y₀)⁻¹ * t ∈ alternatingGroup (Fin 8) := by
        rw [Equiv.Perm.mem_alternatingGroup, ht_def]
        simp [hy₀, Int.units_mul_self]
      have hprod := Subgroup.mul_mem _ hb₀ (hA hbt)
      simpa [mul_inv_cancel_left] using hprod
    have ht0 : t 0 = 0 := by
      rw [ht_def]
      exact Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 8) ≠ 1)
        (by decide : (0 : Fin 8) ≠ 2)
    have ht2 : t ^ 2 = 1 := by
      rw [ht_def, pow_two]
      exact Equiv.swap_mul_self 1 2
    obtain ⟨u, hu, hu2⟩ := hlift t ht_mem ht0 ht2
    have hsign : Perm.sign (π u) = -1 := by
      rw [hu, ht_def]
      exact Equiv.Perm.sign_swap (by decide : (1 : Fin 8) ≠ 2)
    exact ⟨σ.range ⊔ Subgroup.zpowers u,
      sec4P4_perm_compl_of (by norm_num : 3 ≤ 8) π hC h2 hσ hsign hu2⟩
  · have hle : π.range ≤ alternatingGroup (Fin 8) := by
      intro a ha
      rw [Equiv.Perm.mem_alternatingGroup]
      rcases Int.units_eq_one_or (Perm.sign a) with hs | hs
      · exact hs
      · exfalso
        obtain ⟨y, rfl⟩ := ha
        exact hodd ⟨y, hs⟩
    let π' : N →* alternatingGroup (Fin 8) := π.codRestrict _ (fun y => hle ⟨y, rfl⟩)
    have hσ' : ∀ a, π' (σ a) = a := by
      intro a
      apply Subtype.ext
      show π (σ a) = (a : Perm (Fin 8))
      rw [hσ a]
    have hker : π'.ker = π.ker := MonoidHom.ker_codRestrict π _ _
    obtain ⟨h1, h2'⟩ := sec4P4_compl_of_section π' hσ'
    exact ⟨σ.range, by rw [← hker]; exact h1, by rw [← hker]; exact h2'⟩

theorem sec4S47_compl {N : Type*} [Group N] (ρ : N →* Perm (Option (Fin 7)))
    (hC : ρ.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ ρ.ker, k ^ 2 = 1)
    (hA : alternatingGroup (Option (Fin 7)) ≤ ρ.range)
    (hlift : ∀ b ∈ ρ.range, b none = none → b ^ 2 = 1 → ∃ y : N, ρ y = b ∧ y ^ 2 = 1) :
    ∃ K : Subgroup N, K ⊓ ρ.ker = ⊥ ∧ K ⊔ ρ.ker = ⊤ := by
  have hker : (s47e.permCongrHom.toMonoidHom.comp ρ).ker = ρ.ker :=
    MonoidHom.ker_comp_of_injective ρ s47e.permCongrHom.toMonoidHom
      s47e.permCongrHom.injective
  obtain ⟨K, hK⟩ := sec4S47_compl_fin8 (s47e.permCongrHom.toMonoidHom.comp ρ)
    (by rw [hker]; exact hC) (by rw [hker]; exact h2)
    (sec4S47_alt_le_permCongr ρ hA) (sec4S47_lift_permCongr ρ hlift)
  refine ⟨K, ?_, ?_⟩
  · rw [← hker]; exact hK.1
  · rw [← hker]; exact hK.2

end CFSG.OddStandard.SmallF3.Omega
