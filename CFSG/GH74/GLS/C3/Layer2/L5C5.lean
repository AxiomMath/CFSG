module

public import CFSG.GH74.GLS.C3.Layer2.L5C5d

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem rec2
    {S : Type} [Group S] [Finite S] (κ : ↥Sh0 →* S) (hκ : Function.Injective κ)
    (hidx : κ.range.index = 2)
    (hmove : ∀ s : S, (∀ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 →
        ∃ r' : ↥Sh0, (r' : Perm (Fin 16)) ∈ RsubP0 ∧ s * κ r * s⁻¹ = κ r') → s ∈ κ.range) :
    ∃ (ty : Fin 4) (ψ : S ≃* Sh2 ty), ∀ g, ψ (κ g) = inc ty g := by
  have hne : ∃ b : S, b ∉ κ.range := by
    by_contra h
    have h' : ∀ b : S, b ∈ κ.range := fun b => by_contra fun hb => h ⟨b, hb⟩
    rw [(Subgroup.eq_top_iff' _).2 h', Subgroup.index_top] at hidx
    omega
  obtain ⟨b, hb⟩ := hne
  have hN : κ.range.Normal := Subgroup.normal_of_index_eq_two hidx
  let e₁ : ↥Sh0 ≃* κ.range := MonoidHom.ofInjective hκ
  let γ : ↥Sh0 ≃* ↥Sh0 := (e₁.trans (MulAut.conjNormal b)).trans e₁.symm
  have hγ : ∀ h, κ (γ h) = b * κ h * b⁻¹ := by
    intro h
    show κ (e₁.symm (MulAut.conjNormal b (e₁ h))) = _
    rw [MonoidHom.apply_ofInjective_symm hκ, MulAut.conjNormal_apply]
    rfl
  obtain ⟨u, hu⟩ := Subgroup.mul_self_mem_of_index_two hidx b
  have hsq : ∀ h, γ (γ h) = u * h * u⁻¹ := by
    intro h
    apply hκ
    rw [hγ, hγ, map_mul, map_mul, map_inv, hu]
    group
  have hfix : γ u = u := by
    apply hκ
    rw [hγ, hu]
    group
  have hmv : ∃ r : ↥Sh0, (r : Perm (Fin 16)) ∈ RsubP0 ∧ (γ r : Perm (Fin 16)) ∉ RsubP0 := by
    by_contra hcon
    apply hb
    apply hmove b
    intro r hr
    refine ⟨γ r, ?_, (hγ r).symm⟩
    by_contra hn
    exact hcon ⟨r, hr, hn⟩
  obtain ⟨m, h₀, hγ', hu'⟩ := classify_sound γ u hsq hfix hmv
  have hb' : κ h₀ * b ∉ κ.range := by
    intro h
    apply hb
    have := mul_mem (inv_mem (⟨h₀, rfl⟩ : κ h₀ ∈ κ.range)) h
    simpa using this
  have hα : ∀ h, κ ((ext2Data m).α h) = κ h₀ * b * κ h * (κ h₀ * b)⁻¹ := by
    intro h
    show κ (gam m h) = _
    rw [← hγ' h, map_mul, map_mul, map_inv, hγ]
    group
  have hu2 : κ (ext2Data m).u = κ h₀ * b * (κ h₀ * b) := by
    show κ (dec0 (ssData.getD m.val 0)) = _
    rw [← hu', map_mul, map_mul, hγ, hu]
    group
  obtain ⟨ψ, hψ⟩ := Ext2.recognize (ext2Data m) κ hκ hidx (κ h₀ * b) hb' hα hu2
  exact ⟨m, ψ, hψ⟩

end CFSG.GH74.GLS.C3.Layer2.L5
