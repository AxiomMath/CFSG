module

public import CFSG.LocalAnalysis.QuasithinUnique.ONanAction

public section

namespace CFSG.QuasithinUnique.ONan

open Module
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X R : Subgroup (V ≃ₗ[ZMod 2] V)} {A C : Submodule (ZMod 2) V}

theorem eq_of_smul_eq (S : Setting X R A C) (hfin : finrank (ZMod 2) A = finrank (ZMod 2) C)
    (hfree : ∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1)
    {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ R) (hρ1 : ρ ≠ 1) {D : Submodule (ZMod 2) V}
    (hDC : D ⊓ C = ⊥) (hD : finrank (ZMod 2) D = finrank (ZMod 2) A)
    (hρD : ρ • D = D) : D = A := by
  have htop : D ⊔ C = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq D C
    rw [hDC, finrank_bot] at h
    have h2 := S.finrank_space
    omega
  have hρD' : ∀ d ∈ D, ρ d ∈ D := by
    intro d hd
    have : ρ d ∈ ρ • D := Submodule.smul_mem_pointwise_smul d ρ D hd
    rwa [hρD] at this
  have hmap : ∀ a ∈ A, a + ρ a ∈ D := by
    intro a ha
    have : a ∈ D ⊔ C := htop ▸ Submodule.mem_top
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp this
    have h1 : d + e + ρ (d + e) = d + ρ d := by
      rw [map_add, S.fixes ρ hρ e he]
      calc d + e + (ρ d + e) = (d + ρ d) + (e + e) := by abel
        _ = d + ρ d := by rw [ZModModule.add_self, add_zero]
    rw [h1]
    exact D.add_mem hd (hρD' d hd)
  let θ : A → A := fun a => ⟨a + ρ a, A.add_mem a.2 (S.preserves ρ hρ a a.2)⟩
  have hθinj : Function.Injective θ := by
    intro a a' h
    have h1 : (a : V) + ρ a = a' + ρ a' := congrArg Subtype.val h
    have h3 : ((a : V) + a') + (ρ a + ρ a') = 0 := by
      calc ((a : V) + a') + (ρ a + ρ a') = ((a : V) + ρ a) + (a' + ρ a') := by abel
        _ = (a' + ρ a') + (a' + ρ a') := by rw [h1]
        _ = 0 := ZModModule.add_self _
    have h2 : ρ ((a : V) + a') = (a : V) + a' := by
      rw [map_add]
      exact ((add_eq_zero_iff_eq _ _).mp h3).symm
    by_contra hne
    have hne' : (a : V) + a' ≠ 0 := (add_ne_zero_iff_ne _ _).mpr (fun h => hne (Subtype.ext h))
    exact hρ1 (hfree ρ hρ _ (A.add_mem a.2 a'.2) hne' h2)
  have hθsurj : Function.Surjective θ := Finite.injective_iff_surjective.mp hθinj
  have hAD : A ≤ D := by
    intro a ha
    obtain ⟨a', ha'⟩ := hθsurj ⟨a, ha⟩
    have : (a' : V) + ρ a' = a := congrArg Subtype.val ha'
    rw [← this]
    exact hmap a' a'.2
  exact (Submodule.eq_of_le_of_finrank_eq hAD hD.symm).symm

theorem natCard_R (S : Setting X R A C)
    (hfree : ∀ r ∈ R, ∀ a ∈ A, a ≠ 0 → r a = a → r = 1) (hA : 2 ≤ finrank (ZMod 2) A) :
    Nat.card R = 2 ^ finrank (ZMod 2) A - 1 := by
  obtain ⟨a₀, ha₀, ha₀0, -⟩ := exists_mem_ne_two A hA 0 0
  let f : R → V := fun ρ => (ρ : V ≃ₗ[ZMod 2] V) a₀
  have hf : Function.Injective f := by
    intro ρ ρ' h
    have h1 : ((ρ'⁻¹ * ρ : R) : V ≃ₗ[ZMod 2] V) a₀ = a₀ := by
      show (ρ' : V ≃ₗ[ZMod 2] V)⁻¹ ((ρ : V ≃ₗ[ZMod 2] V) a₀) = a₀
      rw [show (ρ : V ≃ₗ[ZMod 2] V) a₀ = (ρ' : V ≃ₗ[ZMod 2] V) a₀ from h]
      simp
    have h2 : (ρ'⁻¹ * ρ : R) = 1 := Subtype.ext (hfree _ (ρ'⁻¹ * ρ).2 a₀ ha₀ ha₀0 h1)
    exact (inv_mul_eq_one.mp h2).symm
  have hrange : Set.range f = (A : Set V) \ {0} := by
    ext v
    constructor
    · rintro ⟨ρ, rfl⟩
      refine ⟨S.preserves ρ ρ.2 a₀ ha₀, ?_⟩
      intro h
      simp only [Set.mem_singleton_iff] at h
      exact ha₀0 ((map_eq_zero_iff (ρ : V ≃ₗ[ZMod 2] V) (ρ : V ≃ₗ[ZMod 2] V).injective).mp h)
    · rintro ⟨hv, hv0⟩
      obtain ⟨r, hr, hra⟩ := S.trans a₀ ha₀ v hv ha₀0 hv0
      exact ⟨⟨r, hr⟩, hra⟩
  have h1 := Set.ncard_range_of_injective hf
  rw [hrange] at h1
  rw [← h1]
  have h3 := Set.ncard_sdiff_singleton_add_one (a := (0 : V)) (s := (A : Set V)) A.zero_mem
  rw [ncard_submodule] at h3
  omega

end CFSG.QuasithinUnique.ONan
