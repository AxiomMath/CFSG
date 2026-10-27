module

public import CFSG.LargeExtraspecial.S8ThreeA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem mem_normalizer_Abar_of_fix (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    τ ∈ normalizer ((S.Lbar g ⊓ Nbar S g t : Subgroup S.O) : Set S.O) := by
  have hτL := mem_normalizer_Lbar_of_fix H ht hτM hτV
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hτM
  have hτN : ∀ n ∈ Nbar S g t, S.ρ k * n * (S.ρ k)⁻¹ ∈ Nbar S g t :=
    fun n hn => conj_mem_Nbar H.conj_mem hτt hn
  have hτN' : ∀ n ∈ Nbar S g t, (S.ρ k)⁻¹ * n * S.ρ k ∈ Nbar S g t := by
    intro n hn
    have h1 : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by
      rw [map_inv]
      calc (S.ρ k)⁻¹ * t = (S.ρ k)⁻¹ * (t * S.ρ k) * (S.ρ k)⁻¹ := by group
        _ = (S.ρ k)⁻¹ * (S.ρ k * t) * (S.ρ k)⁻¹ := by rw [hτt]
        _ = t * (S.ρ k)⁻¹ := by group
    have := conj_mem_Nbar H.conj_mem h1 hn
    rwa [map_inv, inv_inv] at this
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyL, hyN⟩
    exact ⟨(mem_normalizer_iff.mp hτL y).mp hyL, hτN y hyN⟩
  · rintro ⟨hyL, hyN⟩
    refine ⟨(mem_normalizer_iff.mp hτL y).mpr hyL, ?_⟩
    have := hτN' _ hyN
    rwa [show (S.ρ k)⁻¹ * (S.ρ k * y * (S.ρ k)⁻¹) * S.ρ k = y by group] at this

end CFSG.LargeExtraspecial.S8
