module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LargeExtraspecial.S8A5A
public import CFSG.LargeExtraspecial.S8FiveB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem t_mem_A1_of_mem_inf (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {y : S.O}
    (hyM : y ∈ S.Mbar) (hyne : y * t * y⁻¹ ≠ t) {τ : S.O}
    (hτ : τ ∈ S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t)) (hτ1 : τ ≠ 1) :
    t ∈ A1 S g τ ∧ t ∉ zpowers τ ∧ Rbar S g τ ≠ S.Lbar g := by
  have haQ := H.conj_mem
  have hτL : τ ∈ S.Lbar g := hτ.1.1
  have hτN : τ ∈ Nbar S g t := hτ.1.2
  have h5 : ∀ z ∈ S.Mbar, z * t * z⁻¹ ∈ S.Lbar g → z * t * z⁻¹ = t := fun z hz h =>
    conj_eq_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hz h
  have hτt : τ ≠ t := by
    rintro rfl
    have h1 := (mem_conjSubgroup.mp hτ.2).1
    have h2 := h5 y⁻¹ (inv_mem hyM) (by rwa [inv_inv])
    apply hyne
    calc y * τ * y⁻¹ = y * (y⁻¹ * τ * y⁻¹⁻¹) * y⁻¹ := by rw [h2]
      _ = τ := by group
  have hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (mem_Nbar.mp hτN).2
  have hWt := (commSpace_t_eq H C ht ht1 hVQ).2
  have htNτ : t ∈ Nbar S g τ := by
    refine mem_Nbar.mpr ⟨Lbar_le_Rbar hτL ht, fun v hv => ?_⟩
    have hvW := commSpace_le_Wt_of_fix hτV (Vt_le_commSpace H hτ1 hv)
    rw [← hWt] at hvW
    exact mem_fixSpace.mp hvW
  have hcent : ∀ n ∈ Nbar S g τ, n * t = t * n := by
    intro n hn
    have hnM : n ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hn)
    have hna : (n : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
      (mem_Nbar.mp hn).2 _ (cl_a_mem_Vt hτL)
    have hnL : n ∈ normalizer (S.Lbar g : Set S.O) := by
      have h := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hnM (by
        simp only [OneMemClass.coe_one, one_mul]
        exact hna)
      simpa only [OneMemClass.coe_one, one_mul] using h
    have h1 := h5 n hnM ((mem_normalizer_iff.mp hnL t).mp ht)
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h1]
  refine ⟨mem_A1.mpr ⟨ht, htNτ, hcent⟩, ?_, ?_⟩
  · intro htz
    have hττ : τ * τ = 1 := mul_self_of_mem_Lbar S haQ hτL
    rcases eq_one_or_eq_of_mem_zpowers hττ htz with h | h
    · exact ht1 h
    · exact hτt h.symm
  ·
    intro hR
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hyM
    have hτk : τ ∈ S.Lbar ((k : G) * g) := by
      rw [Lbar_mul S k g]
      refine ⟨(S.ρ k)⁻¹ * τ * S.ρ k, (mem_conjSubgroup.mp hτ.2).1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have htk : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) := by
      rw [Lbar_mul S k g]
      exact ⟨t, ht, rfl⟩
    have h1 := Lbar_mul_le_Rbar hτk htk
    rw [hR] at h1
    exact hyne (h5 _ hyM h1)

end CFSG.LargeExtraspecial.S8
