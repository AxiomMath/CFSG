module

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCov
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem fk_l34g_fix_map_inv {Y : Type} [Group Y] (τ σ : MulAut Y) :
    (L34GFix (τ * σ * τ⁻¹)).map (τ⁻¹).toMonoidHom = L34GFix σ := by
  have h1 : L34GFix (τ * σ * τ⁻¹) = (L34GFix σ).comap (τ⁻¹).toMonoidHom := by
    ext p
    rw [l34g_mem_fix, Subgroup.mem_comap, l34g_mem_fix]
    change (τ * σ * τ⁻¹) p = p ↔ σ (τ⁻¹ p) = τ⁻¹ p
    constructor
    · intro hp
      apply τ.injective
      simp only [MulAut.mul_apply, MulAut.inv_apply] at hp
      simp only [MulAut.mul_apply, MulAut.inv_apply]
      rw [hp, MulEquiv.apply_symm_apply]
    · intro hp
      simp only [MulAut.mul_apply, MulAut.inv_apply] at hp
      simp only [MulAut.mul_apply, MulAut.inv_apply]
      rw [hp, MulEquiv.apply_symm_apply]
  rw [h1, Subgroup.map_comap_eq_self_of_surjective (τ⁻¹).surjective]

theorem fkKGAConcl_of_conj {Y : Type} [Group Y] (τ σ : MulAut Y) {B : Subgroup Y}
    (h : ∃ J : Subgroup Y, IsComponentIn J (L34GFix (τ * σ * τ⁻¹)) ∧ InFStar J ∧
      B.map τ.toMonoidHom ≤ J) :
    ∃ J : Subgroup Y, IsComponentIn J (L34GFix σ) ∧ InFStar J ∧ B ≤ J := by
  obtain ⟨J, hJ, hJF, hBJ⟩ := h
  refine ⟨J.map (τ⁻¹).toMonoidHom,
    ?_, l34g_x_inFStar_map_inj (τ⁻¹).toMonoidHom (τ⁻¹).injective hJF, ?_⟩
  · have hcomp :=
      (sec63PT_isComponentIn_map_iff (τ⁻¹).toMonoidHom (τ⁻¹).injective).mpr hJ
    rwa [fk_l34g_fix_map_inv τ σ] at hcomp
  · intro b hb
    exact ⟨τ b, hBJ ⟨b, hb, rfl⟩, by
      change τ⁻¹ (τ b) = b
      rw [MulAut.inv_apply_self]⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fkKGAAt_of_isomInvConj (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 8)
    (h53 : ∀ (s : OGroup Q) (hs : s * s = 1), Fj53 hQ hs)
    (h : ∀ α : MulAut (omegaProj hQ), α * α = 1 →
      ∃ (τ : MulAut (omegaProj hQ)) (s : OGroup Q), s * s = 1 ∧ τ * α * τ⁻¹ = projAut hQ s) :
    FJKGAAt ↥(omegaProj hQ) := by
  intro y B hy hB σ hσσ hσ1 hfix hσy
  obtain ⟨τ, s, hs, hτσ⟩ := h σ hσσ
  have hσ'1 : projAut hQ s ≠ 1 := by
    intro h1
    apply hσ1
    have h2 : τ * σ * τ⁻¹ = 1 := by rw [hτσ, h1]
    calc σ = τ⁻¹ * (τ * σ * τ⁻¹) * τ := by group
      _ = 1 := by rw [h2]; group
  have hy' : orderOf (τ y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
  have hB' : Sl23PocketIn ⊤ (τ y) (B.map τ.toMonoidHom) := by
    have h1 := Sl23PocketIn.map_mulEquiv τ hB
    rwa [Subgroup.map_top_of_surjective τ.toMonoidHom τ.surjective] at h1
  have hfix' : ∀ b ∈ B.map τ.toMonoidHom, projAut hQ s b = b := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    change projAut hQ s (τ b₀) = τ b₀
    rw [← hτσ]
    change (τ * σ * τ⁻¹) (τ b₀) = τ b₀
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix b₀ hb₀]
  have hne' : projAut hQ s ≠ MulAut.conj (τ y) := by
    intro hconj
    have hconjτ : MulAut.conj (τ y) = τ * MulAut.conj y * τ⁻¹ := by
      ext p
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    have h2 : σ = MulAut.conj y := by
      calc σ = τ⁻¹ * (τ * σ * τ⁻¹) * τ := by group
        _ = τ⁻¹ * MulAut.conj (τ y) * τ := by rw [hτσ, hconj]
        _ = τ⁻¹ * (τ * MulAut.conj y * τ⁻¹) * τ := by rw [hconjτ]
        _ = MulAut.conj y := by group
    exact hσy h2
  obtain ⟨J, hJ, hJF, hBJ⟩ :=
    fj_kga_engine hQ hn hs (h53 s hs) hσ'1 hy' hB' hfix' hne'
  exact fkKGAConcl_of_conj τ σ
    ⟨J, by rw [l34g_fix_eq_fixSub, hτσ]; exact hJ, hJF, hBJ⟩

end CFSG.OddStandard.SmallF3.Omega
