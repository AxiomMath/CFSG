module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization

section Dual

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

variable [FiniteDimensional (ZMod 2) W]

theorem isIrreducible_dual (ρ : Representation (ZMod 2) G W) (h : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  obtain ⟨hnt, hirr⟩ := (isIrreducible_iff ρ).1 h
  rw [isIrreducible_iff]
  refine ⟨?_, fun S hS => ?_⟩
  · obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) W, f w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) w).1 hcon)
    exact ⟨⟨f, 0, fun h0 => hf (by rw [h0]; rfl)⟩⟩
  · have hinv : ∀ g, ∀ u ∈ S.dualCoannihilator, ρ g u ∈ S.dualCoannihilator := by
      intro g u hu
      rw [Submodule.mem_dualCoannihilator] at hu ⊢
      intro f hf
      have h1 := hu (ρ.dual g⁻¹ f) (hS g⁻¹ f hf)
      rwa [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
        LinearMap.comp_apply] at h1
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    rcases hirr _ hinv with h0 | h1
    · right
      rw [h0, finrank_bot, add_zero] at hdim
      exact Submodule.eq_top_of_finrank_eq (by rw [hdim, Subspace.dual_finrank_eq])
    · left
      rw [h1, finrank_top] at hdim
      exact Submodule.finrank_eq_zero.1 (by omega)

theorem dual_inv_ne_one {ρ : Representation (ZMod 2) G W} {g : G} (hg : ρ g ≠ 1) :
    ρ.dual g⁻¹ ≠ 1 := by
  intro h
  apply hg
  refine LinearMap.ext fun w => ?_
  have h1 : ∀ f : Module.Dual (ZMod 2) W, f (ρ g w - w) = 0 := fun f => by
    have h2 := LinearMap.congr_fun h f
    rw [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      Module.End.one_apply] at h2
    rw [map_sub, ← LinearMap.comp_apply, h2, sub_self]
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 h1)

end Dual

end CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ

