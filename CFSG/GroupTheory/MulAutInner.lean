module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem eq_one_of_forall_mem_apply_eq {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {α : MulAut G} (hα : ∀ x ∈ N, α x = x) :
    α = 1 := by
  ext x
  have h := CFSG.LocalAnalysis.ComponentInitial.inv_mul_apply_mem_centralizer
    (CFSG.LocalAnalysis.ComponentInitial.mem_pointwiseFixingAut.mpr hα) x
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h
  rw [MulAut.one_apply]
  exact h.symm

theorem centralizer_map_mulAut_conj_eq_bot {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Subgroup.centralizer ((N.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) :
      Set (MulAut G)) = ⊥ := by
  have hκ : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conj_eq_center, eq_bot_iff, ← hC]
    exact Subgroup.center_le_centralizer (N : Set G)
  refine eq_bot_iff.mpr fun β hβ => Subgroup.mem_bot.mpr
    (eq_one_of_forall_mem_apply_eq hC fun n hn => ?_)
  have hc := Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj n) ⟨n, hn, rfl⟩
  apply hκ
  ext y
  have h1 := congrArg (fun γ : MulAut G => γ (β⁻¹ y)) hc
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.apply_inv_self, map_mul,
    map_inv] at h1
  simp only [MulAut.conj_apply]
  exact h1.symm

end CFSG.GroupTheory
