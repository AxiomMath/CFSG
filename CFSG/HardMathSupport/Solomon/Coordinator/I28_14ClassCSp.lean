module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCConj
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassN
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module
  CFSG.LocalAnalysis.ComponentInitial

section

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_C_sp_step {f : LinearMap.BilinForm (ZMod 2) U} (halt : f.IsAlt) {v w : U}
    (hvw : f v w = 1) :
    ∃ g ∈ bilinIsometryGroup f, (g : U →ₗ[ZMod 2] U) v = w := by
  have hcomm := i28_14_N_alt_comm halt
  have h0 : f (v + w) (v + w) = 0 := halt _
  refine ⟨tv (f (v + w)) (v + w) h0, tv_mem_bilinIsometryGroup hcomm h0, ?_⟩
  rw [tv_apply, map_add, LinearMap.add_apply, halt v, zero_add, hcomm w v, hvw, one_smul,
    ← add_assoc, zmod2_add_self, zero_add]

theorem i28_14_C_sp_transitive {f : LinearMap.BilinForm (ZMod 2) U} (hnd : f.Nondegenerate)
    (halt : f.IsAlt) {v w : U} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g ∈ bilinIsometryGroup f, (g : U →ₗ[ZMod 2] U) v = w := by
  have hcomm := i28_14_N_alt_comm halt
  rcases zmod2_eq_zero_or_one (f v w) with h | h
  · have hfv : f v ≠ 0 := fun h0 => hv (hnd.1 v fun y => by rw [h0]; rfl)
    have hfw : f w ≠ 0 := fun h0 => hw (hnd.1 w fun y => by rw [h0]; rfl)
    obtain ⟨u, hu₁, hu₂⟩ := i28_14_C_exists_apply_pair hfv hfw
    obtain ⟨g₁, hg₁, hg₁v⟩ := i28_14_C_sp_step halt (v := v) (w := u) hu₁
    obtain ⟨g₂, hg₂, hg₂u⟩ := i28_14_C_sp_step halt (v := u) (w := w) (by rw [hcomm]; exact hu₂)
    refine ⟨g₂ * g₁, (bilinIsometryGroup f).mul_mem hg₂ hg₁, ?_⟩
    change (g₂ : U →ₗ[ZMod 2] U) ((g₁ : U →ₗ[ZMod 2] U) v) = w
    rw [hg₁v, hg₂u]
  · exact i28_14_C_sp_step halt h

theorem i28_14_C_sp_conj {f : LinearMap.BilinForm (ZMod 2) U} {a c : U}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U} (hg : g ∈ bilinIsometryGroup f)
    (hga : (g : U →ₗ[ZMod 2] U) a = c) (h : f a a = 0) (h' : f c c = 0) :
    g * tv (f a) a h * g⁻¹ = tv (f c) c h' := by
  have h'' : (f a ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U))
      ((g : U →ₗ[ZMod 2] U) a) = 0 := by
    rw [LinearMap.comp_apply, i28_14_C_inv_apply]; exact h
  refine (conj_tv g (f a) a h h'').trans (i28_14_C_tv_congr _ _ ?_ hga)
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, ← hga, ← hg a, i28_14_C_apply_inv]

end

section

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem tvC_sp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {f : LinearMap.BilinForm (ZMod 2) U}
    (hnd : f.Nondegenerate) (halt : f.IsAlt)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hA : IsElemAbelian p A)
    (hAG : A ≤ bilinIsometryGroup f)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U} (htG : t ∈ bilinIsometryGroup f)
    (ht : IsF2Transvection t) :
    HasCentralizedConj p (bilinIsometryGroup f) A t := by
  classical
  by_cases hc : IsCyclic A
  · exact i28_14_C_of_cyclic hp hA hc t
  obtain ⟨E, hEA, hcard, c, hcE, d, hdE, hc0, hd0, hcd⟩ := i28_14_C_exists_hyperplane hp hp2 hA hc
  obtain ⟨φt, a, h, hφt, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  obtain rfl : φt = f a := i28_14_N_sp_tv_mem hnd halt h hφt ha htG
  obtain ⟨g, hgG, hga⟩ := i28_14_C_sp_transitive hnd halt ha hc0
  have hcc : f c c = 0 := halt c
  have hconj := i28_14_C_sp_conj hgG hga h hcc
  refine i28_14_C_close (y := g⁻¹) ((bilinIsometryGroup f).inv_mem hgG) hEA hcard.le fun e he => ?_
  rw [inv_inv, hconj]
  refine i28_14_C_comm_tv hcc (hcE e he) fun x => ?_
  have hec : (e : U →ₗ[ZMod 2] U) c = c := hcE e he
  have := hAG (hEA he) c x
  rwa [hec] at this

end

end CFSG.HardMathSupport.Solomon.Coordinator
