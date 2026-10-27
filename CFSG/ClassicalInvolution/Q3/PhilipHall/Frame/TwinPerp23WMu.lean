module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WPerm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx
public import CFSG.ClassicalInvolution.Q3.TL3T1
public import CFSG.ClassicalInvolution.Uniform.U5Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5 CFSG.ClassicalInvolution.Asc77.Thompson

section Mu

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {Wg : Subgroup G}

@[expose] noncomputable def PsiM (Ω : Set (Subgroup G)) (Wg : Subgroup G) :
    ↥(MGrp Ω Wg) →* NQuot (Wg ⊔ OCW Wg) :=
  (piN Wg).comp (Subgroup.inclusion (MGrp_le_normalizer Ω Wg))

theorem PsiM_apply (x : ↥(MGrp Ω Wg)) : PsiM Ω Wg x = piG Wg (x : G) :=
  (piG_of_mem (MGrp_le_normalizer Ω Wg x.2)).symm

theorem PsiM_mem_mu (x : ↥(MGrp Ω Wg)) : PsiM Ω Wg x ∈ muGroup Ω Wg := by
  rw [PsiM_apply]
  exact piG_mem_muGroup (Subgroup.mem_sup_left x.2)

@[expose] noncomputable def PhiM (e : ↥(muGroup Ω Wg) ≃* Equiv.Perm (Fin 4)) :
    ↥(MGrp Ω Wg) →* Equiv.Perm (Fin 4) :=
  (e : ↥(muGroup Ω Wg) →* Equiv.Perm (Fin 4)).comp
    ((PsiM Ω Wg).codRestrict (muGroup Ω Wg) PsiM_mem_mu)

theorem PhiM_eq_one_iff (e : ↥(muGroup Ω Wg) ≃* Equiv.Perm (Fin 4)) (x : ↥(MGrp Ω Wg)) :
    PhiM e x = 1 ↔ (x : G) ∈ Wg ⊔ OCW Wg := by
  have h1 : PhiM e x = 1 ↔ PsiM Ω Wg x = 1 := by
    constructor
    · intro h
      have := (MulEquiv.map_eq_one_iff e).mp h
      exact congrArg Subtype.val this
    · intro h
      have : (⟨PsiM Ω Wg x, PsiM_mem_mu x⟩ : ↥(muGroup Ω Wg)) = 1 := Subtype.ext h
      show e (⟨PsiM Ω Wg x, PsiM_mem_mu x⟩ : ↥(muGroup Ω Wg)) = 1
      rw [this, map_one]
  rw [h1]
  exact piN_eq_one_iff Wg ⟨x, MGrp_le_normalizer Ω Wg x.2⟩

theorem PhiM_surjective (e : ↥(muGroup Ω Wg) ≃* Equiv.Perm (Fin 4)) :
    Function.Surjective (PhiM e) := by
  intro g
  have hq := (e.symm g).2
  obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp hq
  have hMn : MGrp Ω Wg ≤ Subgroup.normalizer (OCW Wg : Set G) :=
    (MGrp_le_normalizer Ω Wg).trans (normalizer_le_normalizer_OCW Wg)
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right (MGrp Ω Wg) (OCW Wg) hMn
  have hm' : m ∈ ((MGrp Ω Wg ⊔ OCW Wg : Subgroup G) : Set G) := hm
  rw [hco] at hm'
  obtain ⟨x, hx, o, ho, rfl⟩ := hm'
  have hxN : x ∈ Subgroup.normalizer (Wg : Set G) := MGrp_le_normalizer Ω Wg hx
  have hoN : o ∈ Subgroup.normalizer (Wg : Set G) := OCW_le_normalizer Wg ho
  have hpo : piG Wg o = 1 := piG_of_mem_sup (Subgroup.mem_sup_right ho)
  have hpx : ((e.symm g : ↥(muGroup Ω Wg)) : NQuot (Wg ⊔ OCW Wg)) = piG Wg x := by
    rw [hqm, piG_mul hxN hoN, hpo, mul_one]
  refine ⟨⟨x, hx⟩, ?_⟩
  have : (⟨PsiM Ω Wg ⟨x, hx⟩, PsiM_mem_mu ⟨x, hx⟩⟩ : ↥(muGroup Ω Wg)) = e.symm g :=
    Subtype.ext ((PsiM_apply ⟨x, hx⟩).trans hpx.symm)
  exact (congrArg e this).trans (e.apply_symm_apply g)

end Mu

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
