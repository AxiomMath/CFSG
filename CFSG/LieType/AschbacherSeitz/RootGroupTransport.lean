module

public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.LieType.AschbacherSeitz

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType.AutSt

variable {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]

theorem entrywise_rootGroup_map_eq (σ : K ≃+* K) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    Subgroup.map (entrywiseAdjointAut τ σ).toMonoidHom (rootGroup F K γ) = rootGroup F K γ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    rw [MulEquiv.coe_toMonoidHom, entrywiseAdjointAut_xPar]
    exact xPar_mem (F := F) hγ (σ c)
  · intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
    refine ⟨xPar F γ (σ.symm c), xPar_mem (F := F) hγ _, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, entrywiseAdjointAut_xPar, σ.apply_symm_apply]

noncomputable def e7EquivAlg (f : ℕ) :
    ↥(e7Data_valid.minGroup (GaloisField 2 f)) ≃*
      ↥(adjointGroup Tag.E7 (GaloisField 2 f)) :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.e7Equiv (K := GaloisField 2 f)

end CFSG.LieType.AschbacherSeitz

end
