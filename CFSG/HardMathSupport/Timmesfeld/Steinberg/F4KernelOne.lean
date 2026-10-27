module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.F4ThreeSigma
public import CFSG.LieType.AlgebraicGroups.ToralRootCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem kernelSizes_rootCharHom_one_F4 {L : Type} [Field L] :
    KernelSizes (rootCharHom (1 : Fin Tag.F4.rank → Lˣ)) [48] :=
  (ComponentCert.kernelSizes_of_check (S := f4SigmaCertF4) (inS := fun _ => true)
    (fun k _ => by simp [rootCharHom, rootChar]) (by decide +kernel)).of_perm (by decide +kernel)

theorem rootDiagUnit_ne_one_of_ncard_ne_F4
    {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (h : (componentRoots (rootCharHom a) i).ncard ≠ 48) :
    rootDiagUnit Tag.F4 a ≠ 1 := by
  intro ha
  obtain rfl : a = 1 := rootDiagUnit_injective (ha.trans rootDiagUnit_one.symm)
  have hK := kernelSizes_rootCharHom_one_F4 (L := L)
  exact h (by rw [hK.componentRoots_eq i]; exact hK.ncard_eq)

end CFSG.HardMathSupport.Timmesfeld.Steinberg

end
