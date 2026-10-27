module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint


variable {R : Type} [Field R]

theorem rootTorusSL2_eq_rootDiagUnit_cartanCoord {τ : Tag}
    (hτ : Tag.symmetrizer τ = 1) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Rˣ) :
    rootTorusSL2 τ R β c =
      rootDiagUnit τ (fun k => c ^ ExceptionalCover.cartanCoord β k) := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hβ
  have hβ2 : iform β β = 2 := by
    rw [hj, hτ]
    simp
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβ]
  congr 1
  funext k
  congr 1
  rw [iform_single_right, hτ, hβ2]
  simp [ExceptionalCover.cartanCoord]

end CFSG.LocalAnalysis.GLTheoremA.Y10F
