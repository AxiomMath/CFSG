module

public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint


variable {τ : Tag} {L : Type} [Field L]

theorem rootTorusSL2_eq_rootDiagUnit_corootPair {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Lˣ) :
    rootTorusSL2 τ L β c =
      rootDiagUnit τ (fun i => c ^ (2 * iform β (Pi.single i 1) / iform β β)) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ L hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single τ i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit τ a : ModGL τ L) : Module.End L (RootModule τ L))
      (rootVec τ L (Pi.single i 1))) = ((a i : Lˣ) : L) • rootVec τ L (Pi.single i 1) := by
    change rootDiag a (rootVec τ L (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin τ.rank → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single τ i), hs]
  rw [h2] at h1
  have hne : rootVec τ L (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  exact Units.ext (smul_left_injective L hne h1)

end CFSG.LieType.SeitzGeneration.ExcHighThree
