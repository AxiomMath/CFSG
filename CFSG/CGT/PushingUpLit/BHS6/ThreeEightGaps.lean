module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.CStar
public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def SL2EvenMultiplierTrivial : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (E : Type) [Group E] [Finite E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)),
    Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 ↥π.ker →
      Group.IsPerfect E → π.ker = ⊥

@[expose] def PushUpPerfectTwo : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (G T V P' : Subgroup Γ)
    (α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (β : ↥V →* Multiplicative (Fin 2 → GaloisField 2 2)),
    CharTwo G → IsSylowTwoOf T G → cStarIn G T ≠ G →
    G ≤ Subgroup.normalizer (V : Set Γ) → omegaOneCenterOf T ≤ V →
    V ≤ omegaOneCenterOf (pCoreOf 2 G) →
    Function.Surjective α → α.ker = (Subgroup.centralizer (V : Set Γ)).subgroupOf G →
    Function.Surjective β →
    (∀ (g : ↥G) (v v' : ↥V), (v' : Γ) = g * v * g⁻¹ →
      Multiplicative.toAdd (β v') =
        (α g : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec (Multiplicative.toAdd (β v))) →
    β.ker = (Subgroup.centralizer (G : Set Γ)).subgroupOf V →
    P' ≤ G → baum T ≤ P' → V ≤ P' → IsSylowTwoOf (baum T) P' → IsMinParabolic2 (baum T) P' →
    CharTwo P' → (P'.subgroupOf G).map α = ⊤ → NoCharNormal (baum T) P' →
    (∀ t ∈ T, ∃ b ∈ baum T, b⁻¹ * t ∈ Subgroup.centralizer (V : Set Γ)) →
    ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (V : Set Γ) →
    IsChi0Block P' (twoResidual P') → IsLin2Type (twoResidual P') 2 →
      ⁅pCoreOf 2 (twoResidual P'), twoResidual P'⁆ = pCoreOf 2 (twoResidual P')

end CFSG.CGT.PushingUpLit.BHS6
