module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Sporadic.McL

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def Hyp59.Concl81 {H : Type} [Group H] [Finite H] (h : Hyp59 H) : Prop :=
  Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) ∨
        (p = 3 ∧ f = 1 ∧ Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)))) ∧
      (Blueprint.LieModel (generalizedFitting H) .PSL 4 p f ∨
        Blueprint.LieModel (generalizedFitting H) .PSU 4 p f)

@[expose] def GS81Exit6Input : Prop :=
  ClassicalInvolution.GH74SectionalModels →
    ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H), h.L81Hyp →
      (∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) → h.Concl81

@[expose] def GS81Exit10Input : Prop :=
  GSLit.ClassicalInvolutionInput →
    ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
      d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) →
        Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f → 3 < p ^ f →
        layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
        h.Concl81

@[expose] def GS81Exit11Input : Prop :=
  In81 → RestrictedStandardInput →
    ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
      d.Stage7 v → Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2 →
        Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1 →
        layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
        centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) =
          (oddCoreIn (centralizer ({h.a} : Set H)) ⊓ centralizer ({h.a * d.z} : Set H)) ⊔ h.S →
        h.Concl81

end CFSG.ComponentClassification.GSThmB
