module

public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.Fischer.Classification.Defs
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

noncomputable abbrev cdim6 (g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
    ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1)))

end CaseII

open CaseII (cdim6)

@[expose] def CaseIISplit : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (H : Subgroup (GLV V))
    (φ : ↥H ≃* ↥(omegaMinusTwo 2))
    (β : ↥(commSpace H ⊤) →+ (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)),
    Function.Surjective β →
    β.ker = ((fixedSpace H).comap (commSpace H ⊤).subtype).toAddSubgroup →
    (∀ (h : ↥H) (w w' : ↥(commSpace H ⊤)), (w' : V) = (h : GLV V) (w : V) →
      β w' = ((φ h : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).mulVec (β w)) →
    IsCompl (commSpace H ⊤) (fixedSpace H)

@[expose] def CaseIIAut : Prop :=
  ∀ θ : MulAut ↥(omegaMinusTwo 2), ∃ o ∈ orthogonalMinus 2 (ZMod 2) 1 1,
    ∀ w : ↥(omegaMinusTwo 2),
      ((θ w : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
        o * (w : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * o⁻¹

@[expose] def CaseIIG1 : Prop :=
  ∀ a ∈ orthogonalMinus 2 (ZMod 2) 1 1, orderOf a = 2 → cdim6 a = 1 →
    (∀ b ∈ orthogonalMinus 2 (ZMod 2) 1 1, orderOf b = 2 → cdim6 b = 1 →
      ∃ g ∈ omegaMinusTwo 2, g * a * g⁻¹ = b) ∧
    Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {a}) = 720 ∧
    ∀ g ∈ orthogonalMinus 2 (ZMod 2) 1 1,
      (∀ x ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {a},
          omegaMinusTwo 2 ⊓ Subgroup.centralizer {a}⁆, g * x = x * g) →
        g = 1 ∨ g = a

@[expose] def CaseIIG9 : Prop :=
  ∀ (y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) (hy : y ∈ omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}),
    orderOf y = 2 → Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}) = 576 →
    ∀ f : ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}) →* MulAut ↥(alternatingGroup (Fin 6)),
      f ⟨y, hy⟩ = 1 → 2 ≤ CFSG.Open.pRank 2 f.ker

@[expose] def CaseIIG12 : Prop :=
  ∀ a ∈ orthogonalMinus 2 (ZMod 2) 1 1, orderOf a = 2 → cdim6 a = 1 →
    ∀ y ∈ omegaMinusTwo 2, orderOf y = 2 →
      Nat.card ↥(omegaMinusTwo 2 ⊓ Subgroup.centralizer {y}) ≠ 576 →
      ∀ x ∈ ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer {a},
          omegaMinusTwo 2 ⊓ Subgroup.centralizer {a}⁆, orderOf x = 2 →
        ∃ g ∈ omegaMinusTwo 2, g * y * g⁻¹ = x

@[expose] def CaseIIG2 : Prop :=
  (∀ (P : Sylow 2 ↥(orthogonalMinus 2 (ZMod 2) 1 1)) (Q : Sylow 2 ↥(alternatingGroup (Fin 10))),
      Nonempty (↥P ≃* ↥Q)) ∧
    ∀ (P : Sylow 2 ↥(omegaMinusTwo 2)) (Q : Sylow 2 ↥(alternatingGroup (Fin 8))),
      Nonempty (↥P ≃* ↥Q)

@[expose] def CaseIIG10 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X = 128 →
    ∀ P : Subgroup X, P.index = 2 → Nonempty (↥P ≃* (DihedralGroup 4 × DihedralGroup 4)) →
    (∃ g : X, ∃ c ∈ Subgroup.center ↥P, orderOf c = 2 ∧ g * (c : X) * g⁻¹ ≠ (c : X)) →
    ∀ M : Subgroup X, M.index = 2 → Nonempty (↥M ≃* (DihedralGroup 4 × DihedralGroup 4)) →
      (Subgroup.center ↥M).map M.subtype = (Subgroup.center ↥P).map P.subtype

@[expose] def CaseIILemma511a : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (X J L : Subgroup (GLV V))
    (z c : GLV V), J ≤ X → (J.subgroupOf X).Normal → J.relIndex X ≤ 2 →
    X ⊓ Subgroup.centralizer (J : Set (GLV V)) ≤ (Subgroup.center ↥J).map J.subtype →
    IsQuasisimple ↥J → Odd (Nat.card ↥(Subgroup.center ↥J)) → z ∈ X → orderOf z = 2 →
    IsComponentOf L (X ⊓ Subgroup.centralizer ({z} : Set (GLV V))) →
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) → IsAltNaturalModule L 6 → IsIrr J ⊤ → c ∈ L →
    orderOf c = 3 → Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) = 2 →
    (∀ (P : Sylow 2 ↥J) (Q : Sylow 2 ↥(alternatingGroup (Fin 10))), Nonempty (↥P ≃* ↥Q)) →
    Nonempty (↥J ≃* alternatingGroup (Fin 10)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 11))

@[expose] def CaseIILemma511b : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (X J L : Subgroup (GLV V))
    (z c : GLV V), J ≤ X → (J.subgroupOf X).Normal → J.relIndex X ≤ 2 →
    X ⊓ Subgroup.centralizer (J : Set (GLV V)) ≤ (Subgroup.center ↥J).map J.subtype →
    IsQuasisimple ↥J → Odd (Nat.card ↥(Subgroup.center ↥J)) → z ∈ X → orderOf z = 2 →
    IsComponentOf L (X ⊓ Subgroup.centralizer ({z} : Set (GLV V))) →
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) → IsAltNaturalModule L 6 → IsIrr J ⊤ → c ∈ L →
    orderOf c = 3 → Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) = 2 →
    (∀ (P : Sylow 2 ↥J) (Q : Sylow 2 ↥(alternatingGroup (Fin 8))), Nonempty (↥P ≃* ↥Q)) →
    Nonempty (↥J ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥J ≃* alternatingGroup (Fin 9)) ∨
      CFSG.Open.StatedClassicalModel ↥J .PSp 2 3 1

end CFSG.CGT.Foote82
