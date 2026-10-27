module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF4.A2Frame

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

@[expose] def e8ExtVec : Option (Fin 8) → Fin Tag.E8.rank → ℤ
  | none => -![2, 3, 4, 6, 5, 4, 3, 2]
  | some j => Pi.single j 1

@[expose] def e8EdgesRaw : List (Option (Fin 8) × Option (Fin 8)) :=
  [(some 0, some 2), (some 1, some 3), (some 2, some 0), (some 2, some 3), (some 3, some 1),
    (some 3, some 2), (some 3, some 4), (some 4, some 3), (some 4, some 5), (some 5, some 4),
    (some 5, some 6), (some 6, some 5), (some 6, some 7), (some 7, some 6), (some 7, none),
    (none, some 7)]

@[expose] def e8EdgeWord : Option (Fin 8) → Option (Fin 8) → List (Fin Tag.E8.rank)
  | some 1, some 3 => [4, 3, 2, 1, 3, 4, 0, 2, 3]
  | some 2, some 0 => [3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 2, some 3 => [0, 2, 3]
  | some 3, some 1 => [2, 3, 0, 2, 1, 3]
  | some 3, some 2 => [4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 3, some 4 => [2, 3, 4, 0, 2, 3]
  | some 4, some 3 => [1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 4, some 5 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 5, some 4 => [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 5, some 6 => [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 6, some 5 => [4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 6, some 7 => [5, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 7, some 6 => [5, 6, 7, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 7, none => [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4,
      5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]
  | none, some 7 => [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4,
      5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]
  | _, _ => []

@[expose] def e8Edges : List (Option (Fin Tag.E8.rank) × Option (Fin Tag.E8.rank)) := e8EdgesRaw

theorem e8Edges_ok : ∀ e ∈ e8EdgesRaw,
    wordMat Tag.E8 (e8EdgeWord e.1 e.2) *ᵥ (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) =
      e8ExtVec e.1 ∧
    wordMat Tag.E8 (e8EdgeWord e.1 e.2) *ᵥ (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) =
      e8ExtVec e.2 := by
  decide +kernel

section Frames

variable
  {L : Type} [Field L]

theorem isA2Frame_rhoSigmaE8 (v : WeylGroup Tag.E8) :
    CFSG.RankThree.PartOne.KF4.IsA2Frame (rhoSigmaE8 L v) (sigmaRootE8 v) where
  injective := rhoSigmaE8_injective v
  isRoot _ _ hij := isRoot_sigmaRootE8 v hij
  neg i j := (sigmaRootE8_neg v i j).symm
  add := sigmaRootE8_add v
  transv := rhoSigmaE8_transvection v
  range := by rw [rhoSigmaE8_range, sigmaSetE8_eq]
  diag := rhoSigmaE8_diagonal v

theorem exists_a2Frame_of_mem_e8Edges {x y : Option (Fin Tag.E8.rank)} (h : (x, y) ∈ e8Edges) :
    ∃ (ρ : SL(3, L) →* ModGL Tag.E8 L) (σ : Fin 3 → Fin 3 → Fin Tag.E8.rank → ℤ),
      CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = e8ExtVec x ∧ σ 1 2 = e8ExtVec y := by
  obtain ⟨h1, h2⟩ := e8Edges_ok _ h
  refine ⟨rhoSigmaE8 L ((coxeterSystem Tag.E8).wordProd (e8EdgeWord x y)),
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd (e8EdgeWord x y)), isA2Frame_rhoSigmaE8 _, ?_, ?_⟩
  · rw [sigmaRootE8_eq_smul, e8chainRoot13_values.1, wordProd_smul_eq_wordMat_mulVec]
    exact h1
  · rw [sigmaRootE8_eq_smul, e8chainRoot13_values.2.1, wordProd_smul_eq_wordMat_mulVec]
    exact h2

end Frames

section Paths

variable
  {L : Type} [Field L]

theorem kacE8_extRoot : kacE8.extRoot = e8ExtVec := by
  funext x
  cases x <;> rfl

end Paths

end CFSG.HardMathSupport.Timmesfeld.CrossChar
