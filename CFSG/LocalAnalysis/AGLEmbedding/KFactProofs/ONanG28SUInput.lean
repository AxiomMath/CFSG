module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSylow
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def hW : List (List ℕ) := [
  gW[0]!, gW[1]! ++ gW[0]! ++ (gW[1]!).reverse, gW[1]! ++ gW[1]!, gW[2]!,
  gW[1]! ++ gW[2]! ++ (gW[1]!).reverse, gW[3]! ++ (gW[1]!).reverse, gW[1]! ++ gW[3]!]

section SU


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] noncomputable def hElt (k : ℕ) : adjointGroup .G2 K := M.wordElt hW[k]!

theorem rho_hElt (k : ℕ) : M.rho (hElt M k) = decode (wordCode hW[k]!) := M.rho_wordElt _

@[expose] noncomputable def VX : Subgroup (adjointGroup .G2 K) :=
  Subgroup.centralizer ({zE M} : Set (adjointGroup .G2 K))

@[expose] def SUHyp : Prop :=
  Nat.card (VX M) = 16547328 ∧ VX M = Subgroup.closure (Set.range fun k : Fin 7 => hElt M k)

@[expose] def SUStruct : Prop :=
  ⁅VX M, VX M⁆ = VX M ∧
  (∀ W : Subgroup (adjointGroup .G2 K), W ≤ VX M → VX M ≤ Subgroup.normalizer (W : Set _) →
    W = ⊥ ∨ W ≤ Subgroup.zpowers (zE M) ∨ W = VX M) ∧
  VX M ⊓ Subgroup.centralizer (VX M : Set (adjointGroup .G2 K)) ≤ Subgroup.zpowers (zE M) ∧
  (∃ (d : TauCeti.ValidLieTypeIndex) (ψ : VX M →* CatGroup d),
    CFSG.AGLEmbedding.IsUThreeEightIndex d ∧ Function.Surjective ψ) ∧
  ∃ v ∈ VX M, (Matrix.trace (M.rho v)) ^ 2 ≠ Matrix.trace (M.rho v) ∧
    (Matrix.trace (M.rho v)) ^ 4 ≠ Matrix.trace (M.rho v)

end SU

end CFSG.AGLEmbedding.KFactProofs.G28
