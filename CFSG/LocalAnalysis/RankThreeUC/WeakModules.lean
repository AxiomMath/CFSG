module

public import CFSG.LocalAnalysis.RankThreeUC.NormalModules
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

variable {G : Type} [Group G]

@[expose] def centralizerInSubgroup (M V : Subgroup G) : Subgroup M :=
  (centralizer (V : Set G)).subgroupOf M

@[expose] def twoCoreModCentralizer (M V : Subgroup G) [(centralizerInSubgroup M V).Normal] :
    Subgroup (M ⧸ centralizerInSubgroup M V) :=
  CFSG.pCore 2 (M ⧸ centralizerInSubgroup M V)

@[expose] def TwoCoreModCentralizerTrivial (M V : Subgroup G) : Prop :=
  ∃ _ : (centralizerInSubgroup M V).Normal, twoCoreModCentralizer M V = ⊥

@[expose] def TwoCoreModCentralizerNontrivial (M V : Subgroup G) : Prop :=
  ∃ _ : (centralizerInSubgroup M V).Normal, twoCoreModCentralizer M V ≠ ⊥

@[expose] def GeneratedByConjugatesOutside (M V₀ V : Subgroup G) : Prop :=
  ∀ v ∈ V, v ∉ V₀ → Subgroup.closure {x | ∃ m ∈ M, x = m * v * m⁻¹} = V

variable [Finite G]

@[expose] def weakModules (M T : Subgroup G) : Set (Subgroup G) :=
  {V | V ∈ normalElemAbelian2One M T ∧ 2 < CFSG.Assembly.pRank 2 V ∧
    TwoCoreModCentralizerTrivial M V}

@[expose] def weakModulePairs (M : Subgroup G) : Set (Subgroup G × Subgroup G) :=
  {p | p.1 ∈ normalElemAbelian2 M ∧ p.2 ∈ normalElemAbelian2 M ∧ p.1 ≤ p.2 ∧
    CFSG.CGT.Timmesfeld75.IsTI p.1 ∧ ¬ CFSG.CGT.Timmesfeld75.IsTI p.2 ∧
    GeneratedByConjugatesOutside M p.1 p.2 ∧ TwoCoreModCentralizerNontrivial M p.2}

theorem weakModules_subset (M T : Subgroup G) : weakModules M T ⊆ normalElemAbelian2One M T :=
  fun _ h => h.1

end CFSG.LocalAnalysis.RankThreeUC
