module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureLinear
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureChevalley
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthModel
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureUnitModel
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExc
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankThreeUC.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem not_rankThreeUC_of_statedPSL {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n 2 f) : ¬ rankThreeUC G := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_rankThreeUC_of_PSL hS
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm)

theorem not_rankThreeUC_of_statedPSp {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSp n 2 f) : ¬ rankThreeUC G := by
  obtain ⟨⟨-, -, hn, -⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_rankThreeUC_of_PSp hS (by omega) e

theorem not_rankThreeUC_of_statedPOmegaPlus {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaPlus n 2 f) :
    ¬ rankThreeUC G := by
  obtain ⟨⟨-, -, hn⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_rankThreeUC_of_POmegaPlus hS hn e

theorem not_rankThreeUC_of_statedPOmegaMinus {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaMinus n 2 f) :
    ¬ rankThreeUC G := by
  obtain ⟨⟨-, -, hn⟩, K, hK, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hcard
  exact not_rankThreeUC_of_POmegaMinus hS hn hirr e

theorem not_rankThreeUC_of_statedPSU {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU n 2 f) : ¬ rankThreeUC G := by
  obtain ⟨⟨-, -, hn, -⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  exact not_rankThreeUC_of_PSU hS hn hcard e

section Residual


@[expose] def ChevalleySplitCase (G : Type) [Group G] [Finite G] : Prop :=
  ∃ (τ : Tag) (K : Type) (_ : Field K) (_ : CharP K 2) (_ : Finite K) (i j : Fin τ.rank),
    τ.cartan j i = 0 ∧ τ.cartan i j = 0 ∧ Nonempty (G ≃* adjointGroup τ K) ∧
      ∃ p ∈ rankThreeSigmaA G, p ≠ 2 ∧ p ∣ Nat.card Kˣ

@[expose] def PSLTwoCase (G : Type) [Group G] : Prop :=
  ∃ n f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n 2 f

@[expose] def PSpTwoCase (G : Type) [Group G] : Prop :=
  ∃ n f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSp n 2 f

@[expose] def POmegaTwoCase (G : Type) [Group G] : Prop :=
  (∃ n f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaPlus n 2 f) ∨
    ∃ n f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaMinus n 2 f

@[expose] def PSUTwoCase (G : Type) [Group G] : Prop :=
  ∃ n f : ℕ, CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU n 2 f

@[expose] def CatalogNoUCResidual (G : Type) [Group G] [Finite G] : Prop :=
  Standing G → CFSG.Blueprint.Catalog G → ¬ PSLTwoCase G → ¬ PSpTwoCase G →
    ¬ POmegaTwoCase G → ¬ PSUTwoCase G → ¬ ExceptionalTwoCase G → ¬ ChevalleySplitCase G →
      ¬ rankThreeUC G

theorem catalogNoUC_of_residual {G : Type} [Group G] [Finite G] (h : CatalogNoUCResidual G) :
    CatalogNoUC G := by
  intro hS hC
  by_cases hpsl : PSLTwoCase G
  · obtain ⟨n, f, hmod⟩ := hpsl
    exact not_rankThreeUC_of_statedPSL hS hmod
  by_cases hpsp : PSpTwoCase G
  · obtain ⟨n, f, hmod⟩ := hpsp
    exact not_rankThreeUC_of_statedPSp hS hmod
  by_cases hpom : POmegaTwoCase G
  · rcases hpom with ⟨n, f, hmod⟩ | ⟨n, f, hmod⟩
    · exact not_rankThreeUC_of_statedPOmegaPlus hS hmod
    · exact not_rankThreeUC_of_statedPOmegaMinus hS hmod
  by_cases hpsu : PSUTwoCase G
  · obtain ⟨n, f, hmod⟩ := hpsu
    exact not_rankThreeUC_of_statedPSU hS hmod
  by_cases hexc : ExceptionalTwoCase G
  · exact not_rankThreeUC_of_exceptionalTwoCase hS hexc
  by_cases hsplit : ChevalleySplitCase G
  · obtain ⟨τ, K, _, _, _, i, j, hji, hij, ⟨e⟩, p, hp, hp2, hdvd⟩ := hsplit
    exact not_rankThreeUC_of_chevalley_iso τ K hS e i j hji hij hp hp2 hdvd
  · exact h hS hC hpsl hpsp hpom hpsu hexc hsplit

end Residual

end CFSG.LocalAnalysis.RankThreeUC
