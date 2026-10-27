module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Alt
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Transfer
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ThompsonFrame.alt_of_normal {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L : Subgroup X} (hLn : L.Normal) (hDL : D ≤ L) {n : ℕ}
    (hn : 5 ≤ n) (φ : L ≃* alternatingGroup (Fin n)) : p = 3 ∧ n = 7 := by
  obtain ⟨hn3, D', hD', hcard', hsig', hjoin'⟩ := hF.alt_data hLn hDL φ
  exact alternating_signalizer_case hF.prime hF.odd hn hn3 D' hD' hcard' hsig' hjoin'

theorem ThompsonFrame.alt_component {p : ℕ} {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hF : ThompsonFrame p D) {L : Subgroup X} (hL : CFSG.IsComponent L) {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) : p = 3 ∧ n = 7 := by
  obtain ⟨hLn, hDL, h5, ⟨φ⟩⟩ :=
    hF.exists_alt_normal hL (fun L' hL' => hF.component_unique hL' hL) e
  exact hF.alt_of_normal hLn hDL h5 φ

@[expose] def GL83RelPair2ThompsonAlt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T H V : Subgroup G),
    MaximalRelativePair p P M D R T → IsOptimalRelPair p M D R T H V →
      OptimalRelPairFacts p M D H V →
        ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
          ∃ n : ℕ, Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))

theorem gl83RelPair2Thompson_of_alt (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (h : GL83RelPair2ThompsonAlt G) : GL83RelPair2Thompson G := by
  intro p hp P M D R T H V hd hopt hfacts
  obtain ⟨L, hL, n, ⟨e⟩⟩ := h p hp P M D R T H V hd hopt hfacts
  have hF := (hopt.thompsonPreFrame hS hD1 hR h13 hp hd hfacts).quotient
  have hL' : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).mpr hL
  obtain ⟨h3, h7⟩ := hF.alt_component hL' e
  subst h7
  exact ⟨h3, L, hL, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
