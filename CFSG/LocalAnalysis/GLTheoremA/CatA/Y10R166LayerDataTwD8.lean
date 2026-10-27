module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Open
open QuadraticMap Subgroup ClassicalGroups.Orthogonal
open scoped Classical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n q : ℕ} {b c : F}

theorem exists_qLayer_of_layerQGenerators (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hqdvd : q ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hq2 : q ≠ 2)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3 ≤ bJ X ∧
      Nat.card ↥(Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3) = q ^ 2 ∧
      GLAPLayer q (Subgroup.centralizer
        (↑(Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3) :
          Set (matrixProjectiveDerived (Qc F b c)))) ≠ ⊥ := by
  have h2 : Subgroup.zpowers X.g2 ≤ bJ X := by
    rw [bJ_eq_sup]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right le_rfl))
  have h3 : Subgroup.zpowers X.g3 ≤ bJ X := by
    rw [bJ_eq_sup]
    exact le_sup_of_le_left (le_sup_of_le_right le_rfl)
  exact ⟨sup_le h2 h3, exists_qLayer_of_mem_leviFixBar hirr hF hq hqdvd hn hq2
    X.mem_g2 X.mem_g3 X.ord_g2 X.ord_g3⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open scoped Classical

theorem twDLayerData_holds : TwDLayerData := by
  intro F _ _ _ n q hn hF hq hq2 hqdvd b c hirr
  obtain ⟨X⟩ :=
    OmegaMinusLD.exists_layerQGenerators (F := F) (n := n) (q := q) (b := b) (c := c) hirr hF hq hqdvd hn
  obtain ⟨hEJle, hEJcard, hEJlayer⟩ :=
    OmegaMinusLD.exists_qLayer_of_layerQGenerators (F := F) (n := n) (q := q) (b := b) (c := c)
      hirr hF hq hqdvd hn hq2 X
  exact ⟨OmegaMinusLD.bJ X,
    rootRadicalBar (OmegaMinusLD.Qc F b c) (OmegaMinusLD.cPair F b c 0)
      (OmegaMinusLD.cPair F b c 1),
    Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3,
    OmegaMinusLD.isElemAbelian_bJ hirr X, OmegaMinusLD.card_bJ hirr X,
    isPGroup_rootRadicalBar _ _, OmegaMinusLD.bJ_le_normalizer_rootRadicalBar hirr X,
    OmegaMinusLD.bJ_inf_centralizer_rootRadicalBar hirr X, hEJle, hEJcard, hEJlayer⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
