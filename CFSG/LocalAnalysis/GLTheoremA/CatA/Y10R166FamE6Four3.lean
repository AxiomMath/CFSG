module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E6FourCent3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamE6Four
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD4

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Timmesfeld.ExceptionalOrders

section Certs


theorem i166On_famE6Four_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamE6Four := by
  intro K _ _ lab p hlab hfam hp hp2 hns he hr
  have hfam' : lab = ⟨.E6, 0, 2⟩ ∧ Subgroup.center K = ⊥ ∧ p = 5 := hfam
  obtain ⟨rfl, hz, rfl⟩ := hfam'
  obtain ⟨F, hFld, hFin, hFcard, ⟨e⟩⟩ :=
    exists_mulEquiv_adjointGroup_of_isLabel_E6_two rfl hlab hz
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : Finite (ModGL Tag.E6 F) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite ↥(adjointGroup Tag.E6 F) := inferInstance
  exact htr e (p := 5)
    (exists_concl166S_adjointGroup_E6_four_of_concrete hFcard
      (exists_concl166S_e6Four (layerData166At_D le_rfl le_rfl)))

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
