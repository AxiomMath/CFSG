module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalFive
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatSporadicTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviConj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAMain
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyMain
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowCat

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

open CFSG.Quasithin (perfectCore) in
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixIsometries) in
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus) in
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom) in
@[expose] def OmegaPlusSpLeviConjInput : Prop :=
  ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n), Even f →
    ∀ s : matrixIsometries (coordinateQuadPlus n K),
      orderOf (isometryConjugationHom _ s) = 2 →
      2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank →
      ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
        (OmegaPilot.SpLeviSections
            (OmegaPilot.plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
            (perfectCore (LinearPilot.autFixSubgroup (isometryConjugationHom _ s₀))) ∨
          OmegaPilot.SpLeviData
            (OmegaPilot.plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
            (perfectCore (LinearPilot.autFixSubgroup (isometryConjugationHom _ s₀))))

theorem omegaPlusHigherRankRigidityInput_of_spLeviConj (h : OmegaPlusSpLeviConjInput) :
    OmegaPlusHigherRankRigidityInput := fun n f K _ _ _ hK hn hfe =>
  OmegaPilot.higherRankCoresRigid_of_spLeviData_conj hK (OmegaPilot.four_le_card_of_even hK hfe)
    fun s h₁ hr => by
      obtain ⟨s₀, a, hs, hs₀⟩ := h n f K hK hn hfe s h₁ hr
      exact ⟨s₀, a, hs, hs₀.elim (OmegaPilot.spLeviData_of_spLeviSections _
        (OmegaPilot.four_le_card_of_even hK hfe)) id⟩

open CFSG.Quasithin (perfectCore) in
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixIsometries) in
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus) in
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom) in
@[expose] def OmegaPlusSpLeviTypeANSubTwoInput : Prop :=
  ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n), Even f →
    ∀ s : matrixIsometries (coordinateQuadPlus n K), s * s = 1 →
      (∀ w ∈ LinearMap.range (OmegaPilot.sNil s.val), coordinateQuadPlus n K w = 0) →
      Module.finrank K (LinearMap.range (OmegaPilot.sNil s.val)) + 2 = n →
      ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
        OmegaPilot.SpLeviData
          (OmegaPilot.plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
          (perfectCore (LinearPilot.autFixSubgroup (isometryConjugationHom _ s₀)))

open CFSG.Quasithin (perfectCore) in
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixIsometries) in
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus) in
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom) in
@[expose] def OmegaPlusSpLeviTypeBCInput : Prop :=
  ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n), Even f →
    ∀ s : matrixIsometries (coordinateQuadPlus n K), s * s = 1 →
      3 ≤ Module.finrank K (LinearMap.range (OmegaPilot.sNil s.val)) →
      (∃ w ∈ LinearMap.range (OmegaPilot.sNil s.val), coordinateQuadPlus n K w ≠ 0) →
      ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
        OmegaPilot.SpLeviData
          (OmegaPilot.plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
          (perfectCore (LinearPilot.autFixSubgroup (isometryConjugationHom _ s₀)))

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus) in
theorem omegaPlusSpLeviConjInput_of_typeA_nSubTwo_of_typeBC
    (hA2 : OmegaPlusSpLeviTypeANSubTwoInput) (hBC : OmegaPlusSpLeviTypeBCInput) :
    OmegaPlusSpLeviConjInput := by
  intro n f K _ _ _ hK hn hfe s h₁ hr
  have hss : s * s = 1 := OmegaPilot.mul_self_eq_one_of_orderOf_plus (by omega) h₁
  rw [OmegaPilot.matrixRank_sub_one_eq_finrank_sNil] at hr
  by_cases hQW : ∀ w ∈ LinearMap.range (OmegaPilot.sNil s.val), coordinateQuadPlus n K w = 0
  · by_cases hℓ : Module.finrank K (LinearMap.range (OmegaPilot.sNil s.val)) + 2 = n
    · obtain ⟨s₀, a, hs, h⟩ := hA2 n f K hK hn hfe s hss hQW hℓ
      exact ⟨s₀, a, hs, .inr h⟩
    · obtain ⟨s₀, a, hs, h⟩ := OmegaPilot.exists_conj_spLeviData_typeA
        (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn (OmegaPilot.four_le_card_of_even hK hfe)
        s h₁ hQW hℓ
      exact ⟨s₀, a, hs, .inr h⟩
  · have hW : ∃ w ∈ LinearMap.range (OmegaPilot.sNil s.val), coordinateQuadPlus n K w ≠ 0 := by
      simpa only [not_forall, exists_prop] using hQW
    rcases (show Module.finrank K (LinearMap.range (OmegaPilot.sNil s.val)) = 2 ∨
        3 ≤ Module.finrank K (LinearMap.range (OmegaPilot.sNil s.val)) by omega) with h2 | h3
    · exact ⟨s, 1, by rw [one_mul, inv_one, mul_one], .inr (OmegaPilot.spLeviData_typeC_two _ hK hn
        (OmegaPilot.four_le_card_of_even hK hfe) s hss h2 hW)⟩
    · obtain ⟨s₀, a, hs, h⟩ := hBC n f K hK hn hfe s hss h3 hW
      exact ⟨s₀, a, hs, .inr h⟩

section Graph

section Omega

section TwistedE6

theorem twistedE6TwoInput_of_final6 (hGLS : GLS3OddLieAutComponentsInput) : TwistedE6TwoInput :=
  twistedE6TwoInput_of_rows_of_gls3 hGLS
    (TwistedE6Pilot.twistedE6TwoFieldRowInput_of_rigidity
      TwistedE6Pilot.twistedE6TwoDiagonalRigidity_holds)
    TwistedE6Pilot.twistedE6TwoSwapRowInput_holds

theorem seitzExclusion_highTwistedE6_of_final6 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion (HighExceptional .twistedE6) :=
  seitzExclusion_highTwistedE6_of_final5 hGLS (twistedE6TwoInput_of_final6 hGLS)

section F4

theorem twoRowsInput_of_cat_of_gls3 (hGLS : GLS3OddLieAutComponentsInput)
    (h : F4Pilot.TwoRowsCatInput) : F4Pilot.TwoRowsInput :=
  h (sp6CatalogueClauses_of_xchar hGLS monsterInnerInput monsterLocalComponentsInput
    (catSp6SporadicResidual_of_atF_one catSp6SporadicResidualAtF_one_holds))

section PSp

theorem spThreeInput_of_final6 (hGLS : GLS3OddLieAutComponentsInput)
    (hGraph : SymplecticPilot.SpThreeGraphRowsInput) : SymplecticPilot.SpThreeInput :=
  spThreeInput_of_gls3 hGLS SymplecticPilot.catSp2mSporadicResidual_two hGraph

end PSp

end F4

end TwistedE6

end Omega

end Graph

end CFSG.SeitzReduction
