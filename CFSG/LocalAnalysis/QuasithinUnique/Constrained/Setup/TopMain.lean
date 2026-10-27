module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bFinal
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift
open scoped Pointwise

variable {G : Type} [Group G]

theorem evenSL2_packet_all [Finite G] (hEven : EvenSL2ActualBlockProduction) {S P : Subgroup G}
    (h : PushUpObstruction S P) (hhas : HasEvenSL2Component (autOn P (reducedModule S P))) :
    ∃ (r : ℕ) (L : Fin r → Subgroup G), BlockPacket S P r L ∧
      ∀ (D : Subgroup (MulAut (reducedModule S P))) (n : ℕ) (F : Type) (_ : Field F),
        IsComp D (autOn P (reducedModule S P)) → 2 ≤ n → Nat.card F = 2 ^ n →
        Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F) → EvenSL2Refinement S P n r L := by
  obtain ⟨D₀, n₀, F₀, _, hD₀, hn₀, hF₀, hiso₀⟩ := hhas
  have hchar : ∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum S →
      (Rc.subgroupOf (baum S)).Characteristic → ¬ P ≤ Subgroup.normalizer (Rc : Set G) := by
    intro Rc hne hle hch
    exact h.noCharNormal Rc hne (hle.trans (C1GN.baum_le S))
      (C1GN.characteristic_subgroupOf_trans (C1GN.baum_le S) hle (C1GN.characteristic_baum S) hch)
  obtain ⟨r, Lc, hLc⟩ := exists_compList (autOn P (reducedModule S P))
  have hout : ∀ (D : Subgroup (MulAut (reducedModule S P))) (n : ℕ) (F : Type) (_ : Field F),
      IsComp D (autOn P (reducedModule S P)) → 2 ≤ n → Nat.card F = 2 ^ n →
      Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
      EvenSL2BlockOutput P S (reducedModule S P) (reducedAction_of_pushUpObstruction h).le_normalizer
        n r Lc := by
    intro D n F _ hD hn hF hiso
    exact hEven G P S (uniqueMaxOver S P) (reducedModule S P) n F
      (evenSL2_setting h hn hF hD hiso) h.charTwo hchar r Lc hLc
  have hsqt : CFSG.pRank 3 ↥P ≤ 2 := h.sqtk.1 3 Nat.prime_three (by norm_num)
  have hout₀ := hout D₀ n₀ F₀ inferInstance hD₀ hn₀ hF₀ hiso₀
  have hpre := prePacket_of_output (reducedAction_of_pushUpObstruction h).le_normalizer hout₀
  exact ⟨r, _, blockPacket_of_prePacket h hpre (hout₀.rank.2.trans hsqt),
    fun D n F _ hD hn hF hiso => ⟨(hout D n F inferInstance hD hn hF hiso).type_lin,
      (hout D n F inferInstance hD hn hF hiso).type_alt⟩⟩

theorem minParabolicTwoEscapingBlocks
    (hSolv : SolvableA3Family)
    (hEven : EvenSL2ActualBlockProduction) (hSQT : NonsolvableActionSQT)
    (hone : OneQuasisimpleResidualProp) (hfam : FamilyRestrictionProp) (hA6 : NoAlt6Component)
    (hU33 : NoPSU33Component) (hU32 : NoEvenUnitaryThreeComponent)
    (hTri : NoTrialityOrLargeReeComponent) (hG2 : NoG2OrTitsComponent)
    (hL3 : X7a.ActualLinearThreeSelfDualSections) (hSp4 : X7b.ActualSymplecticFourData) :
    ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G), PushUpObstruction S P →
      (Group.IsSolvable (autOn P (reducedModule S P)) ∨
        HasEvenSL2Component (autOn P (reducedModule S P))) ∧
      ∃ (r : ℕ) (L : Fin r → Subgroup G), BlockPacket S P r L ∧
        (Group.IsSolvable (autOn P (reducedModule S P)) → SolvableRefinement r L) ∧
        (∀ (D : Subgroup (MulAut (reducedModule S P))) (n : ℕ) (F : Type) (_ : Field F),
          IsComp D (autOn P (reducedModule S P)) → 2 ≤ n → Nat.card F = 2 ^ n →
          Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F) → EvenSL2Refinement S P n r L) := by
  intro G _ _ S P h
  have hL3' : NoPSL3Component := X7a.noPSL3Component_final hL3
  by_cases hs : Group.IsSolvable (autOn P (reducedModule S P))
  · obtain ⟨r, L, hL, href⟩ := solvable_packet hSolv h hs
    exact ⟨Or.inl hs, r, L, hL, fun _ => href,
      fun D _ _ _ hD _ _ _ => absurd hs (not_isSolvable_of_isComp hD)⟩
  · by_cases hno : NoEvenSL2Component (autOn P (reducedModule S P))
    · exfalso
      obtain ⟨L, hdata, ⟨f, hf, hmodel⟩, hsqtk, E, hFF⟩ :=
        evenLinearThree hSQT hone hfam hA6 hU33 hU32 hTri hG2 (X7b.noPSp4Component_final hSp4) G S P
          h hs hno
      have hV := (reducedAction_of_pushUpObstruction h).isElemAbelian
      let _ : CommGroup (reducedModule S P) := commGroupOfElemAbelian hV
      exact @hL3' (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance _ _ _ E hFF hs
        hsqtk L hdata.residual.isComp f hf hmodel
    · have hhas := not_noEvenSL2Component_iff.mp hno
      obtain ⟨r, L, hL, href⟩ := evenSL2_packet_all hEven h hhas
      exact ⟨Or.inr hhas, r, L, hL, fun hs' => absurd hs' hs, href⟩

theorem minParabolicBlocks_of_clusters
    (hSolv : SolvableA3Family)
    (hEven : EvenSL2ActualBlockProduction) (hSQT : NonsolvableActionSQT)
    (hone : OneQuasisimpleResidualProp) (hfam : FamilyRestrictionProp) (hA6 : NoAlt6Component)
    (hU33 : NoPSU33Component) (hU32 : NoEvenUnitaryThreeComponent)
    (hTri : NoTrialityOrLargeReeComponent) (hG2 : NoG2OrTitsComponent)
    (hL3 : X7a.ActualLinearThreeSelfDualSections) (hSp4 : X7b.ActualSymplecticFourData) :
    MinParabolicBlocks :=
  minParabolicBlocks_of_blockPacket fun G _ _ S P h => by
    obtain ⟨-, r, L, hL, -⟩ := minParabolicTwoEscapingBlocks hSolv hEven hSQT hone hfam hA6 hU33
      hU32 hTri hG2 hL3 hSp4 G S P h
    exact ⟨r, L, hL⟩

end CFSG.QuasithinUnique.Setup.Top
