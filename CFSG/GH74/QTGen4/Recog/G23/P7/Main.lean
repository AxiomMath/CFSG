module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.G23.P7.Assembly

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open scoped MatrixGroups


@[expose] def G23AtInvStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T H H₁ H₂ M : Subgroup G), G23Ctx G T H H₁ H₂ M →
    LieModel G .G2 0 3 1

theorem g23AtInv_of_leaves
    (hLet : LeafLettersH) (hHF : LeafHFacts) (hChar : LeafHCharTable)
    (hZ : LeafZFitting) (hOne : LeafOneClass)
    (hVC : LeafVertexCores) (hPM : LeafPbarMixed) (hFour : LeafFourClasses) (hCor : LeafCor37)
    (hAL : LeafStepALocal) (hCoh : LeafSuzukiCoherence) (hInt : LeafSuzukiIntegers)
    (hAr : LeafStepAArith)
    (hB1 : LeafB27Abelian) (hB2 : LeafB27Normalizer) (hB3 : LeafB27Contradiction)
    (hMS : LeafMStruct) (hL5 : LeafLoc5)
    (hTri : LeafTriLetters) (hCB : LeafTriCosetBound) (hTN : LeafTriNative)
    (hGI : LeafGhatInvolCent)
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hconj : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (hlie : ∀ {Y : Type} [Group Y], (Y ≃* Ghat) → LieModel Y .G2 0 3 1)
    (hSL : ¬ Group.IsSolvable SL(3, ZMod 2)) : G23AtInvStmt := by
  have : G23Leaf LeafLettersH := ⟨hLet⟩
  have : G23Leaf LeafHFacts := ⟨hHF⟩
  have : G23Leaf LeafHCharTable := ⟨hChar⟩
  have : G23Leaf LeafZFitting := ⟨hZ⟩
  have : G23Leaf LeafOneClass := ⟨hOne⟩
  have : G23Leaf LeafVertexCores := ⟨hVC⟩
  have : G23Leaf LeafPbarMixed := ⟨hPM⟩
  have : G23Leaf LeafFourClasses := ⟨hFour⟩
  have : G23Leaf LeafCor37 := ⟨hCor⟩
  have : G23Leaf LeafStepALocal := ⟨hAL⟩
  have : G23Leaf LeafSuzukiCoherence := ⟨hCoh⟩
  have : G23Leaf LeafSuzukiIntegers := ⟨hInt⟩
  have : G23Leaf LeafStepAArith := ⟨hAr⟩
  have : G23Leaf LeafB27Abelian := ⟨hB1⟩
  have : G23Leaf LeafB27Normalizer := ⟨hB2⟩
  have : G23Leaf LeafB27Contradiction := ⟨hB3⟩
  have : G23Leaf LeafMStruct := ⟨hMS⟩
  have : G23Leaf LeafLoc5 := ⟨hL5⟩
  have : G23Leaf LeafTriLetters := ⟨hTri⟩
  have : G23Leaf LeafTriCosetBound := ⟨hCB⟩
  have : G23Leaf LeafTriNative := ⟨hTN⟩
  have : G23Leaf LeafGhatInvolCent := ⟨hGI⟩
  intro G _ _ T H H₁ H₂ M hctx
  obtain ⟨e, hL⟩ := exists_lettersH hctx
  have hS : Setup G T H H₁ H₂ M e := ⟨hctx, hL⟩
  have hF : HFacts H H₁ H₂ e := hS.hFacts
  have hO : OneClass e := hS.oneClass hF hS.zFitting
  obtain ⟨M₁, M₂, hv₁, hv₂⟩ := hS.exists_vertexCores hF hO
  obtain ⟨Pb, Np, Nm, hpb, hnp, hnm⟩ := hS.exists_pbarMixed hF hO
  have hfour : FourClasses e := hS.fourClasses hF hO hv₁ hv₂ hpb hnp hnm
  have hcor : Cor37 e M₁ M₂ Pb := hS.cor37 hF hO hv₁ hv₂ hpb
  have hL3 : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm := ⟨hv₁, hv₂, hpb, hnp, hnm, hfour, hcor⟩
  have hPb9 : Nat.card Pb ≠ 9 := by
    intro h9
    obtain ⟨hD, hsyl⟩ := hS.stepALocal hF hO hL3 h9
    have : Fintype G := Fintype.ofFinite G
    obtain ⟨χ, hχ⟩ := exists_hCharTable hctx.one hL
    obtain ⟨X₁, X₂, ε₁, ε₂, hcoh⟩ := exists_suzukiCoherent hD hχ
    obtain ⟨x₁, x₂, har⟩ := exists_stepAArith hS hF hO hD hχ hcoh
    exact false_of_stepAArith har hsyl
  have hPb81 : Nat.card Pb = 81 := by
    rcases hcor.cases with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact absurd h hPb9
    · exfalso
      obtain ⟨hab₁, hab₂⟩ := hS.b27Abelian hF hO hL3 h
      obtain ⟨W₁, Mf, t', hst⟩ := hS.b27Normalizer hF hO hL3 h hab₁ hab₂
      exact hS.b27Contradiction hF hO hL3 h hab₁ hab₂ hst
    · exact h
  have hms : MStruct e M₁ M₂ := hS.mStruct hF hO hL3 hPb81
  obtain ⟨W, hloc5⟩ := hS.exists_loc5 hF hO hL3 hPb81 hms
  obtain ⟨f, hf, hfK⟩ := hS.triLetters hF hO hL3 hloc5
  exact g23AtInv_tail hsimp hcard card_PG_tri_le exists_native_tri hconj
    (fun y hy => ghat_card_centralizer_invol hy) hlie hSL hctx f hf hfK

end CFSG.GH74.QTGen4.Recog.G23.P7
