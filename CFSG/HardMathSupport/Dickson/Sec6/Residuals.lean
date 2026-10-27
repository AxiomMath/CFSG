module

public import CFSG.HardMathSupport.Dickson.Sec6.Reduction
public import CFSG.HardMathSupport.Dickson.Sec6.Heis
public import CFSG.HardMathSupport.Dickson.Sec6.I923

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

@[expose] def Up34Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G), CFSG.IsKGroup ↥X →
    GLAPComponent 3 X K → ∀ b : G, b ∈ X → ∀ hbN : b ∈ Subgroup.normalizer (K : Set G),
    b ^ 3 = 1 → b ∉ dQ K → ∀ J : Subgroup G,
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J →
    IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
      (IsCatalogLieIso (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) IsL364Index ∧
        ¬ IsInnDiagThree (barAut 3 K ⟨b, hbN⟩)) ∨
      IsCatalogLieIso (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) Is3D44Index ∨
      (IsCatalogLieIso (barOf 3 K) IsD44Index ∧ Subgroup.center (barOf 3 K) = ⊥)

@[expose] def Gen3D4Statement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    IsCatalogLieIso (Y ⧸ Subgroup.center Y) Is3D44Index →
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A →
      ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S

theorem input25_4FactsNarrow_of (hup34 : Up34Statement) (hgen : Gen3D4Statement) :
    GenL3.Input25_4FactsNarrow :=
  ⟨hup34, l364Rank3Heis_holds, hgen⟩


section Final

open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns CFSG.Yardstones.M67c2c3e09a6b

theorem sec6Out_of_open_residuals
    (h03 : LocalTwoBalanceThreeFive)
    (h04 : CFSG.HardMathSupport.Timmesfeld.LocalTwo.LocalTwoBalanceSimpleGtFive)
    (h05 : SporadicBpResiduals) (h09 : I271OpenFamilies)
    (hup34 : Up34Statement) (hgen : Gen3D4Statement) (hLie : I923.Y923_LieRest)
    (h1431 : Input14_31_4 innAutDerivedVocab) :
    Sec6Out :=
  sec6Out_of_slots_and_residuals h03 h04 h05 h09 (input25_4FactsNarrow_of hup34 hgen)
    (I923.input9_2_3_of_lieRest hLie) h1431

end Final

end CFSG.HardMathSupport.Dickson.Sec6
