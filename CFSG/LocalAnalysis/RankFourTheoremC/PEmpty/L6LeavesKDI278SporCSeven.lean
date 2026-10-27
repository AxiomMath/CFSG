module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeSeven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.Schreier.Fi24Schreier

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.HardMathSupport.Dickson.I271

theorem kdSporC_balance_of_sevenModel {X : Type} [Group X] [Finite X] [Fact (Nat.Prime 7)]
    {Q : Subgroup X} {z : X} {gens : Set X} (D : SevenModel X 7 Q z gens)
    (hcen : Subgroup.center X = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 2) :
    ∀ R Y : Subgroup (MulAut X), CFSG.Open.IsElemAbelian 7 R → Nat.card R = 7 ^ 2 →
      ¬ 7 ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥ :=
  fun R Y hR hR9 hY3 hRY =>
    SevenModel.noSig (by norm_num) D hcen hout R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY

theorem kdSporC_Fi24_seven
    {Z : Type} [Group Z] [Finite Z] {K : Subgroup Z} [K.Normal]
    (hsK : P64IsSpor .Fi24Prime ↥K) (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian 7 B) (hBc : Nat.card B = 7 ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * 7)) :
    W = ⊥ := by
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have b₀ : CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group := b
  have g : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime := eK.trans b₀.symm
  have hKout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) = 2 :=
    (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence g).toEquiv).trans
      CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime
  have f := g.trans CFSG.Sporadic.Fi24.fi24EquivJ
  have hJout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥CFSG.Sporadic.Fi24.J) ≤ 2 :=
    ((Nat.card_congr (@CFSG.ComponentClassification.OuterAutomorphisms.equivalence ↥K
      ↥CFSG.Sporadic.Fi24.J _ (Subgroup.toGroup CFSG.Sporadic.Fi24.J) f).toEquiv).symm.trans
        hKout).le
  have hcen : Subgroup.center ↥CFSG.Sporadic.Fi24.J = ⊥ :=
    kdSporC_center_eq_bot_of_equiv f (kdSporC_center_eq_bot hC)
  haveI : Finite ↥CFSG.Sporadic.Fi24.J := Finite.of_equiv ↥K f.toEquiv
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hbal := kdSporC_balance_of_sevenModel fi7_sevenModel hcen hJout
  exact @kdSporC_eq_bot_of_model 7 (by norm_num) Z _ K _ hC ↥CFSG.Sporadic.Fi24.J
    (Subgroup.toGroup CFSG.Sporadic.Fi24.J) f hbal _ _ hB hBc hBW hW

theorem kdSporC_He_seven
    {Z : Type} [Group Z] {K : Subgroup Z} [K.Normal]
    (hsK : P64IsSpor .He ↥K) (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian 7 B) (hBc : Nat.card B = 7 ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * 7)) :
    W = ⊥ := by
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have f : ↥K ≃* ↥CFSG.Sporadic.HeldB.heP :=
    (eK.trans b.symm).trans CFSG.Sporadic.HeldB.heEquivP
  exact kdSporC_eq_bot_of_model (by norm_num : Nat.Prime 7) hC f
    (fun R Y hR hR9 hY3 hRY => heSeven_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 hY3) hRY) hB hBc hBW hW

theorem kdSporC_ON_seven
    {Z : Type} [Group Z] [Finite Z] {K : Subgroup Z} [K.Normal]
    (hsK : P64IsSpor .ONan ↥K) (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian 7 B) (hBc : Nat.card B = 7 ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * 7)) :
    W = ⊥ := by
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have f : ↥K ≃* ↥CFSG.ONSchreier.Pv := (eK.trans b.symm).trans CFSG.ONSchreier.onEquivPv
  have hPout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥CFSG.ONSchreier.Pv) ≤ 2 :=
    Nat.le_of_dvd two_pos CFSG.Sporadic.SteinbergBI.card_outer_Pv_dvd_two
  have hcen : Subgroup.center ↥CFSG.ONSchreier.Pv = ⊥ :=
    kdSporC_center_eq_bot_of_equiv f (kdSporC_center_eq_bot hC)
  haveI : Finite ↥CFSG.ONSchreier.Pv := Finite.of_equiv ↥K f.toEquiv
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hbal := kdSporC_balance_of_sevenModel on7_sevenModel hcen hPout
  exact kdSporC_eq_bot_of_model (by norm_num : Nat.Prime 7) hC f hbal hB hBc hBW hW

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
