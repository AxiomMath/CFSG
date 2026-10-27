module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HSFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.RuFive

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.HardMathSupport.Dickson.I271

theorem kdSporC_HS_five
    {Z : Type} [Group Z] {K : Subgroup Z} [K.Normal]
    (hsK : P64IsSpor .HS ↥K) (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian 5 B) (hBc : Nat.card B = 5 ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * 5)) :
    W = ⊥ := by
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have f : ↥K ≃* ↥CFSG.RankThree.Native.hs100P :=
    (eK.trans b.symm).trans CFSG.RankThree.Native.hs100Equiv
  exact kdSporC_eq_bot_of_model Nat.prime_five hC f
    (fun R Y hR hR9 hY3 hRY => hsFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) hB hBc hBW hW

theorem kdSporC_Ru_five
    {Z : Type} [Group Z] {K : Subgroup Z} [K.Normal]
    (hsK : P64IsSpor .Ru ↥K) (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian 5 B) (hBc : Nat.card B = 5 ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * 5)) :
    W = ⊥ := by
  obtain ⟨eK⟩ := hsK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have f : ↥K ≃* ↥CFSG.Sporadic.RuSchreier.ruP :=
    (eK.trans b.symm).trans CFSG.Sporadic.RuSchreier.ruEquivP
  exact kdSporC_eq_bot_of_model Nat.prime_five hC f
    (fun R Y hR hR9 hY3 hRY => ruFive_noSig R hR hR9 Y
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hY3) hRY) hB hBc hBW hW

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
