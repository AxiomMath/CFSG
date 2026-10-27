module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChainE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDRecog

open CompsPTwoDDatumG

section Odd


theorem twoDChainRecog_odd {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r]
    [IsAlgClosed L] {e m : ℕ} (hr2 : r ≠ 2) (he : 0 < e) (hm4 : 4 ≤ m) (hq5 : 5 ≤ r ^ e) :
    TwoDChainRecog r L e m := by
  classical
  intro G _ ρ Φ C hρinj hcomm hfr hΦ0 hΦ1 hΦ2 hC
  obtain ⟨bb, cc, hirr, ⟨KD⟩⟩ := CompsPTwoDKlein.exists_kleinData_frob (k := L) (p := r) he hr2
  haveI hFfin : Finite ↥(frobeniusFixedField L r e) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_frobeniusFixedField he]
      exact (pow_pos (Fact.out : r.Prime).pos _).ne')
  have hFcard : Nat.card ↥(frobeniusFixedField L r e) = r ^ e := card_frobeniusFixedField he
  have hq4 : 4 ≤ Nat.card ↥(frobeniusFixedField L r e) := by
    rw [hFcard]
    omega
  have hadm : StatedLieAdmissible .POmegaMinus m r e := ⟨Fact.out, he, hm4⟩
  obtain ⟨hlie, -⟩ := CompsPTwoDChain.lieModel_of_chain (k := L) (G := G) (n := m) (p := r)
    (f := e) hadm hr2 hFcard hq4 KD hirr (frobeniusFixedField L r (e * 2)).subtype ρ hρinj hcomm
    hfr Φ hΦ0 hΦ1 hΦ2 C hC
  exact hlie

end Odd

section All

@[expose] def TwoDChainRecogAll (L : Type) [Field L] [IsAlgClosed L] (Q : ℕ → ℕ → Prop) : Prop :=
  ∀ (r : ℕ) [Fact r.Prime] [CharP L r] (e m : ℕ), 0 < e → 5 ≤ m → Q r (r ^ e) →
    TwoDChainRecog r L e m


theorem twoDChainRecogAll_even_or_five (L : Type) [Field L] [IsAlgClosed L] :
    TwoDChainRecogAll L (fun r q => r = 2 ∨ 5 ≤ q) := by
  intro r hr hch e m he hm5 hq
  by_cases hr2 : r = 2
  · subst hr2
    exact CompsPTwoDChainE.twoDChainRecog_even he (by omega)
  · exact twoDChainRecog_odd hr2 he (by omega) (hq.resolve_left hr2)

end All

end CompsPTwoDRecog

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
