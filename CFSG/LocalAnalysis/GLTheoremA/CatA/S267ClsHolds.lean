module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAtLU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsFinalLanes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFinalHeads
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

section Lanes


theorem badClsAt_twistedA_holds (hGA : GriessAllModelsStatement) {n : ℕ}
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) :
    BadClsAt ⟨.twistedA n Q, hv⟩ :=
  badClsAt_twistedA concA_caseL_lu hGA hv

theorem badClsAt_A_holds (hGA : GriessAllModelsStatement) {n : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (hn : 2 ≤ n) : BadClsAt ⟨.A n Q, hv⟩ :=
  badClsAt_A concA_caseL_lin hGA hv hn

end Lanes

section Assembly


theorem s267FactBadCls_of_twE6Three
    (h2E6threePlus : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid),
        (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) →
        p ∣ Q.card ^ 2 - 1 → p = 3 → 3 ∣ Q.card + 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B) :
    S267FactBadCls :=
  s267FactBadCls_of_lanes badClsAt_A_holds badClsAt_twistedA_holds
    (BadExc.s267FactBadExcCore_of_heads h2E6threePlus)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
