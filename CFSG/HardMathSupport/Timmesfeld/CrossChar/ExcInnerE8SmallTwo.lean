module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodA2E8
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyE8Three

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false

theorem primePower_p_eq_two {q : TauCeti.PrimePower} (hq2 : q.card = 2) : q.p = 2 := by
  rw [TauCeti.PrimePower.card_def] at hq2
  exact ((Nat.Prime.pow_eq_iff Nat.prime_two).1 hq2).1

theorem orderOf_two_zmod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

section Rows


theorem innerPlaneBalance_two_of_class (k : LieFamily) (hk : IsExceptionalFam k) {p e : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (he : orderOf ((2 : ℕ) : ZMod p) = e)
    {C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgClass k (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = e) C)
    (hrig : ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup (excTag k) L p),
      S.D.q = 2 → S.IsAlgebraic → C L p S → SetupRigid S) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid),
      Subgroup.center (CatT ⟨excIndex k q, hv⟩) = ⊥) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid), q.card = 2 →
      InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩) := by
  intro q hv hq2
  have hpq : p ≠ q.p := by
    rw [primePower_p_eq_two hq2]
    omega
  obtain ⟨L, hF, hA, S, hSq, hAlg, hC, hsyl, ⟨ε⟩⟩ :=
    ha hk q hv p hp ⟨hp7, by rw [hq2]; exact he⟩ hpq
  have hinj := conj_injective_of_mulEquiv ε (conj_injective_of_center_bot (hZ q hv))
  exact InnerPlaneBalance.of_mulEquiv ε
    (innerPlaneBalance_of_langSetup_rigid S hsyl (hrig L S (hSq.trans hq2) hAlg hC) hcp hinj)

theorem innerPlaneBalance_E8_three_two (hcp : LangComponentPieces) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid), q.card = 2 →
      InnerPlaneBalance 7 (CatT ⟨excIndex .E8 q, hv⟩) :=
  innerPlaneBalance_two_of_class .E8 trivial (by norm_num) le_rfl orderOf_two_zmod_seven
    (langTorusAtAlgClass_E8_three frobeniusOnRoots_proved)
    (fun L _ _ S hq hAlg hC => setupRigid_E8_three_two S hAlg hq
      (by rw [hq]; exact orderOf_two_zmod_seven) hC) hcp center_catT_E8_eq_bot

end Rows

end CFSG.HardMathSupport.Timmesfeld.CrossChar
