module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangSeven
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairTwE6
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.F4Neg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.E6Five
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.TriD4Five

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_adjointE8_five_split (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K - 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E8 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_five e8FiveToralPlane_proved
    (steinbergLang_langTorusPlaneBalance_E8_five_split hsub hin hsu htw hex) K h5 hq

theorem innerPlaneBalance_adjointE8_five_neg (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K + 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E8 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_five e8FiveToralPlane_proved
    (steinbergLang_langTorusPlaneBalance_E8_five_neg hsub hin hsu htw hex) K h5 hq

section Catalogue


theorem innerPlaneBalance_adjointF4_five (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K - 1 ∨ 5 ∣ Nat.card K + 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.F4 K) := by
  rcases hq with h | h
  · exact innerPlanes_adjointF4_of_dvd_sub_one' Nat.prime_five le_rfl h
  · obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
    exact innerPlaneBalance_adjointF4_of_negBalance Nat.prime_five le_rfl
      (langTorusPlaneBalance_neg_dvd_add_one (Or.inl rfl) f4Neg_smul Nat.prime_five le_rfl hsub
        hin hsu htw hex) K h

theorem innerPlaneBalance_trialityD4_five (q : TauCeti.PrimePower)
    (hv : (excIndex .trialityD4 q).Valid) (hq : q.p ≠ 5)
    (h : 5 ∣ q.card - 1 ∨ 5 ∣ q.card + 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .trialityD4 q, hv⟩) := by
  rcases h with h | h
  · exact innerPlaneBalance_trialityD4_one_odd q hv Nat.prime_five le_rfl hq.symm
      (orderOf_natCast_zmod_five_of_dvd h (by
        rw [TauCeti.PrimePower.card_def]
        exact Nat.one_le_pow _ _ q.prime_p.pos)) t1_pieces
  · exact innerPlaneBalance_trialityD4_two_odd q hv Nat.prime_five le_rfl hq.symm
      (CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_natCast_zmod_five_of_dvd_add_one h)
      t1_pieces

theorem innerPlaneBalance_E6_five_dvd_add_one (q : TauCeti.PrimePower)
    (hv : (excIndex .E6 q).Valid) (hq : q.p ≠ 5) (h : 5 ∣ q.card + 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .E6 q, hv⟩) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at h
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE6_five_of_dvd_add_one
    (langTorusPlaneBalance_E6_two_five_of_components hsub hin hsu htw hex) K h)

theorem innerPlaneBalance_twistedE6_five_dvd_sub_one (q : TauCeti.PrimePower)
    (hv : (excIndex .twistedE6 q).Valid) (hq : q.p ≠ 5) (h : 5 ∣ q.card - 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .twistedE6 q, hv⟩) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at h
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_twistedE6_five_of_dvd_sub_one
    (twistedE6LangTorusPlaneBalance_one_five_of_components hsub hin hsu htw hex) q.prime_p
    q.exponent_pos K hK σ hσ h)

end Catalogue

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
