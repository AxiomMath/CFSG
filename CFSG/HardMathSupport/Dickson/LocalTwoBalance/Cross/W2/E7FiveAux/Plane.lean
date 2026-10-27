module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Steinberg
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangSeven

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

set_option linter.unusedSectionVars false

section Toral


theorem planesToralBar_E7_five : PlanesToralBar Tag.E7 5 :=
  planesToralBar_five_of_chainBlock
    (fun _ hγ => EvenOddRadical.iform_self_eq_two (Or.inr (Or.inr (Or.inl rfl))) hγ)
    chainBlockToral_E7_four fun _ _ a ha =>
      (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five a ha).le

theorem langToralPlane_E7_five : LangToralPlane Tag.E7 5 :=
  langToralPlane_of_bar Nat.prime_five planesToralBar_E7_five

section Balance


theorem steinbergLang_langTorusPlaneBalance_E7_five_split
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E7) :
    LangTorusPlaneBalance Tag.E7 w 5 fun q => 5 ∣ q - 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inl rfl) Nat.prime_five
    (fun _ _ b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five b hb).le)
    e7Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

theorem steinbergLang_langTorusPlaneBalance_E7_five_neg
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) (w : WeylGroup Tag.E7) :
    LangTorusPlaneBalance Tag.E7 w 5 fun q => 5 ∣ q + 1 :=
  steinbergLang_langTorusPlaneBalance_E78 (Or.inl rfl) Nat.prime_five
    (fun _ _ b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five b hb).le)
    e7Neg_smul (fun q hq2 hQ => ⟨by omega, by omega⟩) hsub hin hsu htw hex w

section Inner


theorem innerPlaneBalance_adjointE7_five_split (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K - 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E7 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_five langToralPlane_E7_five
    (steinbergLang_langTorusPlaneBalance_E7_five_split hsub hin hsu htw hex) K h5 hq

theorem innerPlaneBalance_adjointE7_five_neg (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K + 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E7 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_five langToralPlane_E7_five
    (steinbergLang_langTorusPlaneBalance_E7_five_neg hsub hin hsu htw hex) K h5 hq

section Cat


theorem innerPlaneBalance_catE7_five_split (q : TauCeti.PrimePower)
    (hv : (excIndex .E7 q).Valid) (h : 5 ∣ q.card - 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at h
  have h5 : ¬ 5 ∣ Nat.card K := by
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE7_five_split K h5 h)

theorem innerPlaneBalance_catE7_five_neg (q : TauCeti.PrimePower)
    (hv : (excIndex .E7 q).Valid) (h : 5 ∣ q.card + 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .E7 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at h
  have h5 : ¬ 5 ∣ Nat.card K := by omega
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE7_five_neg K h5 h)

end Cat

end Inner

end Balance

end Toral

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
