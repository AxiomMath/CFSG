module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.Quasithin.H13.A5W1620Tc
public import CFSG.HardMathSupport.Solomon.Proving.SU3CentreScalars

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.HardMathSupport.Solomon

def slQuotEquivProj (K : Type) [Field K] :
    (↥(StatedSL 3 K) ⧸ Subgroup.center ↥(StatedSL 3 K)) ≃* StatedProj (StatedSL 3 K) :=
  QuotientGroup.quotientMulEquivOfEq
    (by exact CFSG.Quasithin.H13.A5.center_statedSL_eq_statedScalars 3 K)

def suQuotEquivProj {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    (↥(StatedSU 3 q K) ⧸ Subgroup.center ↥(StatedSU 3 q K)) ≃* StatedProj (StatedSU 3 q K) :=
  QuotientGroup.quotientMulEquivOfEq (center_statedSU_three_eq_scalars hK)

theorem isLThreeEpsOrON_of_localBalance {X : Type*} [Group X]
    (h : LocalBalance.IsLThreeEpsOrON X) :
    LocalBalance.Lemma55Ns.IsLThreeEpsOrON X := by
  rcases h with ⟨K, fld, fin, hK, ⟨φ⟩⟩ | ⟨K, fld, fin, q, hKq, hq, hq8, ⟨φ⟩⟩ | hON
  · exact Or.inl ⟨K, fld, fin, hK, ⟨φ.trans (slQuotEquivProj K)⟩⟩
  · exact Or.inr (Or.inl ⟨K, fld, fin, q, hKq, hq, hq8, ⟨φ.trans (suQuotEquivProj hKq)⟩⟩)
  · exact Or.inr (Or.inr hON)

theorem input23_26_of_lemma55 (h : LocalBalance.Lemma55Ns.Input23_26) :
    LocalBalance.Input23_26 := by
  intro Y _ _ _ 𝒮 hcomp hLT E hE hcard hnorm
  exact h Y (⨆ J ∈ 𝒮, J) E 𝒮
    (fun K hK => ⟨hcomp K hK, isLThreeEpsOrON_of_localBalance (hLT K hK)⟩)
    rfl hE hcard hnorm

end CFSG.HardMathSupport.Solomon.Proving
