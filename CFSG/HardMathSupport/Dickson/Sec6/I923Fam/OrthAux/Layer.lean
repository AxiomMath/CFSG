module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

theorem noL2Layer_of_congr {P P' : Type} [Group P] [Finite P] [Group P'] (e : P ≃* P')
    {ψ : MulAut P} (h : NoL2Layer (MulAut.congr e ψ)) : NoL2Layer ψ := by
  intro A hA r hr hT
  haveI : Finite P' := Finite.of_equiv P e.toEquiv
  have hker : (e : P →* P').ker ≤ Subgroup.center P := by
    intro x hx
    have hx1 : x = 1 := e.injective (by simpa using hx)
    rw [hx1]
    exact one_mem _
  have hαψ : ∀ y, (e : P →* P') (ψ y) = (MulAut.congr e ψ) ((e : P →* P') y) := fun y => by
    simp [MulAut.congr_apply]
  obtain ⟨A', hA', hT'⟩ :=
    typeL2_barOf_of_central (e : P →* P') e.surjective hker ψ (MulAut.congr e ψ) hαψ hA hT
  exact h A' hA' r hr hT'

theorem noL2Layer_of_normal_simple {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (J : Subgroup P) (hJC : J ≤ fixSubgroup δ) [(J.subgroupOf (fixSubgroup δ)).Normal]
    (hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥J) : NoL2Layer δ := by
  intro A hA r hr hT
  have hq : CFSG.Open.IsQuasisimple ↥J := isQuasisimple_of_simple hnab
  have hAD : A ≤ fixSubgroup δ := hA.1
  have hAJ : A ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJC hsol
      hAD (glaPComponent_perfect hA)
  have hsn : IsSubnormal A J := isSubnormal_of_le_of_le hA.2.1 hAJ hJC
  have hAeq : A = J :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))
  exact hL2 r hr (l2fld_isTypeL2_of_mulEquiv e hT)

theorem noL2Layer_of_fix_eq {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (N J : Subgroup P) (hfix : fixSubgroup δ = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL2 : ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r ↥J) : NoL2Layer δ := by
  subst hfix
  exact noL2Layer_of_normal_simple δ J hJN hsol hs hnab hL2

end CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
