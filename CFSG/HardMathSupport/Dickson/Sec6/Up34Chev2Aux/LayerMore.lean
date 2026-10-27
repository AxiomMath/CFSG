module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Up34Chev2

theorem barOf_equiv_of_simple {P : Type} [Group P] {A : Subgroup P}
    (hA : IsSimpleGroup ↥A) (hAq : CFSG.Open.IsQuasisimple (barOf 3 A)) :
    Nonempty (barOf 3 A ≃* ↥A) := by
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
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))⟩

theorem noL34Layer_of_fixed_equiv {P : Type} [Group P] [Finite P] (ψ : MulAut P) {X : Type}
    [Group X] (e : ↥(fixSubgroup ψ) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour X) : NoL34Layer ψ := by
  haveI : IsSimpleGroup ↥(fixSubgroup ψ) := e.isSimpleGroup
  refine noL34_of_simple_normal_comm ψ (fixSubgroup ψ) le_rfl ?_ inferInstance ?_ ?_
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  · intro h
    exact hL34 (IsLThreeFour.of_mulEquiv e h)

theorem noL34Layer_of_simple_commutator {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hSD : S = ⁅fixSubgroup ψ, fixSubgroup ψ⁆) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour ↥S) : NoL34Layer ψ := by
  refine noL34_of_simple_normal_comm ψ S ?_ hSD.ge hs hnab hL34
  rw [hSD]
  exact Subgroup.commutator_le.2 fun a ha b hb =>
    (fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ((fixSubgroup ψ).mul_mem ha hb)
      ((fixSubgroup ψ).inv_mem ha)) ((fixSubgroup ψ).inv_mem hb)

theorem noL34Layer_of_normal_simple {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (J : Subgroup P) (hJC : J ≤ fixSubgroup δ) [(J.subgroupOf (fixSubgroup δ)).Normal]
    (hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥J) : NoL34Layer δ := by
  intro A hA hT
  have hq : CFSG.Open.IsQuasisimple ↥J := isQuasisimple_of_simple_up34 hnab
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
  obtain ⟨e⟩ := barOf_equiv_of_simple hs hAq
  exact hL34 (IsLThreeFour.of_mulEquiv e hT)

theorem noL34Layer_of_fixed_normal_simple {P : Type} [Group P] [Finite P] (δ : MulAut P)
    (N J : Subgroup P) (hfix : fixSubgroup δ = N) (hJN : J ≤ N) [(J.subgroupOf N).Normal]
    (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    (hs : IsSimpleGroup ↥J) (hnab : ∃ a b : ↥J, a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥J) : NoL34Layer δ := by
  subst hfix
  exact noL34Layer_of_normal_simple δ J hJN hsol hs hnab hL34

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
