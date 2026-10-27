module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBMain
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

section Outer

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem t6psub_innAutDerived_le (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    innAutDerived (primeFormP h (idGram K n)) ≤ primeFormD h (idGram K n) := by
  refine sup_le ?_ ?_
  · intro α hα
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP (h := h) (idGram K n) α).1 hα
    exact ⟨_, rfl⟩
  · rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact OuterDerived.commutator_mem_primeFormD h hn hq a b

end Outer

@[expose] def FamPsuBadThree : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => FamPsuBadRest t n p f ∧ n = 3

theorem y1431_noCfg_psuBadThree (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431NoCfgAt FamPsuBadThree := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hdiv, hn6⟩, rfl⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  haveI := h.finite
  haveI : Finite (GL (Fin 3) K) :=
    Finite.of_injective (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) Units.val_injective
  haveI : Finite (primeFormP h (idGram K 3)) := inferInstance
  have cS := c.descend e0
  have hq2 : p ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f + 1 := (Nat.dvd_gcd_iff.1 hdiv).2
    have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hadm.2.1; omega)
    omega
  have hA : ∀ a ∈ Â.map (descendHom e0),
      ∃ B : primeFormUnitary h (idGram K 3), primeFormConjHom h (idGram K 3) B = a := by
    rintro _ ⟨a', ha', rfl⟩
    have h1 : MulAut.congr e0 (centerDescend Y a') ∈ innAutDerived (primeFormP h (idGram K 3)) :=
      (mem_innAutDerived_congr e0).2 (centerDescend_mem_innAutDerived (c.mem_innAutDerived ha'))
    exact t6psub_innAutDerived_le h le_rfl (fun hc => hq2 hc.2) h1
  exact s1431_false_psu_bad_three hO h hp3 hq2 cS (ten_le_of_cube hq0 hqq) hA

end CFSG.HardMathSupport.Dickson.Sec6.I1431
