module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OrderSeven
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.SimplyLacedCover PairFrame
  CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
open scoped commutatorElement
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Order

variable {τ : Tag} {L : Type} [Field L]

theorem orderOf_word_aux (hd : DataChecks τ) {j k : Fin τ.rank}
    (hp : ordPowCheck τ j k = true) (hn : ordNeCheck τ j k = true) (h2 : (2 : L) = 0) :
    orderOf (xUnit τ L k 1 * yUnit τ L k 1 * yUnit τ L j 1 * xUnit τ L j 1) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hu : (((xUnit τ L k 1 * yUnit τ L k 1 * yUnit τ L j 1 * xUnit τ L j 1 :
      (Module.End L (RootModule τ L))ˣ)) : Module.End L (RootModule τ L)) =
      prodOp (genOp τ L j k) ordWord := by
    simp only [Units.val_mul, coe_xUnit, coe_yUnit, prodOp, ordWord, genOp, List.foldl_cons,
      List.foldl_nil, mul_one, mul_assoc]
  refine orderOf_eq_prime ?_ ?_
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hu, prodOp_ord_pow hd j k h2 hp, Units.val_one]
  · intro h1
    have := congrArg (fun u : (Module.End L (RootModule τ L))ˣ => (u : Module.End L (RootModule τ L))) h1
    simp only [Units.val_one] at this
    rw [hu] at this
    exact prodOp_ord_ne hd j k h2 hn this

theorem orderOf_stdWord (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP L 2] :
    ∃ j k : Fin τ.rank, (j : ℕ) = 0 ∧ (k : ℕ) = 2 ∧
      orderOf (xUnit τ L k 1 * yUnit τ L k 1 * yUnit τ L j 1 * xUnit τ L j 1) = 7 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  rcases hτ with rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl, rfl,
      orderOf_word_aux (RootOps.dataChecks Tag.E6) ordPowCheck_E6 ordNeCheck_E6 h2⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl, rfl,
      orderOf_word_aux (RootOps.dataChecks Tag.E7) ordPowCheck_E7 ordNeCheck_E7 h2⟩
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, rfl, rfl,
      orderOf_word_aux (RootOps.dataChecks Tag.E8) ordPowCheck_E8 ordNeCheck_E8 h2⟩

theorem exists_weyl_std_pair (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {j k : Fin τ.rank}
    (hjk : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single k 1) = -1)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hab : iform α β = -1) :
    ∃ w : WeylGroup τ, w • (Pi.single j 1 : Fin τ.rank → ℤ) = α ∧
      w • (Pi.single k 1 : Fin τ.rank → ℤ) = β := by
  have hsl := symmetrizer_diag_one hτ
  have hinj : PairInjective τ := by
    rcases hτ with rfl | rfl | rfl
    exacts [pairInjective_E6, pairInjective_E7, pairInjective_E8]
  have hj := isRoot_single τ j
  have hk := isRoot_single τ k
  have hne : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single k 1 := fun e => by
    rw [e, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne' : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single k 1 := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne₂ : α ≠ β := fun e => by
    rw [e, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  have hne₂' : α ≠ -β := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  exact exists_weyl_pair_iform hinj hj hk hα hβ hne hne' hne₂ hne₂' (hjk.trans hab.symm)

theorem orderOf_pairWord_two [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hab : iform α β = -1) :
    orderOf (pinnedX τ L β 1 * pinnedX τ L (-β) 1 * pinnedX τ L (-α) 1 * pinnedX τ L α 1) = 7 := by
  obtain ⟨j, k, hj0, hk0, hord⟩ := orderOf_stdWord (τ := τ) (L := L) hτ
  have hjk : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single k 1) = -1 := by
    rcases hτ with rfl | rfl | rfl <;>
    · have hj : j = ⟨0, by decide⟩ := Fin.ext hj0
      have hk : k = ⟨2, by decide⟩ := Fin.ext hk0
      subst hj hk
      decide +kernel
  obtain ⟨w, hwj, hwk⟩ := exists_weyl_std_pair hτ hjk hα hβ hab
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hj := isRoot_single τ j
  have hk := isRoot_single τ k
  have e : n * (xUnit τ L k 1 * yUnit τ L k 1 * yUnit τ L j 1 * xUnit τ L j 1) * n⁻¹ =
      pinnedX τ L β 1 * pinnedX τ L (-β) 1 * pinnedX τ L (-α) 1 * pinnedX τ L α 1 := by
    have c1 := canonicalRep_conj_pinnedX_two (L := L) w hj 1
    have c2 := canonicalRep_conj_pinnedX_two (L := L) w (IsRoot.neg hj) 1
    have c3 := canonicalRep_conj_pinnedX_two (L := L) w hk 1
    have c4 := canonicalRep_conj_pinnedX_two (L := L) w (IsRoot.neg hk) 1
    rw [pinnedX_single] at c1 c3
    rw [pinnedX_neg_single] at c2 c4
    rw [smul_neg, hwj] at c2
    rw [smul_neg, hwk] at c4
    rw [hwj] at c1
    rw [hwk] at c3
    calc n * (xUnit τ L k 1 * yUnit τ L k 1 * yUnit τ L j 1 * xUnit τ L j 1) * n⁻¹
        = (n * xUnit τ L k 1 * n⁻¹) * (n * yUnit τ L k 1 * n⁻¹) * (n * yUnit τ L j 1 * n⁻¹) *
            (n * xUnit τ L j 1 * n⁻¹) := by group
      _ = _ := by rw [c1, c2, c3, c4]
  rw [← e]
  rw [← hord]
  exact (MulAut.conj n).orderOf_eq _ |>.trans rfl

end Order

end CFSG.HardMathSupport.Timmesfeld.LangTorus
