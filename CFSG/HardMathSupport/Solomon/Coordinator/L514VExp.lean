module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514VExpCore
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VExpT
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldHolds
import CFSG.HardMathSupport.Solomon.Proving.PSL2CentSolvableProof
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (GLAPComponent GLAPPrimeCore)
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.LocalAnalysis.GLTheoremB

theorem inputL2exp_of_facts (h1 : L2Aut3Classification) (h0 : L2CentreThree) (hC : PSL2CentSolvable) : InputL2exp innAutDerivedVocab := by
  intro G _ _ K g h s r0 hQ hs hgN hhN hg3 hh3 hgh hnot J hJ hr
  have hO : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hX : K ⊓ Cs g ⊓ Cs h ≤ K := inf_le_left.trans inf_le_left
  obtain ⟨J₁, hJ₁, hJ₁J⟩ := exists_comp_subgroupOf hX hJ
  have hcomp := glaPComponent_map Nat.prime_three
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) (coprime_ker_mk K _) hJ₁
  rw [l514vexp_map_inf_centralizer_two hgN hhN hg3 hh3 hgh] at hcomp
  subst hJ₁J
  have hr' := l2fld_isTypeL2_of_mulEquiv (liftEquiv J₁) hr
  have hcomm : barAut 3 K ⟨g, hgN⟩ * barAut 3 K ⟨h, hhN⟩ = barAut 3 K ⟨h, hhN⟩ * barAut 3 K ⟨g, hgN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hgh)
  refine l2exp_core Proving.l2OrderUnique_holds h1 l2FieldFixed_holds h0 hC hQ hO hs
    (barAut_pow_three hgN hg3) (barAut_pow_three hhN hh3) hcomm (fun y hy => hnot ⟨hgN, ?_⟩) hcomp hr'
  exact Subgroup.mem_sup_left ⟨y, hy⟩

theorem inputL2exp_holds :
    InputL2exp innAutDerivedVocab :=
  inputL2exp_of_facts l2Aut3Classification_holds l2CentreThree_holds
    HardMathSupport.Solomon.Proving.psl2CentSolvable_holds

end CFSG.HardMathSupport.Solomon.Coordinator
