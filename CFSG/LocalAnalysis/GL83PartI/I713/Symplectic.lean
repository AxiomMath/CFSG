module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (perfect_symplectic_central_quotient_outer_prime_control)
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  refine Group.isPerfect_def.2 ?_
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  · exact h

theorem outClauseFor_classical_PSp {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel S .PSp n p f) : OutClauseFor S := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, -, hK, ⟨e⟩⟩ := h
  have : Group.IsPerfect S := isPerfect_of_simple_nonabelian hnonab
  have hJ : Nonempty (S ⧸ Subgroup.center S ≃* StatedProj (StatedSp n K)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnonab)).trans
      QuotientGroup.quotientBot).trans e⟩
  have hctl := perfect_symplectic_central_quotient_outer_prime_control hp hf hn hK S hJ
  intro q hq hq2 _
  have hq1 : CFSG.pRank q (Outer S) ≤ 1 := hctl.2.1 q hq hq2
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top q (Outer S)] at hq1

end GL83.I713
