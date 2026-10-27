module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistOmega
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNN

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Twist

variable {X : Type} [Group X] [Finite X]

theorem input22_4_tw {K B : Subgroup X} (hH : I271Hyp 3 K B)
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3)
    (hrel : ∀ c ∈ B, c ∉ Subgroup.normalizer (K : Set X) →
      ∀ z ∈ K ⊓ Subgroup.centralizer (K : Set X),
        z * (c * z * c⁻¹) * (c * c * z * c⁻¹ * c⁻¹) = 1)
    (hgen : K ≤ ⨆ (F : Subgroup X)
      (_ : F ≤ B ⊓ Subgroup.normalizer (K : Set X) ∧
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) ≤ 3 * Nat.card F), i224Tw K F) :
    IsInGMinusOne 3 B K := by
  classical
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hKc : CFSG.Open.IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  have hBA : Nat.card B = 3 * Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (K : Set X)) (K := B)
    rw [hidx, inf_comm] at h
    exact h.symm
  have hctx : I224CtxT 3 B K :=
    { hp3 := rfl
      prime := Nat.prime_three
      elem := hBel
      quasi := hq
      dist := fun g _ g' _ hne => i224_comm_cj hKc g g' hne
      index := hBA
      rel := hrel
      gen := hgen }
  have hΩ := i224T_omega hctx
  have hKeq : bClosure B K = i224K B K := by
    apply le_antisymm
    · refine iSup₂_le fun b hb x hx => ?_
      refine Subgroup.mem_iSup_of_mem b⁻¹ (Subgroup.mem_iSup_of_mem (B.inv_mem hb) ?_)
      rw [mem_i224Cj]
      have := mem_gLBConj.1 hx
      simpa using this
    · refine iSup₂_le fun b hb x hx => ?_
      refine Subgroup.mem_iSup_of_mem b⁻¹ (Subgroup.mem_iSup_of_mem (B.inv_mem hb) ?_)
      rw [mem_gLBConj]
      have := mem_i224Cj.1 hx
      simpa using this
  unfold IsInGMinusOne
  rw [hKeq]
  apply le_antisymm
  · refine hΩ.trans (iSup₂_le fun E hE => ?_)
    have hEB := hE.1
    have hEel : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hBel hEB
    have hrk : CFSG.Open.pRank 3 B - 1 ≤ CFSG.Open.pRank 3 E :=
      (i224_card_le_iff Nat.prime_three hBel hEel).2 hE.2
    exact i224_le_gammaPrimeIn hEB hrk
  · unfold gammaPrimeIn
    exact iSup₂_le fun E _ => inf_le_left

theorem nn_caseA_of_twist {K B : Subgroup X} (hH : I271Hyp 3 K B)
    (hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3)
    (hrel : ∀ c ∈ B, c ∉ Subgroup.normalizer (K : Set X) →
      ∀ z ∈ K ⊓ Subgroup.centralizer (K : Set X),
        z * (c * z * c⁻¹) * (c * c * z * c⁻¹ * c⁻¹) = 1)
    (hgen : K ≤ ⨆ (F : Subgroup X)
      (_ : F ≤ B ⊓ Subgroup.normalizer (K : Set X) ∧
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) ≤ 3 * Nat.card F), i224Tw K F) :
    I271CaseA 3 K B :=
  ⟨hH.rank_four, isInGOne_of_isInGMinusOne_of_four_le hH.rank_four
    (input22_4_tw hH hidx hrel hgen)⟩

end Twist

end CFSG.HardMathSupport.Solomon.Coordinator
