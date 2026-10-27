module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113Claims

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

namespace D

variable {G : Type} [Group G] [Finite G]

theorem rcfg_of_sylow {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) (hA : Claim113A (M := M) E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G))
    {R : Subgroup G} (hR : IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R) (hQR : Q ≤ R) :
    RCfg E A e K Q R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := Ctx.of_cfg h hA
  have hEJ : E = thompsonJ 3 Q := hA.2.2.2.2.2.1
  have hQC : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q := h.hQ.1
  have hQN : Q ≤ Subgroup.normalizer (E : Set G) :=
    Lemma113f.le_normalizer_of_eq_thompsonJ hEJ
  obtain ⟨R₀, hR₀, -, hR₀8⟩ := Lemma113f.exists_sylow_three_eight_of_index c.he3 h.he.2 hQN hQC
    (c.card_Q hB) (c.index_eq hB)
  exact ⟨c, hB, hR, hQR, (card_eq_of_isSylowIn hR₀ hR).trans hR₀8⟩

end D

end Lemma113Claims

theorem pieceD_subR4_holds : Lemma113g.PieceD_SubR4 := by
  intro G _ _ m B M E A a e K Q h _ R hR hQR
  have h0 := lemma113_ii_piece0_holds h
  have hA := lemma113_ii_pieceA_of_inputs' Lemma113Claims.hC113 h h0
  have hB := lemma113_ii_pieceB_holds' h hA
  have r := Lemma113Claims.D.rcfg_of_sylow h hA hB hR hQR
  have hΩ := r.omega_le_E h.ha.1 (Lemma113Claims.normalizer_le_M h) h0
  refine ⟨R ⊓ Lemma113Claims.N0 E (Q ⊓ K), inf_le_left, ?_, r.E_le_T, ?_, hΩ⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (r.R_normalizes_T g.2) n).1 hn
  · have hle : (R ⊓ Lemma113Claims.N0 E (Q ⊓ K) : Subgroup G) ≤ R := inf_le_left
    have hmul := Subgroup.relIndex_mul_card (H := R ⊓ Lemma113Claims.N0 E (Q ⊓ K)) (K := R)
    rw [inf_eq_left.2 hle, r.card_T, r.hR8] at hmul
    have hidx : (R ⊓ Lemma113Claims.N0 E (Q ⊓ K)).relIndex R = 3 := by
      have : (R ⊓ Lemma113Claims.N0 E (Q ⊓ K)).relIndex R * 3 ^ 7 = 3 * 3 ^ 7 := by
        rw [hmul]; norm_num
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    rw [← hidx]
    rfl

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
