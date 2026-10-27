module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsCtx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsGrun
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsI3011
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsB
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsR
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113ClaimsN

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise commutatorElement

namespace Lemma113Claims

variable {G : Type} [Group G] [Finite G]

theorem pieceA_holds : Lemma113_ii_pieceAStatement :=
  lemma113_ii_pieceA_of_inputs' hC113

theorem normalizer_le_M {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (h : Cfg113 G m B M E A a e K Q) : Subgroup.normalizer (E : Set G) ≤ M := by
  have h4 : 2 ≤ CFSG.Open.pRank 3 E := by rw [h.h4]; norm_num
  exact (le_sSup ⟨E, le_rfl, h4, rfl⟩ : Subgroup.normalizer (E : Set G) ≤ GLBCore 3 2 E).trans
    h.pair.1.1.2.clause_d

theorem pieceC_claims_holds : Lemma113_ii_pieceC_Claims := by
  intro G _ _ m B M E A a e K Q h hA hB
  have c := Ctx.of_cfg h hA
  have hEJ : E = thompsonJ 3 Q := hA.2.2.2.2.2.1
  have hQC : IsSylowIn 3 (Subgroup.centralizer ({e} : Set G)) Q := h.hQ.1
  have hQN : Q ≤ Subgroup.normalizer (E : Set G) :=
    Lemma113f.le_normalizer_of_eq_thompsonJ hEJ
  have hG2 : Nat.card ↥Q = 3 ^ 5 := c.card_Q hB
  refine ⟨c.sylow_centralizer_E hB, hG2,
    Lemma113f.exists_sylow_three_eight_of_index c.he3 h.he.2 hQN hQC hG2 (c.index_eq hB), ?_⟩
  intro R hR hQR hR8
  have r : RCfg E A e K Q R := ⟨c, hB, hR, hQR, hR8⟩
  have hΩ := r.omega_le_E h.ha.1 (normalizer_le_M h) (lemma113_ii_piece0_holds h)
  exact (r.thompsonJ_eq hΩ).symm

end Lemma113Claims

theorem lemma113_ii_pieceA_holds' : Lemma113_ii_pieceAStatement := Lemma113Claims.pieceA_holds

theorem lemma113_ii_pieceC_of_inputs' : Lemma113_ii_pieceCStatement :=
  lemma113_ii_pieceC_of Lemma113Claims.pieceC_claims_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
