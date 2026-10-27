module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenLinII
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAbs
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
  TauCeti CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

theorem exists_mulEquiv_specialLinear_cover {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZ3 : Nat.card (Subgroup.center K) = 3) {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (h3 : 3 ∣ q.card - 1) (h4 : q.card ≠ 4)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), 3 ∣ Nat.card k - 1 ∧ Nat.card k ≠ 4 ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 3) k ≃* K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  obtain ⟨-, k, _, _, hkcard, ⟨e'⟩⟩ := hm
  have hcard : Nat.card k = q.card := by rw [hkcard, TauCeti.PrimePower.card_def]
  have h3k : 3 ∣ Nat.card k - 1 := by rw [hcard]; exact h3
  have h4k : Nat.card k ≠ 4 := by rw [hcard]; exact h4
  have hZK : Subgroup.center K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨ψ⟩ := exists_mulEquiv_specialLinear h3k h4k hK.1
    ((e'.trans (projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)) hZK
  exact ⟨k, inferInstance, inferInstance, h3k, h4k, ⟨ψ⟩⟩

theorem kGenTwoModAbFix_linCover {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZ3 : Nat.card (Subgroup.center K) = 3) {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (h3 : 3 ∣ q.card - 1) (h4 : q.card ≠ 4)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group) :
    KGenTwoModAbFix 3 K := by
  obtain ⟨k, _, _, h3k, -, ⟨ψ⟩⟩ := exists_mulEquiv_specialLinear_cover hK hZ3 hv h3 h4 e
  exact kGenTwoModAbFix_of_equiv ψ fun E hE hcard hfix =>
    closure_fixSet_eq_top_linear h3k E hE hcard hfix

end CFSG.AGLEmbedding.KFactProofs.CoverThree
