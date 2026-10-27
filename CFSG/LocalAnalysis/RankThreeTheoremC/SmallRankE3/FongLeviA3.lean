module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviA3Equiv
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

theorem valid_A_two_of_ne_two {q : PrimePower} (h : q.card ≠ 2) : (LieTypeIndex.A 2 q).Valid := by
  refine (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2
    ⟨by norm_num, fun h' => absurd h' (by norm_num)⟩, ?_⟩
  rw [LieTypeIndex.isDuplicateRepresentative_iff]
  rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h3, -⟩)
  · omega
  · exact h h2
  · omega

theorem a3_e3_full {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {q : PrimePower} (hq2 : q.p = 2)
    (hv : (LieTypeIndex.A 3 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩)) : E3Concl K₀ B z p := by
  obtain ⟨e⟩ := e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 :=
    (ringChar.eq (GaloisField q.p q.exponent) q.p).trans hq2
  haveI : CharP (GaloisField q.p q.exponent) 2 := ringChar.of_eq hchar
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hvv := (LieTypeIndex.valid_iff _).1 hv
  have hne2 : q.card ≠ 2 := by
    intro h2
    apply hvv.2
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    exact Or.inr (Or.inr ⟨rfl, h2⟩)
  have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq2]
  have hcardF : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent (by omega), hq2]
  have h4 : 4 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF]
    rcases Nat.lt_or_ge q.exponent 2 with h | h
    · exfalso
      have h1 : q.exponent = 1 := by omega
      rw [h1] at hq
      exact hne2 (by rw [hq]; norm_num)
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h
  let eSL : ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField q.p q.exponent) :=
    (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 4
        (GaloisField q.p q.exponent)))).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL
        (GaloisField q.p q.exponent))
  have hLS := a3_leviSurj_of_equiv S h4 eSL
  have hv2 : (LieTypeIndex.A 2 q).Valid := valid_A_two_of_ne_two hne2
  have hLS' : LeviSurj p K₀ z (CFSGIndex.lie ⟨.A 2 q, hv2⟩).Group :=
    hLS.of_mulEquiv (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv2).symm
  exact LeviSurj.conclusion S.hp S.hBK₀ (d := ⟨.A 2 q, hv2⟩) (by simpa using hq2) (by simp)
    (by simp [CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex]) hLS'

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
