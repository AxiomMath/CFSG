module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviRankArith
public import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open

theorem aBig_false {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {n : ℕ} (hn : 4 ≤ n) {q : PrimePower} (hq2 : q.p = 2)
    (hodd : Odd q.exponent) (hv : (LieTypeIndex.A n q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A n q, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hmodel : StatedClassicalModel K .PSL (n + 1) q.p q.exponent :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
  have hF2 : Nat.card F = 2 ^ q.exponent := by rw [hF, hq2]
  rcases Nat.lt_or_ge q.exponent 3 with hlt | hge
  ·
    have hf1 : q.exponent = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hcard : q.card = 2 := by
      rw [TauCeti.PrimePower.card_def, hq2, hf1, pow_one]
    let e0 : ↥K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (n + 1)
        (GaloisField q.p q.exponent) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          (n + 1) (GaloisField q.p q.exponent)))
    have hZ : Subgroup.center ↥K = ⊥ :=
      center_eq_bot_of_mulEquiv e0
        (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := n + 1)
          (k := GaloisField q.p q.exponent) (by omega))
    exact false_of_not_dvd_card_outer S hZ
      (CFSG.AGLEmbedding.not_dvd_card_outer_lie_two ⟨.A n q, hv⟩ (Or.inl hcard) e S.hp S.hp5)
  ·
    obtain ⟨ℓ, hℓp, hℓ2, hℓ5, hℓd⟩ := exists_prime_dvd_two_pow_sub_one_ne_five hodd hge
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    have hℓrk : CFSG.Open.pRank ℓ K ≤ 3 := S.hℓ ℓ hℓp hℓ2
    have h4 : 4 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥K) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓp.one_lt eF]
      exact psl_four_le_pRank_of_dvd hℓ2 (by omega) (Or.inl hℓ5) hF2 hℓd
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at hℓrk
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
