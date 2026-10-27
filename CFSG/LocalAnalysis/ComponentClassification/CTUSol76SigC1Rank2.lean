module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigDisc
public import CFSG.Walter.RankTwo

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem involutionsFourCover_of_conj {Q : Type} [Group Q] {z : Q}
    (h : ∀ t : Q, orderOf t = 2 → ∃ g : Q, g⁻¹ * t * g = z) : InvolutionsFourCover Q := by
  intro E hE x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyE, hy1⟩ : ∃ y ∈ E, y ≠ 1 := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have hbot : E = ⊥ := eq_bot_iff.2 fun y hy => mem_bot.2 (hne y hy)
    have h4 := hE.card_four
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hy2 : orderOf y = 2 := orderOf_eq_prime (Sig.sq_eq_one_of_isKleinFour hE hyE) hy1
  obtain ⟨g₁, hg₁⟩ := h x hx
  obtain ⟨g₂, hg₂⟩ := h y hy2
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hy : y = g₂ * z * g₂⁻¹ := by rw [← hg₂]; group
  have heq : (g₁ * g₂⁻¹)⁻¹ * x * (g₁ * g₂⁻¹) = y := by
    rw [hy, ← hg₁]
    group
  rw [heq]
  exact hyE

theorem c1Rank2Simple_holds :
    C1Rank2Simple := by
  intro Q _ _ hQq hQO hQcat hQr hZ
  obtain ⟨-, hs, a, b, hab⟩ := hQq
  let e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup Q := e.symm.isSimpleGroup
  have hnab : ∃ a b : Q, a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hrank : CFSG.Assembly.twoRank Q = 2 := by
    rw [← CFSG.Walter.twoRank_eq_assembly]
    change CFSG.Open.pRank 2 ⊤ = 2
    rw [← SectionRank.pRank_eq_open_pRank_top]
    exact hQr
  obtain ⟨z, -, hall⟩ := RankTwoShapes.rank_two_simple_involutions_conjugate hnab hrank
  exact involutionsFourCover_of_conj hall

end CFSG.ComponentClassification.Sol76.Sig
