module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem exists_projectiveSL_of_isLieOfTorus {p : ℕ} {X : Type} [Group X]
    (h : IsLieOfTorus IdxA p X) :
    ∃ r f : ℕ, 1 ≤ r ∧ 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      Nonempty (X ≃* projectiveSL (r + 1) (GaloisField 2 f)) := by
  obtain ⟨⟨d, hv⟩, hPd, ht, ⟨e⟩⟩ := h
  cases d with
  | A r q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨q₀, f, hq₀, hf⟩ := q
    change q₀ = 2 at hPd
    subst hPd
    have ht' : ¬ ((⟨2, f, hq₀, hf⟩ : TauCeti.PrimePower).card = 2 ∨
        ¬ p ∣ (⟨2, f, hq₀, hf⟩ : TauCeti.PrimePower).card - 1) := ht
    rw [TauCeti.PrimePower.card_def, not_or, not_not] at ht'
    change ¬ 2 ^ f = 2 ∧ p ∣ 2 ^ f - 1 at ht'
    refine ⟨r, f, hr.1, ?_, ht'.2, ⟨(e.trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r _ hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩
    by_contra hf2
    exact ht'.1 (by rw [show f = 1 by omega, pow_one])
  | _ => exact (hPd : False).elim

theorem exists_cover_of_oddCenter (hZ : OddCenterLinear) (hC : KFactCoverLinear) {Y : Type}
    [Group Y] [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Fintype K] [CharP K 2] (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ∧
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · have hdvd := hZ Y L hL hodd 2 K ⟨e⟩
    obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
    rw [hcard, gcd_two_two_pow_pred_eq_one f.pos, Nat.dvd_one] at hdvd
    obtain ⟨ρ, hρ⟩ := exists_compat_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ hdvd) e
    obtain ⟨hs, hk⟩ := surjective_and_ker_le_of_compat hL.2.2.1 e ρ hρ
    exact ⟨ρ, hs, hk, hρ⟩
  · exact hC Y L hL hodd n K hn3 e

theorem not_dvd_card_center_of_three (hZ : OddCenterLinear) {Y : Type} [Group Y] [Finite Y]
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    {K : Type} [Field K] [Fintype K] [CharP K 2]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K) {p : ℕ} (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
  intro hdvd
  have h := (hdvd.trans (hZ Y L hL hodd 3 K ⟨e⟩)).trans (Nat.gcd_dvd_left 3 _)
  have := Nat.le_of_dvd (by norm_num) h
  omega

end ToralCensus

end CFSG.AGLEmbedding
