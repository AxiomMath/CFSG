module

public import CFSG.LocalAnalysis.AGLEmbedding.AltSix
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.AGLEmbedding


open CFSG.Open Subgroup CFSG.RankThree.PerfectCover

theorem card_center_dvd_card_hopfMultiplier {K : Type} [Group K] [Group.IsPerfect K] {n : ℕ}
    (e : K ⧸ center K ≃* alternatingGroup (Fin n)) :
    Nat.card (center K) ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin n))) := by
  set q : K →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center K := by
    ext x
    simp [q]
  have h := Subgroup.card_dvd_of_surjective (hopfMultiplierToKer_surjective q hq hker.le)
  rwa [hker] at h

theorem eq_six_or_seven_of_center {K : Type} [Group K] [Group.IsPerfect K] {n : ℕ}
    (hn : 5 ≤ n) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : center K ≠ ⊥) (hZp : IsPGroup p (center K)) : n = 6 ∨ n = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpZ : p ∣ Nat.card (center K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  have hdvd := hpZ.trans (card_center_dvd_card_hopfMultiplier e)
  rw [(Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
  by_contra h
  rw [ite_eq_right h] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

theorem kFactAlphaAlt : KFactAlphaAlt := by
  intro K _ _ hK n hn ⟨e⟩ p hp hp2 hZ hZp _ _
  right; left
  have : Group.IsPerfect K := ⟨hK.1⟩
  have h1 := SectionRank.pRank_top_le_of_injective hp.one_lt
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
    (ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  rw [SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr e)] at h1
  rcases eq_six_or_seven_of_center hn e hp hp2 hZ hZp with rfl | rfl
  · exact h1.trans (pRank_top_mulAut_alternatingGroup_six_le hp hp2)
  · refine h1.trans ((pRank_top_mulAut_le (by norm_num) (by norm_num) (MulEquiv.refl _) hp).trans
      ((Nat.div_le_div_left (c := 3) ?_ (by norm_num)).trans (by norm_num)))
    have := hp.two_le
    omega

end CFSG.AGLEmbedding
