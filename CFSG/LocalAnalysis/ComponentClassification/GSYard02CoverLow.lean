module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Cover
import CFSG.GH74.Generic.GKFFinal
import CFSG.GH74.E2.FactsK
import CFSG.GH74.KGroups.TwoA7Main

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

private theorem card_le_two_of_le_cyclic {Q : Type} [Group Q] [Finite Q] {Z : Subgroup Q}
    [IsCyclic Z] {E : Subgroup Q} (hEZ : E ≤ Z) (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  classical
  have := Fintype.ofFinite Z
  have h2 := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hinj : Function.Injective
      (fun t : E => (⟨(⟨(t : Q), hEZ t.2⟩ : Z), by
        apply Subtype.ext
        simpa using hsq (t : Q) t.2⟩ : {x : Z // x ^ 2 = 1})) := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun y : {x : Z // x ^ 2 = 1} => ((y.1 : Z) : Q)) h
  have h3 := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card {x : Z // x ^ 2 = 1} =
      (Finset.univ.filter (fun x : Z => x ^ 2 = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem coverLow_holds :
    CoverLow := by
  intro Q _ _ hCov hle
  obtain ⟨hQ, hZ, hZ2, hZc, hr3, -⟩ := hCov
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hr3' : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 2 Q]
    exact hr3
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (H := (⊤ : Subgroup Q))
      (k := 3) hr3'
  have hnot : ¬ E ≤ center Q := by
    intro hEZ
    have h8 := card_le_two_of_le_cyclic hEZ hE.2
    rw [hEcard] at h8
    norm_num at h8
  obtain ⟨x, hxE, hxZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx2 : x ^ 2 = 1 := hE.2 x hxE
  have hxbar1 : (x : Q ⧸ center Q) ≠ 1 := fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
  have hxbar2 : (x : Q ⧸ center Q) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
  have heven : Even (Nat.card (Q ⧸ center Q)) := by
    have hdvd := orderOf_dvd_natCard (x : Q ⧸ center Q)
    rw [orderOf_eq_prime hxbar2 hxbar1] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  have h2le : 2 ≤ CFSG.Open.twoRank (Q ⧸ center Q) :=
    CFSG.Walter.two_le_twoRank (Q ⧸ center Q) hQ.2.2 heven
  have h2eq : CFSG.Open.twoRank (Q ⧸ center Q) = 2 := le_antisymm hle h2le
  have hGK : CFSG.GH74.Generic.GenericKnownFacts :=
    CFSG.GH74.Generic.genericKnownFacts_of_griess
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hE2 : CFSG.GH74.E2.E2ComponentFacts := CFSG.GH74.E2.e2ComponentFacts
  rcases CFSG.Assembly.LowTwoRank.rank_two_isomorphism_types (Q ⧸ center Q) hQ.2.2 h2eq with
    ⟨p, f, hp, hp2, -, hPSL2⟩ | ⟨p, f, hp, hp2, -, hPSL3⟩ | ⟨p, f, hp, hp2, -, hPSU3⟩ |
      hPSU322 | hA7 | hM11
  ·
    have hLie : CFSG.Blueprint.LieModel (Q ⧸ center Q) .PSL 2 p f := Or.inl ⟨by decide, hPSL2⟩
    rcases hGK.psl2_cover p f hp hp2 Q hQ hZ2 hLie with hbot | ⟨F, hF, hFin, hcard, ⟨e⟩⟩
    · exact hZ hbot
    · have hodd : Odd (Nat.card F) := by
        rw [hcard]
        exact (hp.odd_of_ne_two hp2).pow
      have hF1 := CFSG.Semidihedral.OddFieldSL2.twoRank_le_one F hodd
      have hiso := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num)
        (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm)
      have key : CFSG.Open.pRank 2 (⊤ : Subgroup Q) ≤ 1 := by
        rw [hiso]
        exact hF1
      omega
  ·
    have hLie : CFSG.Blueprint.LieModel (Q ⧸ center Q) .PSL 3 p f := Or.inl ⟨by decide, hPSL3⟩
    exact hZ (hGK.noTwoCover_psl3 p f hp hp2 (Q ⧸ center Q) hLie Q hQ hZ2 ⟨MulEquiv.refl _⟩)
  ·
    have hLie : CFSG.Blueprint.LieModel (Q ⧸ center Q) .PSU 3 p f := Or.inl ⟨by decide, hPSU3⟩
    exact hZ (hGK.noTwoCover_psu3 p f hp hp2 (Q ⧸ center Q) hLie Q hQ hZ2 ⟨MulEquiv.refl _⟩)
  ·
    have hLie : CFSG.Blueprint.LieModel (Q ⧸ center Q) .PSU 3 2 2 := Or.inl ⟨by decide, hPSU322⟩
    exact hZ (hE2.noTwoCover_even (Q ⧸ center Q) (Or.inr (Or.inr hLie)) Q hQ hZ2
      ⟨MulEquiv.refl _⟩)
  ·
    have hc1 : 2 ≤ Nat.card (center Q) := by
      have := (Subgroup.one_lt_card_iff_ne_bot (H := center Q)).mpr hZ
      omega
    have hc2 : Nat.card (center Q) ≤ 2 :=
      hGK.alt_cover 7 (by norm_num) (by norm_num) Q hQ hZ2 hA7
    have hdbl : CFSG.GH74.GLS.IsDoubleCoverOfAlt Q 7 := ⟨hQ, le_antisymm hc2 hc1, hA7⟩
    obtain ⟨π, z, hdc, -⟩ := CFSG.GH74.KGroups.TwoA7.exists_cover hdbl
    have h7 := CFSG.GH74.KGroups.TwoA7.pRank_eq_one hdc
    omega
  ·
    exact hZ (hE2.noTwoCover_sporadic (Q ⧸ center Q) hM11 Q hQ hZ2 ⟨MulEquiv.refl _⟩)

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
