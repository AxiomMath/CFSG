module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveComm
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCyclic

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.KFactProofs.RankOneCore KFactProofs.SmallIdent

theorem normalizerQuotientComm_of_section_rankOne
    {K L : Type} [Group K] [Finite K] [Group L] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : (∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
      IsReeGTwoIndex p d)
    (hK : Nonempty (K ≃* CatGroup d)) (A : Subgroup K) (π : A →* L)
    (hπ : Function.Surjective π) : NormalizerQuotientComm p L :=
  fun T hT _ hx _ hy => comm_mem_normalizer_of_section_rankOne hp2 hd hK A π hπ T hT hx hy

structure SmallBadNonComm : Prop where
  altTwoP : ∀ {p : ℕ}, p.Prime → 5 ≤ p → ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L →
    IsAltTwoP p L → ¬ NormalizerQuotientComm p L
  linThreeFour : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsLinThreeFour L →
    ¬ NormalizerQuotientComm 3 L
  m11 : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsSporadicGroup .M11 L →
    ¬ NormalizerQuotientComm 3 L
  tits : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsTitsGroup L →
    ¬ NormalizerQuotientComm 5 L
  mcl : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsSporadicGroup .McL L →
    ¬ NormalizerQuotientComm 5 L
  fi22 : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsFi22 L →
    ¬ NormalizerQuotientComm 5 L
  j4 : ∀ {L : Type} [Group L] [Finite L], IsSimpleGroup L → IsSporadicGroup .J4 L →
    ¬ NormalizerQuotientComm 11 L

theorem kFactSmallInvolve_of_bad
    (hId : KFactOneLieIdent) (hSId : KFactSmallIdent) (hB : SmallBadNonComm) :
    KFactSmallInvolve := by
  intro KC _ _ hsKC hnabKC hcatKC p hp hp2 T hncyc hΓ hrk L _ _ hsL hnabL hcatL TL hncycL hΓL hrkL
    A f hf
  have hpf : Fact p.Prime := ⟨hp⟩
  have hSP := isSmallStrongP_of_autRank hSId hsL hnabL hcatL hp hp2 TL hncycL hΓL hrkL
  obtain ⟨d, hd, hK⟩ := hId KC hsKC hnabKC hcatKC p hp hp2 T hncyc hΓ (by omega)
  have hcomm : NormalizerQuotientComm p L :=
    normalizerQuotientComm_of_section_rankOne hp2 hd hK A f hf
  rcases hSP with h | h | h | ⟨h3, h | h⟩ | ⟨h5, h | h | h⟩ | ⟨h11, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · by_cases hp3 : p = 3
    · subst hp3
      exact Or.inr (Or.inr ⟨rfl, h⟩)
    · have hp5 : 5 ≤ p := by
        by_contra hlt
        have h2 := hp.two_le
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)
      exact absurd hcomm (hB.altTwoP hp hp5 hsL h)
  · subst h3
    exact absurd hcomm (hB.linThreeFour hsL h)
  · subst h3
    exact absurd hcomm (hB.m11 hsL h)
  · subst h5
    exact absurd hcomm (hB.tits hsL h)
  · subst h5
    exact absurd hcomm (hB.mcl hsL h)
  · subst h5
    exact absurd hcomm (hB.fi22 hsL h)
  · subst h11
    exact absurd hcomm (hB.j4 hsL h)

end CFSG.AGLEmbedding
