module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeStepsAt
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_elemAbelian_card_three {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {U A : Subgroup G} (hU : IsPGroup p U) (hUM : U ≤ M)
    (hAU : A ≤ U) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hrank : 3 ≤ CFSG.Open.pRank p A :=
    CFSG.SectionRank.le_pRank he.prime.one_lt le_rfl hA hAc
  have hAC : A ≤ U ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf hAU ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hCrank : 3 ≤ CFSG.Open.pRank p (U ⊓ Subgroup.centralizer (A : Set G)) :=
    CFSG.SectionRank.le_pRank he.prime.one_lt hAC hA hAc
  exact normalizer_le_of_pRank_centralizer he hU hUM hAU (by omega) hCrank

theorem normalizer_le_d1X0_of_elemAbelian {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    {A : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hAQ : A ≤ (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hA : IsElemAbelian 3 A) (hA27 : Nat.card A = 27) :
    normalizer (A : Set (H ⧸ primeComplementCore (G := H) 3)) ≤ d1X0 3 M H := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  set O := primeComplementCore (G := H) 3
  set π := QuotientGroup.mk' O
  have hO : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  have hQp : IsPGroup 3 (Q.subgroupOf H) :=
    hd.base.2.1.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨E₁, hE₁Q, hE₁π, hE₁el, hE₁card⟩ :=
    exists_isElemAbelian_lift hp O hO hQp hA hAQ
  have hE₁p : IsPGroup 3 E₁ := hQp.to_le hE₁Q
  have hÃQ : E₁.map H.subtype ≤ Q :=
    (Subgroup.map_mono hE₁Q).trans (le_of_eq (Subgroup.map_subgroupOf_eq_of_le hd.le_H))
  have hÃel : IsElemAbelian 3 (E₁.map H.subtype) := IsElemAbelian.map hE₁el H.subtype
  have hÃcard : Nat.card (E₁.map H.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hE₁card, hA27]
    norm_num
  have hNM : Subgroup.normalizer (E₁.map H.subtype : Set G) ≤ M :=
    normalizer_le_of_elemAbelian_card_three he hd.base.2.1 hd.base.1 hÃQ hÃel hÃcard
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hx₁ : (QuotientGroup.mk' O) h ∈ Subgroup.normalizer
      ((E₁.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)) := by
    rw [hE₁π]
    exact hx
  have hsup : h ∈ O ⊔ Subgroup.normalizer (E₁ : Set H) :=
    comap_normalizer_map_le_sup hp O hO hE₁p hx₁
  have hsub : O ⊔ Subgroup.normalizer (E₁ : Set H) ≤ (H ⊓ M).subgroupOf H := by
    refine sup_le ?_ ?_
    · intro o ho
      exact Subgroup.mem_subgroupOf.mpr
        ⟨o.property, hd.primeCore_le (Subgroup.mem_map_of_mem H.subtype ho)⟩
    · intro n hn
      refine Subgroup.mem_subgroupOf.mpr ⟨n.property, hNM ?_⟩
      exact Subgroup.le_normalizer_map (H := E₁) H.subtype
        (Subgroup.mem_map_of_mem H.subtype hn)
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) (hsub hsup)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
