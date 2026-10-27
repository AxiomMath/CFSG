module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Ctx
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Norm
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G}

theorem isPPoint_of_mem_abelian (hloc : D1Local p P M) (hab : IsMulCommutative (P : Subgroup G))
    {a : G} (ha : a ∈ (P : Subgroup G)) (hao : orderOf a = p)
    (hC : ¬ centralizer ({a} : Set G) ≤ M) : IsPPoint p P M a := by
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hPC := PPointFrobenius.pt_P_le_centralizer_of_mem hab ha
  have h4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hloc.beta P
  have hinf : (P : Subgroup G) ⊓ centralizer ({a} : Set G) = P := inf_of_le_left hPC
  have h3 : 3 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({a} : Set G)) :=
    (by norm_num : 3 ≤ 4).trans (h4.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp.out (le_inf hPM hPC)))
  refine ⟨?_, ha, ?_, ?_⟩
  · exact ⟨hPM ha, hao, h3, hC⟩
  · rw [hinf]
    exact PPointFrobenius.pt_isSylowOf_of_le P hPC
  · rw [hinf]
    omega

theorem exists_sylow_through_plane_p (hG : P5Global G) (hloc : D1Local p P M)
    {R H : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hRH : R ≤ H) :
    ∃ R' : Subgroup G, IsSylowOf p R' H ∧ R ≤ R' ∧ R' ≤ M := by
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hRp : IsPGroup p R := elementary_isPGroup p R hRe
  have hRA : R ≤ H ⊓ M := le_inf hRH (hRP.trans hPM)
  obtain ⟨T₁, hT₁⟩ := (hRp.comap_subtype (K := H ⊓ M)).exists_le_sylow
  set R'' : Subgroup G := (T₁ : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  have hR''A : IsSylowOf p R'' (H ⊓ M) := ⟨T₁, rfl⟩
  have hRR'' : R ≤ R'' := fun r hr => ⟨⟨r, hRA hr⟩, hT₁ hr, rfl⟩
  have hR''M : R'' ≤ M := hR''A.le.trans inf_le_right
  have hR''H : R'' ≤ H := hR''A.le.trans inf_le_left
  have hR''p : IsPGroup p R'' := hR''A.isPGroup
  obtain ⟨T₂, hT₂⟩ := (hR''p.comap_subtype (K := H)).exists_le_sylow
  set R' : Subgroup G := (T₂ : Subgroup ↥H).map H.subtype
  have hR'H : IsSylowOf p R' H := ⟨T₂, rfl⟩
  have hR''R' : R'' ≤ R' := fun r hr => ⟨⟨r, hR''H hr⟩, hT₂ hr, rfl⟩
  refine ⟨R', hR'H, hRR''.trans hR''R', ?_⟩
  have hR'R'' : R' ≤ R'' := by
    by_contra hnle
    have hlt : R''.subgroupOf R' < ⊤ :=
      lt_top_iff_ne_top.mpr fun htop => hnle (Subgroup.subgroupOf_eq_top.mp htop)
    have : Group.IsNilpotent ↥R' := hR'H.isPGroup.isNilpotent
    obtain ⟨n, hn, hnB⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    rw [← Subgroup.subgroupOf_normalizer_eq hR''R'] at hn
    have h2 : 2 ≤ CFSG.Open.pRank p R'' :=
      CFSG.SectionRank.le_pRank hp.out.one_lt hRR'' hRe hRc
    have hnM : (n : G) ∈ M := normalizer_le_of_two_le_pRank hG.fc hloc hR''p hR''M h2 hn
    have hQA : R'' ⊔ zpowers (n : G) ≤ H ⊓ M :=
      sup_le hR''A.le (zpowers_le.mpr ⟨hR'H.le n.2, hnM⟩)
    have hQR' : R'' ⊔ zpowers (n : G) ≤ R' := sup_le hR''R' (zpowers_le.mpr n.2)
    have hQ : R'' ⊔ zpowers (n : G) = R'' :=
      hR''A.eq_of_le le_sup_left hQA (hR'H.isPGroup.to_le hQR')
    exact hnB (hQ ▸ mem_sup_right (mem_zpowers (n : G)))
  exact hR'R''.trans hR''M

theorem rank3_absorb_p (hG : P5Global G) (hloc : D1Local p P M)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) :
    ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M := by
  intro H hH hRH hH3
  obtain ⟨R', hR'H, -, hR'M⟩ := exists_sylow_through_plane_p hG hloc hRP hRe hRc hRH
  have h3 : 3 ≤ CFSG.Open.pRank p (H ⊓ M) := by
    have h1 : CFSG.Open.pRank p R' = CFSG.Open.pRank p H := pRank_eq_of_isSylowOf hp.out hR'H
    have h2 : CFSG.Open.pRank p R' ≤ CFSG.Open.pRank p (H ⊓ M) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp.out (le_inf hR'H.le hR'M)
    omega
  exact hG.d1 p hloc.beta P M hloc.maxLocal hloc.core H hH h3

end CFSG.LocalAnalysis.RankFourTheoremC.P5
