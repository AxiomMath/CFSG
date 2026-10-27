module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen49q_exists_sylow [Fact p.Prime] (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {R H : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hRH : R ≤ H) :
    ∃ R' : Subgroup G, IsSylowOf p R' H ∧ R ≤ R' ∧ R' ≤ M := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
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
    have hnM : (n : G) ∈ M := normalizer_le_of_le_of_two_le_pRank hG.setting hG.u0 hl.sigma
      hl.core hR''p hR''M (le_pRank_of_elemAbelian_card hRR'' hRe hRc) hn
    have hQA : R'' ⊔ zpowers (n : G) ≤ H ⊓ M :=
      sup_le hR''A.le (zpowers_le.mpr ⟨hR'H.le n.2, hnM⟩)
    have hQR' : R'' ⊔ zpowers (n : G) ≤ R' := sup_le hR''R' (zpowers_le.mpr n.2)
    have hQ : R'' ⊔ zpowers (n : G) = R'' :=
      hR''A.eq_of_le le_sup_left hQA (hR'H.isPGroup.to_le hQR')
    exact hnB (hQ ▸ mem_sup_right (mem_zpowers (n : G)))
  exact hR'R''.trans hR''M

end CFSG.LocalAnalysis.RankThreeTheoremC
