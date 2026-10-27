module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorelStruct
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma45
import CFSG.LocalAnalysis.RankFourTheoremC.PPointKlein

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.PreuniquenessRankFour.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BorelData3

variable {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ} {f : GaloisField 3 n → G}
  {W : Subgroup G}

theorem exists_rankTwoMaximal_not_le (hB : BorelData3 P M x f W) {t₀ : GaloisField 3 n}
    (ht₀ : t₀ ≠ 0) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup (plane x f t₀) S₁ ∧ ¬ S₁ ≤ M := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, d, hfacts, hd, ⟨e⟩, hρ, -, -, -, -⟩ := hB.reduced
  have hred := hfacts.red
  have hn := hB.three_le
  have hn1 : 1 ≤ n := by omega
  have : K.Normal := hred.normal
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set ρ : C →* RedCent 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρdef
  obtain ⟨hc, hmem, hne⟩ := hρ t₀
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K R
  set u : K := ⟨ρ ⟨f t₀, hc⟩, hmem.2⟩ with hu
  have huT : u ∈ (T : Subgroup K) := by
    have : (u : RedCent 3 x) ∈ (T : Subgroup K).map K.subtype := by rw [hT]; exact hmem
    obtain ⟨t', ht', hteq⟩ := this
    have : t' = u := Subtype.ext hteq
    exact this ▸ ht'
  have hu1 : u ≠ 1 := fun h => hne ht₀ (congrArg Subtype.val h)
  obtain ⟨V₀, hV₀2, hnorm, hnl⟩ := exists_isPGroup_two_normalized_not_le_normalizer hn1 e T huT hu1
  set V : Subgroup (RedCent 3 x) := V₀.map K.subtype with hV
  have hV2 : IsPGroup 2 V := hV₀2.map K.subtype
  have huV : ρ ⟨f t₀, hc⟩ ∈ normalizer (V : Set (RedCent 3 x)) :=
    Subgroup.le_normalizer_map K.subtype ⟨u, hnorm, rfl⟩
  have hzV : ρ ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ ∈ normalizer (V : Set (RedCent 3 x)) :=
    Subgroup.center_le_normalizer (V : Set (RedCent 3 x)) (mk_mem_center_centralizer _ rfl)
  set A : Subgroup C := (normalizer (V : Set (RedCent 3 x))).comap ρ with hA
  have hUA : plane x f t₀ ≤ A.map C.subtype := by
    refine sup_le (zpowers_le.mpr ⟨⟨x, mem_centralizer_singleton_iff.2 rfl⟩, hzV, rfl⟩)
      (zpowers_le.mpr ⟨⟨f t₀, hc⟩, huV, rfl⟩)
  have hUC : plane x f t₀ ≤ C := (hB.plane_le_inf t₀).trans inf_le_right
  have hUV : ∀ (w : G) (hw : w ∈ plane x f t₀),
      ρ ⟨w, hUC hw⟩ ∈ normalizer (V : Set (RedCent 3 x)) := fun w hw => by
    obtain ⟨a, ha, haw⟩ := hUA hw
    have : a = ⟨w, hUC hw⟩ := Subtype.ext haw
    exact this ▸ ha
  have hVM : ¬ V ≤ redCentM 3 M x := by
    intro hVX
    obtain ⟨hTab, hTcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 e R
    have hrank : 3 ≤ Open.pRank 3 ((R : Subgroup (RedCent 3 x)) ⊓ K) :=
      hn.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨_, le_rfl, hTab, hTcard⟩)
    have hN : normalizer ((((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x))) :
        Set (RedCent 3 x)) ≤ redCentM 3 M x :=
      (normalizer_le_glbCore 3 2 inf_le_left (by omega)).trans hred.fullCore
    have hKX := inf_le_normalizer_of_psl2GF (by norm_num : (3 : ℕ) ≠ 2) hn1 e R hN hred.not_le
    have hTt : ∀ s : K, s ∈ (T : Subgroup K) ↔
        (s : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) ⊓ K := fun s => by
      rw [← hT]
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
    refine hnl fun k hk => ?_
    have hkN : (k : RedCent 3 x) ∈ normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K :
        Subgroup (RedCent 3 x)) : Set (RedCent 3 x)) :=
      hKX ⟨hVX ⟨k, hk, rfl⟩, k.2⟩
    rw [mem_normalizer_iff] at hkN ⊢
    intro t
    have := hkN (t : RedCent 3 x)
    show t ∈ (T : Subgroup K) ↔ k * t * k⁻¹ ∈ (T : Subgroup K)
    rw [hTt, hTt]
    simpa using this
  have hUp : IsPGroup 3 (plane x f t₀) := elementary_isPGroup 3 _ (hB.plane_isElemAbelian t₀)
  exact exists_rankTwoMaximal_not_le_of_reduced hp (by norm_num) hUp hUC V hV2 hUV hVM

end BorelData3

end CFSG.LocalAnalysis.RankFourTheoremC
