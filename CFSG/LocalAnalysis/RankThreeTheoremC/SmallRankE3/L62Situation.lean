module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Step0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

private theorem l62sit_isElemAbelian_subgroupOf {X : Type} [Group X] {p : ℕ} (K E : Subgroup X)
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.Open.IsElemAbelian p (E.subgroupOf K) := by
  obtain ⟨hcomm, hpow⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
  · have h := mul_comm' (⟨a.1.1, Subgroup.mem_subgroupOf.mp a.2⟩ : E)
      ⟨b.1.1, Subgroup.mem_subgroupOf.mp b.2⟩
    have h' := congrArg Subtype.val h
    exact h'
  · exact Subtype.ext (hpow _ (Subgroup.mem_subgroupOf.mp hx))

private theorem l62sit_pRank_map_subtype {X : Type} [Group X] [Finite X] {p : ℕ} (hp : 1 < p)
    (K : Subgroup X) (S : Subgroup ↥K) :
    CFSG.Open.pRank p (S.map K.subtype) = CFSG.Open.pRank p S := by
  refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map hp K.subtype K.subtype_injective S)
  obtain ⟨E, hEmap, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp (S.map K.subtype)
  have hEK : E ≤ K := hEmap.trans (Subgroup.map_subtype_le S)
  have hmap : (E.subgroupOf K).map K.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEK
  refine CFSG.SectionRank.le_pRank hp (E := E.subgroupOf K) ?_
    (l62sit_isElemAbelian_subgroupOf K E hE) ?_
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hEmap (Subgroup.mem_subgroupOf.mp hy))
    have hzy' : K.subtype z = K.subtype y := hzy
    have hzy'' : z = y := K.subtype_injective hzy'
    rw [← hzy'']
    exact hz
  · rw [← Subgroup.card_map_of_injective K.subtype_injective, hmap]
    exact hcard

private theorem l62sit_pRank_centralizer_le {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {x : G} (hxM : x ∈ M) {k : ℕ} (h : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ k) :
    CFSG.Open.pRank 3 (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) ≤ k := by
  refine le_trans (CFSG.SectionRank.pRank_le_map (by norm_num) M.subtype M.subtype_injective _)
    (le_trans (CFSG.SectionRank.pRank_mono (by norm_num) ?_) h)
  rintro _ ⟨c, hc, rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))

private theorem l62sit_pRank_top_le {G : Type} [Group G] [Finite G] {q : ℕ} (hq : 1 < q)
    (M : Subgroup G) : CFSG.Open.pRank q (⊤ : Subgroup ↥M) ≤ CFSG.Open.pRank q M := by
  have h := CFSG.SectionRank.pRank_le_map hq M.subtype M.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

theorem l62Data_of_situation {G : Type} [Group G] [Finite G]
    (hS : CFSG.LocalAnalysis.RankThreeTheoremC.Setting G)
    (hU0 : CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreLocal G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSituation G 3 P M) {x z : G}
    (hx : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPoint P M x)
    (hz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCentral P z) :
    ∃ (S : Sylow 3 ↥M) (x' z' : ↥M), L62Data ↥M S x' z' ∧
      (S : Subgroup ↥M).map M.subtype = (P : Subgroup G) ∧ (x' : G) = x ∧ (z' : G) = z := by
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hMne : M ≠ ⊤ := fun h => hs.not_gamma_one_le (by rw [h]; exact le_top)
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hs.largeObstruction_empty x
      ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Sylow 3 ↥M, S = P.subtype hPM := ⟨_, rfl⟩
  have hSsub : (S : Subgroup ↥M) = (P : Subgroup G).subgroupOf M := by
    rw [hSdef, Sylow.coe_subtype]
  have hSmap : (S : Subgroup ↥M).map M.subtype = (P : Subgroup G) := by
    rw [hSsub, Subgroup.map_subgroupOf_eq_of_le hPM]
  have hmemS : ∀ g : ↥M, g ∈ (S : Subgroup ↥M) ↔ (g : G) ∈ (P : Subgroup G) := by
    intro g
    rw [hSsub]
    exact Subgroup.mem_subgroupOf
  have hxM : x ∈ M := hPM hx.mem
  have hzM : z ∈ M := hPM hz.mem
  have hcat : CFSG.AGLEmbedding.CatalogSimpleSections ↥M :=
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMne
  have hrank : CFSG.Open.pRank 3 (S : Subgroup ↥M) = 3 := by
    rw [← l62sit_pRank_map_subtype (p := 3) (by norm_num) M (S : Subgroup ↥M), hSmap, hP3]
  have hx_mem : (⟨x, hxM⟩ : ↥M) ∈ (S : Subgroup ↥M) := (hmemS (⟨x, hxM⟩ : ↥M)).mpr hx.mem
  have hx_ne : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx.ne_one (congrArg Subtype.val h)
  have hx_pow : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := Subtype.ext hx.pow_eq_one
  have hcent : CFSG.Open.pRank 3 (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) ≤ 2 :=
    l62sit_pRank_centralizer_le hxM hCx
  have hz_mem : (⟨z, hzM⟩ : ↥M) ∈ (S : Subgroup ↥M) := (hmemS (⟨z, hzM⟩ : ↥M)).mpr hz.mem
  have hz_central : ∀ g ∈ (S : Subgroup ↥M), g * (⟨z, hzM⟩ : ↥M) = (⟨z, hzM⟩ : ↥M) * g := by
    intro g hg
    apply Subtype.ext
    exact mem_centralizer_iff.mp hz.centralizes (g : G) ((hmemS g).mp hg)
  have hz_ne : (⟨z, hzM⟩ : ↥M) ≠ 1 := fun h => hz.ne_one (congrArg Subtype.val h)
  have hz_pow : (⟨z, hzM⟩ : ↥M) ^ 3 = 1 := Subtype.ext hz.pow_eq_one
  have hz_gen : ∀ w ∈ (S : Subgroup ↥M), (∀ g ∈ (S : Subgroup ↥M), g * w = w * g) →
      w ^ 3 = 1 → w ∈ Subgroup.zpowers (⟨z, hzM⟩ : ↥M) := by
    intro w hw hwc hw3
    have hplane := smallRankPlane_of_largeObstruction_empty hS hs.mem_sigmaA hs.isCoreMaxLocal
      hs.largeObstruction_empty hx.mem hx.ne_one hx.pow_eq_one hx.not_centralizer_le hz.mem
      hz.centralizes hz.ne_one hz.pow_eq_one
    have hwP : (w : G) ∈ (P : Subgroup G) := (hmemS w).mp hw
    have hwcent : (w : G) ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro g hg
      have hg' : g ∈ (S : Subgroup ↥M).map M.subtype := by
        rw [hSmap]
        exact hg
      obtain ⟨h, hhS, rfl⟩ := Subgroup.mem_map.mp hg'
      exact congrArg Subtype.val (hwc h hhS)
    have hw3' : (w : G) ^ 3 = 1 := congrArg Subtype.val hw3
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hplane.center (w : G) hwP hwcent hw3')
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext hj⟩
  have hno3 : ∀ N : Subgroup ↥M, N.Normal → N.index ≠ 3 :=
    no_normal_index_three_of_situation hS hU0 hs
  have hqrank : ∀ q : ℕ, q.Prime → 5 ≤ q → CFSG.Open.pRank q (⊤ : Subgroup ↥M) ≤ 2 :=
    fun q hq h5 => (l62sit_pRank_top_le hq.one_lt M).trans (pRank_le_two_of_situation hS hs hq h5)
  refine ⟨S, ⟨x, hxM⟩, ⟨z, hzM⟩, ?_, hSmap, rfl, rfl⟩
  exact
    { catalog := hcat
      rank := hrank
      x_mem := hx_mem
      x_ne := hx_ne
      x_pow := hx_pow
      cent := hcent
      z_mem := hz_mem
      z_central := hz_central
      z_ne := hz_ne
      z_pow := hz_pow
      z_gen := hz_gen
      no_normal_three := hno3
      qrank := hqrank }

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
