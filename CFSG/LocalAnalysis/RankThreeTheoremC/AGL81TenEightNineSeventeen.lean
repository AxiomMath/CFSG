module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenFirst
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenFirstTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerRankTwo
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

variable {G : Type} [Group G] [Finite G]

theorem exists_pComponent_not_le_of_ne_bot {p : ℕ} {M N : Subgroup G} (hK : d1KBar p M N ≠ ⊥) :
    ∃ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y N ∧ ¬ Y ≤ M := by
  obtain ⟨L, hLc, hLX⟩ := exists_component_of_d1KBar_ne_bot hK
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p)
  obtain ⟨Y', hY', hYL⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent
    p (isComponent_of_isComponentOf_top'' hLc)
  have hYL' : Y'.map π = L := hYL
  have hYY : (Y'.map N.subtype).subgroupOf N = Y' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  refine ⟨Y'.map N.subtype, ⟨Subgroup.map_subtype_le _, by rw [hYY]; exact hY'⟩, ?_⟩
  intro hle
  refine hLX ?_
  rw [← hYL']
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, ⟨y.2, hle ⟨y, hy, rfl⟩⟩, rfl⟩

theorem d1KBar_ne_bot_of_pRank_le_two_of_bases (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut)
    (hSch : KFactCatalogSchreier) (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁)
    {B B' H N R : Subgroup G} (hB : IsAGLQ p M B) (hBH : B ≤ H) (hB' : IsAGLQ p M B')
    (hB'N : B' ≤ N) (hHtop : H ≠ ⊤) (hNtop : N ≠ ⊤)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) (hcov : AGLCovers p H N (d1KBar p M H))
    (hR : CFSG.Quasithin.IsSylowIn p R N) (hr : CFSG.Open.pRank p R ≤ 2) :
    d1KBar p M N ≠ ⊥ := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  intro hKN
  have hKH : d1KBar p M H ≠ ⊥ := fun h =>
    not_le_bot_of_isComponentOf hL (h ▸ le_d1KBar hL hLX)
  set O := primeComplementCore (G := N) p
  set πH := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set πN := QuotientGroup.mk' O
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hcoreY : primeComplementCore (G := N ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  have hrankY : CFSG.Open.pRank p (⊤ : Subgroup (N ⧸ O)) ≤ 2 := by
    refine pRank_le_of_sylow_inf (hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O))
      Subgroup.IsSubnormal.top ?_
    rw [inf_top_eq, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow,
      pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
    exact hr
  have hlayerX : CFSG.layer (N ⧸ O) ≤ d1X0 p M N := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun L' hL' => ?_
    have hL'c : IsComponentOf L' ⊤ := (CFSG.isComponent_iff_open L').mp hL'
    by_contra hL'X
    exact not_le_bot_of_isComponentOf hL'c (hKN ▸ le_d1KBar hL'c hL'X)
  haveI := CFSG.LocalCores.layer_characteristic (G := N ⧸ O)
  set W₀ : Subgroup G := (H ⊓ N) ⊓ ((d1KBar p M H).comap πH).map H.subtype with hW₀def
  have hW₀ : W₀ ≤ H ⊓ N := inf_le_left
  have hW₀H : W₀ ≤ H := hW₀.trans inf_le_left
  have hW₀N : W₀ ≤ N := hW₀.trans inf_le_right
  have hψ : ∀ w : W₀, πH (Subgroup.inclusion hW₀H w) ∈ d1KBar p M H := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set ψ : W₀ →* d1KBar p M H := (πH.comp (Subgroup.inclusion hW₀H)).codRestrict _ hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := hcov hk
    exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh, h, hk, rfl⟩, rfl⟩
  set ρ : W₀ →* N ⧸ O := πN.comp (Subgroup.inclusion hW₀N)
  haveI : Group.IsPerfect (d1KBar p M H) := Subgroup.isPerfect_iff.mpr (commutator_d1KBar p M H)
  have hPψ := CFSG.LocalAnalysis.RankThreeTheoremC.map_perfectCore_comap ψ hψs ⊤
    Group.IsPerfect.commutator_eq_top
  rw [Subgroup.comap_top] at hPψ
  set Pc := CFSG.LocalAnalysis.RankThreeTheoremC.perfectCore (⊤ : Subgroup W₀)
  have hPerf : Group.IsPerfect (Pc.map ρ) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator,
      CFSG.LocalAnalysis.RankThreeTheoremC.commutator_perfectCore]
  have hout : ∀ L' : Subgroup (N ⧸ O), IsComponentOf L' ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥L' ⧸ Subgroup.center ↥L')) := by
    intro L' hL'
    have hK' : CFSG.Open.IsKGroup L' := catalogSimpleSections_iff_isKGroup.mp
      (((catalogSimpleSections_of_isKProper hKP N hNtop).quotient _).subgroup L')
    exact hSch _ hL'.2.2.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL'.2.2)
      (isCatalogGroup_center_quotient hK' hL'.2.2)
  have hPρ := le_layer_sup_centralizer_of_isPerfect he.ne_two hcoreY hrankY hout hPerf
  have hT : (Pc ⊓ (CFSG.layer (N ⧸ O)).comap ρ).map ψ = ⊥ := by
    refine eq_bot_of_normal_le_d1X0 h31 hKP he hB hBH hHtop hKH ⟨fun t ht k => ?_⟩ ?_
    · obtain ⟨w, hw, rfl⟩ := ht
      obtain ⟨x, hx, rfl⟩ : k ∈ Pc.map ψ := hPψ ▸ Subgroup.mem_top k
      refine ⟨x * w * x⁻¹, ⟨Pc.mul_mem (Pc.mul_mem hx hw.1) (Pc.inv_mem hx), ?_⟩, by
        rw [map_mul, map_mul, map_inv]⟩
      show ρ (x * w * x⁻¹) ∈ CFSG.layer (N ⧸ O)
      rw [map_mul, map_mul, map_inv]
      exact (inferInstance : (CFSG.layer (N ⧸ O)).Normal).conj_mem _ hw.2 _
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨m, hm, hmw⟩ := hlayerX hw.2
      have h1 : πN (m⁻¹ * Subgroup.inclusion hW₀N w) = 1 := by
        rw [map_mul, map_inv, hmw]
        exact inv_mul_cancel _
      have hoM : ((m⁻¹ * Subgroup.inclusion hW₀N w : N) : G) ∈ M :=
        core_le_of_base (muAt_of_escape he) hB' hB'N
          ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
      have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
      have ewm : (w : G) = (m : G) * ((m⁻¹ * Subgroup.inclusion hW₀N w : N) : G) := by simp
      refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.inclusion hW₀H w, Subgroup.mem_subgroupOf.mpr
        ⟨hW₀H w.2, ?_⟩, rfl⟩
      show (w : G) ∈ M
      rw [ewm]
      exact M.mul_mem hmM hoM
  obtain ⟨U, φ₀, hUC, hφ₀⟩ :=
    exists_le_centralizer_surjective ψ ρ (CFSG.layer (N ⧸ O)) Pc hPψ hPρ hT
  set C := Subgroup.centralizer (CFSG.layer (N ⧸ O) : Set (N ⧸ O))
  have hinvU : CFSG.QuasiDihedralFusion.Involves U L :=
    involves_trans (CFSG.QuasiDihedralFusion.involves_of_surjective φ₀ hφ₀)
      ⟨L.subgroupOf (d1KBar p M H), (Subgroup.subgroupOfEquivOfLe (le_d1KBar hL hLX)).toMonoidHom,
        (Subgroup.subgroupOfEquivOfLe (le_d1KBar hL hLX)).surjective⟩
  obtain ⟨J, φ, hφ⟩ :=
    hinvU.of_injective (Subgroup.inclusion hUC) (Subgroup.inclusion_injective hUC)
  obtain ⟨hLs, hLnab, -⟩ := isSimpleGroup_catalog_of_component h31 hKP he hB hBH hHtop hL hLX
  have hL2 := sq_dvd_card_component_of_escape h31 h75 hR1 hSyl hS hKP he hB hBH hHtop hL hLX
  have hrankC : CFSG.Open.pRank p (⊤ : Subgroup C) ≤ 2 := by
    have e : (⊤ : Subgroup C).map C.subtype = C := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp C.subtype
      C.subtype_injective, e]
    exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top).trans hrankY
  exact false_of_pRank_le_two_of_surjective he.ne_two
    (primeComplementCore_centralizer_layer_eq_bot hcoreY) layer_centralizer_layer_eq_bot hrankC
    hLs hLnab φ hφ hL2

theorem d1KBar_ne_bot_of_cover (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut)
    (hSch : KFactCatalogSchreier) (h74 : AGL81SevenFourTwo) (hOutC : KFactOutCyclic)
    (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B B' H N : Subgroup G}
    (hB : IsAGLQ p M B) (hBH : B ≤ H) (hB' : IsAGLQ p M B') (hB'N : B' ≤ N)
    (hHtop : H ≠ ⊤) (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) (hcov : AGLCovers p H N (d1KBar p M H)) :
    d1KBar p M N ≠ ⊥ := by
  have hNtop : N ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hS.simple hS.nonab hN.1
  obtain ⟨R, -, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB' hB'N
  by_cases h3 : 3 ≤ CFSG.Open.pRank p R
  · exact d1KBar_ne_bot_of_three_le h31 h75 hR1 hSyl h74 hOutC hS hKP he hB hBH hHtop hL hLX hN
      hNM hcov hRM hR h3
  · exact d1KBar_ne_bot_of_pRank_le_two_of_bases h31 h75 hR1 hSyl hSch hS hKP he hB hBH hB' hB'N
      hHtop hNtop hL hLX hcov hR (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
