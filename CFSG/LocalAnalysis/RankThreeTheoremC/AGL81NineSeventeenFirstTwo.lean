module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenOf
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerRankTwo
import CFSG.LocalAnalysis.GLTheoremA.S8.Close

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

section Abstract

theorem exists_le_centralizer_surjective {W Y K : Type*} [Group W] [Group Y] [Group K]
    (ψ : W →* K) (ρ : W →* Y) (E : Subgroup Y) [hE : E.Normal] (P : Subgroup W)
    (hPψ : P.map ψ = ⊤) (hPρ : P.map ρ ≤ E ⊔ Subgroup.centralizer (E : Set Y))
    (hT : (P ⊓ E.comap ρ).map ψ = ⊥) :
    ∃ (U : Subgroup Y) (φ : U →* K), U ≤ Subgroup.centralizer (E : Set Y) ∧
      Function.Surjective φ := by
  classical
  set C := Subgroup.centralizer (E : Set Y)
  set Q : Subgroup Y := E ⊔ P.map ρ with hQ
  have hρQ : ∀ x : P, ρ x ∈ Q := fun x => Subgroup.mem_sup_right (Subgroup.mem_map_of_mem ρ x.2)
  haveI hEQn : (E.subgroupOf Q).Normal := Subgroup.Normal.subgroupOf hE Q
  set ρQ : P →* Q := (ρ.comp P.subtype).codRestrict Q hρQ
  set σ : P →* Q ⧸ E.subgroupOf Q := (QuotientGroup.mk' (E.subgroupOf Q)).comp ρQ
  have hσs : Function.Surjective σ := by
    intro z
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf Q) z
    have hq : (q : Y) ∈ ((E : Set Y) * (P.map ρ : Set Y)) := by
      rw [← Subgroup.normal_mul]
      exact q.2
    obtain ⟨e, he, _, ⟨x, hx, rfl⟩, hqe⟩ := hq
    refine ⟨⟨x, hx⟩, ?_⟩
    change (QuotientGroup.mk' (E.subgroupOf Q)) (ρQ ⟨x, hx⟩) =
      (QuotientGroup.mk' (E.subgroupOf Q)) q
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have hq' : (q : Y) = e * ρ x := hqe.symm
    have e1 : (((ρQ ⟨x, hx⟩)⁻¹ * q : Q) : Y) = (ρ x)⁻¹ * (e * ρ x) := by
      show (ρ x)⁻¹ * (q : Y) = _
      rw [hq']
    rw [e1]
    have := hE.conj_mem e he (ρ x)⁻¹
    simpa [mul_assoc] using this
  set ψP : P →* K := ψ.comp P.subtype
  have hψPs : Function.Surjective ψP := by
    intro k
    obtain ⟨x, hx, rfl⟩ : k ∈ P.map ψ := hPψ ▸ Subgroup.mem_top k
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : σ.ker ≤ ψP.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxE : ρ x ∈ E := by
      have h1 := (QuotientGroup.eq_one_iff (ρQ x)).mp hx
      exact Subgroup.mem_subgroupOf.mp h1
    have h2 : ψP x ∈ (P ⊓ E.comap ρ).map ψ := ⟨x, ⟨x.2, hxE⟩, rfl⟩
    rwa [hT, Subgroup.mem_bot] at h2
  obtain ⟨φ₁, hφ₁, -, -⟩ := CFSG.AGLEmbedding.exists_surjective_comp_eq σ hσs ψP hψPs hker
  refine ⟨C ⊓ Q, φ₁.comp ((QuotientGroup.mk' (E.subgroupOf Q)).comp
    (Subgroup.inclusion inf_le_right)), inf_le_left, ?_⟩
  intro k
  obtain ⟨x, rfl⟩ := hψPs k
  have hx : ρ x ∈ ((E : Set Y) * (C : Set Y)) := by
    rw [← Subgroup.normal_mul]
    exact hPρ (Subgroup.mem_map_of_mem ρ x.2)
  obtain ⟨e, he, c, hc, hec⟩ := hx
  have hce : c = e⁻¹ * ρ x := by rw [← hec]; group
  have hcQ : c ∈ Q := by
    rw [hce]
    exact Q.mul_mem (Subgroup.mem_sup_left (E.inv_mem he)) (hρQ x)
  refine ⟨⟨c, hc, hcQ⟩, ?_⟩
  rw [← hφ₁ x]
  change φ₁ ((QuotientGroup.mk' (E.subgroupOf Q)) ⟨c, hcQ⟩) =
    φ₁ ((QuotientGroup.mk' (E.subgroupOf Q)) (ρQ x))
  congr 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e2 : (((⟨c, hcQ⟩ : Q))⁻¹ * ρQ x : Q) = (c⁻¹ * ρ x : Y) := rfl
  rw [e2, hce]
  have := hE.conj_mem e he (ρ x)⁻¹
  simpa [mul_assoc] using this

private theorem involves_trans_aux {A B C : Type*} [Group A] [Group B] [Group C]
    (hAB : CFSG.QuasiDihedralFusion.Involves A B) (hBC : CFSG.QuasiDihedralFusion.Involves B C) :
    CFSG.QuasiDihedralFusion.Involves A C := by
  obtain ⟨U, φ, hφ⟩ := hAB
  obtain ⟨V, ψ, hψ⟩ := hBC
  refine ⟨(V.comap φ).map U.subtype, ψ.comp ((φ.subgroupComap V).comp
    ((V.comap φ).equivMapOfInjective U.subtype U.subtype_injective).symm.toMonoidHom), ?_⟩
  exact hψ.comp ((φ.subgroupComap_surjective V hφ).comp (MulEquiv.surjective _))

theorem isCatalogGroup_center_quotient {Y : Type*} [Group Y] (hY : CFSG.Open.IsKGroup Y)
    (hq : CFSG.Open.IsQuasisimple Y) : IsCatalogGroup (Y ⧸ Subgroup.center Y) := by
  have hsimple : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  let e : (↥(⊤ : Subgroup Y) ⧸ (Subgroup.center Y).subgroupOf ⊤) ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)
  have : ((Subgroup.center Y).subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf inferInstance ⊤
  have hcat' := hY ⊤ (Subgroup.center Y) le_top (e.isSimpleGroup_congr.2 hsimple)
    (by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩)
  obtain ⟨i, ⟨f⟩⟩ := hcat'
  exact ⟨i, ⟨e.symm.trans f⟩⟩

end Abstract

variable {G : Type} [Group G] [Finite G]

theorem d1KBar_ne_bot_of_pRank_le_two (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut)
    (hSch : KFactCatalogSchreier) (hS : Setting G) (hKP : CFSG.Open.IsKProper G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B H N : Subgroup G}
    (hB : IsAGLQ p M B) (hBH : B ≤ H) (hBN : B ≤ N) (hHtop : H ≠ ⊤) (hNtop : N ≠ ⊤)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) (hcov : AGLCovers p H N (d1KBar p M H))
    (hr : ∀ R : Subgroup G, R ≤ M → CFSG.Quasithin.IsSylowIn p R N →
      CFSG.Open.pRank p R ≤ 2) :
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
  obtain ⟨R, -, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  have hrankY : CFSG.Open.pRank p (⊤ : Subgroup (N ⧸ O)) ≤ 2 := by
    refine pRank_le_of_sylow_inf (hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O))
      Subgroup.IsSubnormal.top ?_
    rw [inf_top_eq, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow,
      pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
    exact hr R hRM hR
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
        core_le_of_base (muAt_of_escape he) hB hBN ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
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
    involves_trans_aux (CFSG.QuasiDihedralFusion.involves_of_surjective φ₀ hφ₀)
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

theorem agl81NineSeventeenNotConstrainedTwo_holds (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR1 : KFactNineThreeListRankOne) (hSyl : KFactCaseTwoSylowAut)
    (hSch : KFactCatalogSchreier) (hS : Setting G) :
    AGL81NineSeventeenNotConstrainedTwo G := by
  intro hg p P M H hμ hH hHM hKex B N hB hBH hN hNM hBN hcov hr
  obtain ⟨H₁, R₁, he⟩ := hμ.escape
  obtain ⟨L, hL, hLX⟩ := hKex
  exact d1KBar_ne_bot_of_pRank_le_two h31 h75 hR1 hSyl hSch hS hg.kProper he hB hBH hBN
    (CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hH.1)
    (CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hg.simple hg.nonab hN.1) hL hLX hcov hr

theorem agl81NineCompetitorQ_of_threeKFacts (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hOut : KFactNineThreeOutPClosed) (hR1 : KFactNineThreeListRankOne)
    (hSyl : KFactCaseTwoSylowAut) (hSch : KFactCatalogSchreier) (h74 : AGL81SevenFourTwo)
    (hOutC : KFactOutCyclic) (hS : Setting G) : AGL81NineCompetitorQ G :=
  agl81NineCompetitorQ_of_nineSeventeen h31 h75 hOut hR1 hSyl hSch h74 hOutC
    (agl81NineSeventeenNotConstrainedTwo_holds h31 h75 hR1 hSyl hSch hS) hS

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
