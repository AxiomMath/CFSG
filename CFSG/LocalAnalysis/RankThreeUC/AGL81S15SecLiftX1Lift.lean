module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Centre
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81FiveTwentySixStar
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbExtra

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC

variable {X : Type} [Group X] [Finite X]

theorem isC2_subgroupOf_of_normal {L M : Subgroup X} (hLn : L.Normal) (hLM : L ≤ M)
    (hL : IsC2 L) : IsC2 (L.subgroupOf M) := by
  haveI := hLn
  have hLn' : (L.subgroupOf M).Normal := Subgroup.normal_subgroupOf
  have hodd : oddHull (L.subgroupOf M) = L.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    calc (oddHull (L.subgroupOf M)).map M.subtype = oddHull L := by
          simp only [oddHull, MonoidHom.map_closure]
          congr 1
          ext y
          simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.mem_subgroupOf,
            Subgroup.coe_subtype]
          constructor
          · rintro ⟨x, ⟨hx, hxo⟩, rfl⟩
            exact ⟨hx, by rwa [Subgroup.orderOf_coe]⟩
          · rintro ⟨hy, hyo⟩
            exact ⟨⟨y, hLM hy⟩, ⟨hy, by rwa [Subgroup.orderOf_mk]⟩, rfl⟩
      _ = L := hL.2.1
      _ = (L.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hLM).symm
  have hO : ∀ x (hx : x ∈ L), x ∈ CFSG.pCore 2 X ↔ (⟨x, hLM hx⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := by
    intro x hx
    constructor
    · intro h
      haveI : ((CFSG.pCore 2 X).subgroupOf M).Normal := Subgroup.normal_subgroupOf
      exact isC2_normalizer_aux0 (IsPGroup.comap_of_injective CFSG.pCore_isPGroup M.subtype
        M.subtype_injective) (Subgroup.mem_subgroupOf.mpr h)
    · intro h
      set N : Subgroup ↥L := ((CFSG.pCore 2 ↥M).map M.subtype).subgroupOf L with hN
      haveI hNn : N.Normal := ⟨fun n hn l => by
        rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
        obtain ⟨m, hm, hmn⟩ := hn
        have hmn' : (m : X) = n := hmn
        refine ⟨⟨(l : X), hLM l.2⟩ * m * ⟨(l : X), hLM l.2⟩⁻¹,
          (inferInstance : (CFSG.pCore 2 ↥M).Normal).conj_mem m hm _, ?_⟩
        simp [hmn']⟩
      have hNp : IsPGroup 2 N := IsPGroup.comap_of_injective
        (IsPGroup.map CFSG.pCore_isPGroup M.subtype) L.subtype L.subtype_injective
      have hxN : (⟨x, hx⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr ⟨⟨x, hLM hx⟩, h, rfl⟩
      exact CFSG.AGLEmbeddingD2.map_pCore_le_pCore_of_normal L
        ⟨⟨x, hx⟩, isC2_normalizer_aux0 hNp hxN, rfl⟩
  let π : ↥L →* ↥(barO2 L) := (QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap L
  let π₁ : ↥L →* ↥((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap (L.subgroupOf M)).comp
      (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hπ : Function.Surjective π := MonoidHom.subgroupMap_surjective _ _
  have hπ₁ : Function.Surjective π₁ := (MonoidHom.subgroupMap_surjective _ _).comp
    (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  have hker : π.ker = π₁.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, Subtype.ext_iff]
    change (QuotientGroup.mk (x : X) : X ⧸ CFSG.pCore 2 X) = 1 ↔
      (QuotientGroup.mk (⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) = 1
    rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    exact hO x x.2
  have e : ↥(barO2 L) ≃* ↥((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :=
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁)
  refine ⟨CFSG.Open.IsSubnormal.of_mathlib hLn'.isSubnormal, hodd, le_top,
    CFSG.Open.IsSubnormal.of_mathlib
      (hLn'.map _ (QuotientGroup.mk'_surjective _)).isSubnormal, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hL.component.2.2

theorem not_subgroupOf_le_gnC_subgroupOf {T L M : Subgroup X} (hTM : T ≤ M) (hLM : L ≤ M)
    (hLn : L.Normal) (hLC : ¬ L ≤ gnC T) : ¬ L.subgroupOf M ≤ gnC (T.subgroupOf M) := by
  intro h
  apply hLC
  refine le_gnC_of_normal hLn fun x hx => ?_
  have h1 : (⟨x, hLM hx⟩ : ↥M) ∈ gnC (T.subgroupOf M) := h (Subgroup.mem_subgroupOf.mpr hx)
  rw [gnC_subgroupOf_eq hTM, Subgroup.mem_subgroupOf] at h1
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (omegaOneCenterOf_le_uCore M T)) h1

theorem not_le_gnC_of_liftOf {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hcomp : CFSG.Open.IsComponentOf Ls ⊤) (hlift : LiftOf T L Ls) : ¬ L ≤ gnC T := by
  intro h
  apply CFSG.LocalAnalysis.ComponentInitial.ne_bot_of_isComponentOf
    (CFSG.Assembly.isComponentOf_iff_open.2 hcomp)
  rw [← hlift.2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact h

theorem isComponentOf_map_toStar_subgroupOf {T L M : Subgroup X} (hTM : T ≤ M) (hLM : L ≤ M)
    (hLn : L.Normal) (hgn : GNSetting ↥M (T.subgroupOf M)) (hL : IsC2 L) (hLC : ¬ L ≤ gnC T) :
    CFSG.Open.IsComponentOf ((L.subgroupOf M).map (toStar (T.subgroupOf M))) ⊤ :=
  CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix.isComponentOf_map_toStar hgn
    (isC2_subgroupOf_of_normal hLn hLM hL) (not_subgroupOf_le_gnC_subgroupOf hTM hLM hLn hLC)

theorem not_map_toStar_subgroupOf_le_gnImg_centralizer {T T₁ L M : Subgroup X} (hTM : T ≤ M)
    (hLM : L ≤ M) (hT₁ : T₁ ≤ CFSG.Quasithin.omegaOneCenterOf T)
    (h : ¬ L.map (toStar T) ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))) :
    ¬ (L.subgroupOf M).map (toStar (T.subgroupOf M)) ≤
      gnImg (T.subgroupOf M) (Subgroup.centralizer ((T₁.subgroupOf M : Subgroup ↥M) : Set ↥M)) := by
  intro hle
  apply h
  have hT₁U : T₁ ≤ uCore M T := hT₁.trans (omegaOneCenterOf_le_uCore M T)
  have hLc : L ≤ Subgroup.centralizer (T₁ : Set X) := by
    intro l hl
    have hl' : toStar (T.subgroupOf M) ⟨l, hLM hl⟩ ∈
        (L.subgroupOf M).map (toStar (T.subgroupOf M)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
    obtain ⟨c, hc, hce⟩ := hle hl'
    have hk : c⁻¹ * ⟨l, hLM hl⟩ ∈ gnC (T.subgroupOf M) := QuotientGroup.eq.mp hce
    rw [gnC_subgroupOf_eq hTM, Subgroup.mem_subgroupOf] at hk
    have hk' : ((c⁻¹ * ⟨l, hLM hl⟩ : ↥M) : X) ∈ Subgroup.centralizer (T₁ : Set X) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hT₁U) hk
    have hc' : c ∈ Subgroup.centralizer ((T₁.subgroupOf M : Subgroup ↥M) : Set ↥M) := hc
    rw [Subgroup.mem_centralizer_iff] at hc' hk' ⊢
    intro t ht
    have htM : t ∈ M := uCore_le_of_le hTM (hT₁U ht)
    have h1 : t * (c : X) = c * t :=
      congrArg Subtype.val (hc' ⟨t, htM⟩ (Subgroup.mem_subgroupOf.mpr ht))
    have h2 : t * ((c : X)⁻¹ * l) = (c : X)⁻¹ * l * t := by simpa using hk' t ht
    calc t * l = t * c * ((c : X)⁻¹ * l) := by group
      _ = c * (t * ((c : X)⁻¹ * l)) := by rw [h1]; group
      _ = c * ((c : X)⁻¹ * l * t) := by rw [h2]
      _ = l * t := by group
  exact Subgroup.map_mono hLc

theorem gnYComponent_subgroupOf {T T₁ T₂ L M : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hTM : T ≤ M) (hLM : L ≤ M) (hLn : L.Normal) (hgn : GNSetting ↥M (T.subgroupOf M))
    (hT₁ : T₁ ≤ CFSG.Quasithin.omegaOneCenterOf T) (hcomp : GNYComponent T T₁ T₂ Ls)
    (hlift : LiftOf T L Ls)
    (h3 : ¬ (L.subgroupOf M).map (toStar (T.subgroupOf M)) ≤
      gnImg (T.subgroupOf M) (Subgroup.normalizer ((T₂.subgroupOf M : Subgroup ↥M) : Set ↥M))) :
    GNYComponent (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M)
      ((L.subgroupOf M).map (toStar (T.subgroupOf M))) := by
  refine ⟨isComponentOf_map_toStar_subgroupOf hTM hLM hLn hgn hlift.1
    (not_le_gnC_of_liftOf hcomp.1 hlift), ?_, h3⟩
  refine not_map_toStar_subgroupOf_le_gnImg_centralizer hTM hLM hT₁ ?_
  rw [hlift.2]
  exact hcomp.2.1

theorem liftCtxGen_subgroupOf {T T₁ T₂ L M : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hl : LiftCtxGen X T T₁ T₂ Ls L) (hLn : L.Normal) (hTM : T ≤ M) (hLM : L ≤ M)
    (hgn : GNSetting ↥M (T.subgroupOf M))
    (hg : GNGood (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M))
    (h3 : ¬ (L.subgroupOf M).map (toStar (T.subgroupOf M)) ≤
      gnImg (T.subgroupOf M) (Subgroup.normalizer ((T₂.subgroupOf M : Subgroup ↥M) : Set ↥M))) :
    LiftCtxGen ↥M (T.subgroupOf M) (T₁.subgroupOf M) (T₂.subgroupOf M)
      ((L.subgroupOf M).map (toStar (T.subgroupOf M))) (L.subgroupOf M) := by
  refine ⟨hgn, hg, ?_, ?_,
    gnYComponent_subgroupOf hTM hLM hLn hgn hl.good.pair.le_center hl.comp hl.lift h3,
    ⟨isC2_subgroupOf_of_normal hLn hLM hl.lift.1, rfl⟩⟩
  · exact (CFSG.SectionRank.pRank_le_map (by norm_num) M.subtype M.subtype_injective ⊤).trans
      ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hl.rank_three)
  · intro r hr hr2
    refine (CFSG.SectionRank.pRank_le_map hr.one_lt M.subtype M.subtype_injective _).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hLM]
    exact hl.rank_L r hr hr2

theorem nonempty_mulEquiv_map_toStar_subgroupOf {T L M : Subgroup X} (hTM : T ≤ M)
    (hLM : L ≤ M) (h : L ⊓ Subgroup.centralizer (uCore M T : Set X) ≤ gnC T) :
    Nonempty (↥(L.map (toStar T)) ≃* ↥((L.subgroupOf M).map (toStar (T.subgroupOf M)))) := by
  let ρ : ↥L →* ↥(L.map (toStar T)) := (toStar T).subgroupMap L
  let ρ₁ : ↥L →* ↥((L.subgroupOf M).map (toStar (T.subgroupOf M))) :=
    ((toStar (T.subgroupOf M)).subgroupMap (L.subgroupOf M)).comp
      (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  have hρ₁ : Function.Surjective ρ₁ := (MonoidHom.subgroupMap_surjective _ _).comp
    (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  have hker : ρ.ker = ρ₁.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff, Subtype.ext_iff]
    change (QuotientGroup.mk (x : X) : X ⧸ gnC T) = 1 ↔
      (QuotientGroup.mk (⟨x, hLM x.2⟩ : ↥M) : ↥M ⧸ gnC (T.subgroupOf M)) = 1
    rw [QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, gnC_subgroupOf_eq hTM,
      Subgroup.mem_subgroupOf]
    exact ⟨fun hx => gnC_le_centralizer_uCore M T hx, fun hx => h ⟨x.2, hx⟩⟩
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁)⟩

theorem inf_comap_centralizer_le_centralizer_uCore {T L M : Subgroup X} (hTM : T ≤ M)
    (hLM : L ≤ M)
    (hc : Subgroup.center ↥((L.subgroupOf M).map (toStar (T.subgroupOf M))) = ⊥) :
    L ⊓ (Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T))).comap (toStar T) ≤
      Subgroup.centralizer (uCore M T : Set X) := by
  intro z hz
  obtain ⟨hzL, hzc⟩ := hz
  have hzc' : toStar T z ∈ Subgroup.centralizer (L.map (toStar T) : Set (X ⧸ gnC T)) := hzc
  set Ls₁ := (L.subgroupOf M).map (toStar (T.subgroupOf M)) with hLs₁
  have hz₁ : toStar (T.subgroupOf M) ⟨z, hLM hzL⟩ ∈ Ls₁ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzL)
  have hcen : (⟨_, hz₁⟩ : ↥Ls₁) ∈ Subgroup.center ↥Ls₁ := by
    rw [CFSG.AGLEmbedding.mem_center_subtype_iff, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hlL : (l : X) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have h1 : toStar T (l : X) * toStar T z = toStar T z * toStar T (l : X) :=
      Subgroup.mem_centralizer_iff.mp hzc' _ (Subgroup.mem_map_of_mem _ hlL)
    rw [← map_mul, ← map_mul] at h1 ⊢
    have h2 : ((l : X) * z)⁻¹ * (z * l) ∈ gnC T := QuotientGroup.eq.mp h1
    have h3 : (l * ⟨z, hLM hzL⟩)⁻¹ * (⟨z, hLM hzL⟩ * l) ∈ gnC (T.subgroupOf M) := by
      rw [gnC_subgroupOf_eq hTM, Subgroup.mem_subgroupOf]
      exact gnC_le_centralizer_uCore M T (by simpa using h2)
    exact QuotientGroup.eq.mpr h3
  rw [hc, Subgroup.mem_bot] at hcen
  have h1 : toStar (T.subgroupOf M) ⟨z, hLM hzL⟩ = 1 := congrArg Subtype.val hcen
  have h2 := (QuotientGroup.eq_one_iff (N := gnC (T.subgroupOf M)) _).mp h1
  rw [gnC_subgroupOf_eq hTM, Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.LocalAnalysis.RankThreeUC.S15
