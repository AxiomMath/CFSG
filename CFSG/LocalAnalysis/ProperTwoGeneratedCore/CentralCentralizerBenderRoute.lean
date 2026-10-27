module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki

section Helpers

variable {X : Type*} [Group X]

theorem isSimpleBenderGroup_commutator_eq_top [Finite X] (h : IsSimpleBenderGroup X) :
    commutator X = ⊤ := by
  have := h.isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h1 | h1
  · refine absurd (fun a b => ?_) h.not_commutative
    have hc := (commutator_eq_bot_iff_center_eq_top X).mp h1
    exact (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a)
  · exact h1

theorem isSimpleBenderGroup_center_eq_bot [Finite X] (h : IsSimpleBenderGroup X) :
    Subgroup.center X = ⊥ := by
  have := h.isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exact absurd (fun a b => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a))
      h.not_commutative

theorem commutator_self_eq_of_commutator_eq_top {K : Subgroup X} (h : commutator K = ⊤) :
    ⁅K, K⁆ = K := by
  have hmap := Subgroup.map_commutator (⊤ : Subgroup K) ⊤ K.subtype
  rw [← commutator_def, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm

theorem commutator_eq_top_of_commutator_self_eq {K : Subgroup X} (h : ⁅K, K⁆ = K) :
    commutator K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]

theorem isComponent_of_normal_of_simple_quotient [Finite X] {L : Subgroup X} [L.Normal]
    (hperf : commutator L = ⊤) (hsimple : IsSimpleGroup (L ⧸ Subgroup.center L)) :
    CFSG.IsComponent L :=
  (CFSG.isComponent_iff_open L).mpr ⟨le_top,
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤), hperf, hsimple⟩

theorem le_of_normal_of_odd_index [Finite X] {P : Subgroup X} [P.Normal] (hP : Odd P.index)
    {T : Subgroup X} (hT : IsPGroup 2 T) : T ≤ P := by
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : QuotientGroup.mk' P t ^ 2 ^ k = 1 := by
    rw [← map_pow, show t ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, map_one]
  have hodd : Odd (Nat.card (⊤ : Subgroup (X ⧸ P))) := by
    rwa [Subgroup.card_top, ← Subgroup.index_eq_card]
  have h1 := eq_one_of_pow_two_pow_eq_one_of_odd hodd (Subgroup.mem_top _) hk'
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

end Helpers

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

namespace EscapingQuotientData

variable (hq : EscapingQuotientData H x) (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x)
include hq hsq

theorem bender_route_component
    {N : Subgroup (BenderQuotient x)} [N.Normal]
    (hNodd : Odd N.index) (hNB : IsSimpleBenderGroup N)
    (hxD : escapingBar x ∉ ⁅N.comap (benderMk x), N.comap (benderMk x)⁆) :
    ∃ J : Subgroup (EscapingQuotient x), CFSG.IsComponent J ∧ escapingBar x ∉ J ∧
      ¬ J ≤ escapingImage H x ∧ IsSimpleBenderGroup J ∧ fusionIsBenderGroup J ∧
      Odd (J ⊔ Subgroup.zpowers (escapingBar x)).index ∧
      Subgroup.centralizer (J : Set (EscapingQuotient x)) = Subgroup.zpowers (escapingBar x) := by
  have := hNB.isSimple
  set P := N.comap (benderMk x)
  set D := ⁅P, P⁆
  have hDmap : D.map (benderMk x) = N := by
    rw [Subgroup.map_commutator,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      commutator_self_eq_of_commutator_eq_top (isSimpleBenderGroup_commutator_eq_top hNB)]
  have hDP : D ⊔ Subgroup.zpowers (escapingBar x) = P := by
    have h := Subgroup.comap_map_eq (benderMk x) D
    rw [hDmap, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hinj : Function.Injective ((benderMk x).domRestrict D) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk',
      Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro y hy hyD
    rcases eq_one_or_eq_of_mem_zpowers hq.bar_order hy with h | h
    · exact h
    · exact absurd (h ▸ hyD) hxD
  let e : D ≃* N := (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range, hDmap]))
  have hDB : IsSimpleBenderGroup D := hNB.map_mulEquiv e.symm
  have hDcomp : CFSG.IsComponent D := by
    refine isComponent_of_normal_of_simple_quotient (isSimpleBenderGroup_commutator_eq_top hDB) ?_
    have := hDB.isSimple
    exact ((QuotientGroup.quotientMulEquivOfEq (isSimpleBenderGroup_center_eq_bot hDB)).trans
      QuotientGroup.quotientBot).isSimpleGroup
  have := hq.component_centralizer_normal hDcomp hxD
  refine ⟨D, hDcomp, hxD, hq.component_not_le_image hDcomp hxD, hDB,
    fusionIsBenderGroup_of_isSimpleBenderGroup hDB, ?_, le_antisymm ?_ ?_⟩
  · rw [hDP, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hNodd
  · exact normal_le_zpowers_of_unique_involution hq.oddCore_eq_bot hq.bar_mem_center
      (fun n hn hn2 => hq.eq_bar_of_mem_component_centralizer hDcomp hxD hn hn2) fun n _ => hsq n
  · exact Subgroup.zpowers_le.mpr hq.bar_mem_component_centralizer

omit hsq in
theorem bender_route_quasisimple
    {N : Subgroup (BenderQuotient x)} [N.Normal]
    (hNodd : Odd N.index) (hNB : IsSimpleBenderGroup N)
    (hxD : escapingBar x ∈ ⁅N.comap (benderMk x), N.comap (benderMk x)⁆) :
    ∃ J : Subgroup (EscapingQuotient x), J.Normal ∧ CFSG.IsComponent J ∧ escapingBar x ∈ J ∧
      Odd J.index ∧ ¬ J ≤ escapingImage H x ∧
      (Subgroup.center J).map J.subtype = Subgroup.zpowers (escapingBar x) ∧
      fusionIsBenderGroup (J ⧸ Subgroup.center J) := by
  have := hNB.isSimple
  set P := N.comap (benderMk x)
  have hPmap : P.map (benderMk x) = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N
  have hPperf : ⁅P, P⁆ = P := by
    have h := Subgroup.comap_map_eq (benderMk x) ⁅P, P⁆
    rw [Subgroup.map_commutator, hPmap,
      commutator_self_eq_of_commutator_eq_top (isSimpleBenderGroup_commutator_eq_top hNB),
      QuotientGroup.ker_mk', sup_eq_left.mpr (Subgroup.zpowers_le.mpr hxD)] at h
    exact h.symm
  have hxP : escapingBar x ∈ P := hPperf ▸ hxD
  have hPidx : Odd P.index := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hNodd
  let φ : P →* N := ((benderMk x).domRestrict P).codRestrict N fun p =>
    Subgroup.mem_comap.mp p.property
  have hφ : Function.Surjective φ := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ n
    exact ⟨⟨m, hn⟩, rfl⟩
  have hker : φ.ker = (Subgroup.zpowers (escapingBar x)).subgroupOf P := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (c : EscapingQuotient x)
  have hcenter : Subgroup.center P = φ.ker := by
    apply le_antisymm
    · intro c hc
      have hcN : φ c ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun n => by
        obtain ⟨p, rfl⟩ := hφ n
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc p)]
      rw [isSimpleBenderGroup_center_eq_bot hNB, Subgroup.mem_bot] at hcN
      exact hcN
    · intro c hc
      rw [hker, Subgroup.mem_subgroupOf] at hc
      refine Subgroup.mem_center_iff.mpr fun p => Subtype.ext ?_
      rcases eq_one_or_eq_of_mem_zpowers hq.bar_order hc with h | h
      · simp only [Subgroup.coe_mul, h, mul_one, one_mul]
      · simp only [Subgroup.coe_mul, h]
        exact (commute_escapingBar _).eq
  let e : P ⧸ Subgroup.center P ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hPcomp : CFSG.IsComponent P :=
    isComponent_of_normal_of_simple_quotient (commutator_eq_top_of_commutator_self_eq hPperf)
      e.isSimpleGroup
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  have hUP : (U : Subgroup (EscapingQuotient x)) ≤ P := le_of_normal_of_odd_index hPidx U.isPGroup'
  have hPrank : 2 ≤ CFSG.Open.pRank 2 P := by
    have h1 := CFSG.SectionRank.pRank_mono (by decide : 1 < 2) hUP
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq] at h1
    have := hq.rank
    omega
  refine ⟨P, inferInstance, hPcomp, hxP, hPidx,
    CFSG.ProperTwoGeneratedCore.normal_rank_two_not_le_overgroup U _ hq.image_ne_top hUH hcore P
      hPrank, ?_, fusionIsBenderGroup_of_isSimpleBenderGroup (hNB.map_mulEquiv e.symm)⟩
  rw [hcenter, hker, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxP)]

theorem bender_route :
    (∃ J : Subgroup (EscapingQuotient x), CFSG.IsComponent J ∧ escapingBar x ∉ J ∧
      ¬ J ≤ escapingImage H x ∧ IsSimpleBenderGroup J ∧ fusionIsBenderGroup J ∧
      Odd (J ⊔ Subgroup.zpowers (escapingBar x)).index ∧
      Subgroup.centralizer (J : Set (EscapingQuotient x)) = Subgroup.zpowers (escapingBar x)) ∨
    (∃ J : Subgroup (EscapingQuotient x), J.Normal ∧ CFSG.IsComponent J ∧ escapingBar x ∈ J ∧
      Odd J.index ∧ ¬ J ≤ escapingImage H x ∧
      (Subgroup.center J).map J.subtype = Subgroup.zpowers (escapingBar x) ∧
      fusionIsBenderGroup (J ⧸ Subgroup.center J)) := by
  obtain ⟨N, hN, hNodd, hNB⟩ := hq.exists_benderQuotient_normal_simpleBender hsq
  by_cases hxD : escapingBar x ∈ ⁅N.comap (benderMk x), N.comap (benderMk x)⁆
  · exact Or.inr (hq.bender_route_quasisimple hNodd hNB hxD)
  · exact Or.inl (hq.bender_route_component hsq hNodd hNB hxD)

end EscapingQuotientData

theorem coreSetting_bender_route
    {S : Sylow 2 G} {z : G} (hset : CoreSetting G S H)
    (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsq : ∀ v ∈ (S : Subgroup G), v ^ 2 ≠ z) :
    (fixedSetKernel H z).subgroupOf (Subgroup.centralizer ({z} : Set G)) =
      (Subgroup.zpowers (escapingBar z)).comap (escapingMk z) ∧
    ((∃ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J ∧ escapingBar z ∉ J ∧
      ¬ J ≤ escapingImage H z ∧ IsSimpleBenderGroup J ∧ fusionIsBenderGroup J ∧
      Odd (J ⊔ Subgroup.zpowers (escapingBar z)).index ∧
      Subgroup.centralizer (J : Set (EscapingQuotient z)) = Subgroup.zpowers (escapingBar z)) ∨
    (∃ J : Subgroup (EscapingQuotient z), J.Normal ∧ CFSG.IsComponent J ∧ escapingBar z ∈ J ∧
      Odd J.index ∧ ¬ J ≤ escapingImage H z ∧
      (Subgroup.center J).map J.subtype = Subgroup.zpowers (escapingBar z) ∧
      fusionIsBenderGroup (J ⧸ Subgroup.center J))) := by
  have hzH : z ∈ H := hset.sylow_le hz.1
  have hq := escapingQuotientData hset hzH hz.2.1 hesc
  have hsq' := centralInvolution_not_sq_bar hz hsq
  exact ⟨coreSetting_fixedSetKernel_eq_comap_zpowers hset hzH hz.2.1 hesc hsq',
    hq.bender_route hsq'⟩

end CFSG.ProperTwoGeneratedCore.Assembly
