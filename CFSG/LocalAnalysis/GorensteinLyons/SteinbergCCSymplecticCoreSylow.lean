module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCNestedCoreCenters
public import CFSG.Quasithin.SteinbergCCSylowNormalizerBootstrap

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

instance normal_range_mulAutConj (Q : Type*) [Group Q] :
    ((MulAut.conj : Q →* MulAut Q).range).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α g, MulEquiv.ext fun x => ?_⟩
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_eq_of_unique_involution_center {Q : Subgroup G} {z : G}
    (hzZ : z ∈ (center Q).map Q.subtype)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z) (hz : orderOf z = 2)
    {g : G} (hg : g ∈ normalizer (Q : Set G)) : g * z * g⁻¹ = z := by
  obtain ⟨c, hc, rfl⟩ := hzZ
  refine huniq _ ⟨Q.normalizerMonoidHom ⟨g, hg⟩ c, ?_, rfl⟩ ?_
  · have h := characteristic_iff_map_eq.mp (inferInstance : (center Q).Characteristic)
      (Q.normalizerMonoidHom ⟨g, hg⟩)
    rw [← h]
    exact mem_map_of_mem _ hc
  · change orderOf ((Q.normalizerMonoidHom ⟨g, hg⟩ c : Q) : G) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hz

theorem conj_mem_center_map {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G)) {y : G}
    (hy : y ∈ (center Q).map Q.subtype) : g * y * g⁻¹ ∈ (center Q).map Q.subtype := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨Q.normalizerMonoidHom ⟨g, hg⟩ c, ?_, rfl⟩
  have h := characteristic_iff_map_eq.mp (inferInstance : (center Q).Characteristic)
    (Q.normalizerMonoidHom ⟨g, hg⟩)
  rw [← h]
  exact mem_map_of_mem _ hc

theorem symplectic_core_central_involution_sylow [Finite G] {M : Subgroup G}
    (hM : CFSG.Open.GLAIsMaxTwoLocal M) (hchar : IsCharacteristicP 2 M)
    (hsym : CFSG.Open.GLASymplecticType (CFSG.Open.pCoreOf 2 M)) :
    let Q := (CFSG.pCore 2 M).map M.subtype
    let ZQ := (center Q).map Q.subtype
    Q ≠ ⊥ ∧ IsCyclic ZQ ∧
      ∃ z ∈ ZQ, orderOf z = 2 ∧ (∀ y ∈ ZQ, orderOf y = 2 → y = z) ∧
        M = centralizer {z} ∧ M = normalizer (Q : Set G) ∧ M = normalizer (ZQ : Set G) ∧
        (∀ T : Subgroup G, IsSylowOf 2 T M →
          IsSylowOf 2 T ⊤ ∧ (center T).map T.subtype ≤ ZQ ∧ omegaOneCenterOf 2 T = zpowers z) ∧
        M ⊓ centralizer (Q : Set G) = ZQ ∧ generalizedFitting M = CFSG.pCore 2 M ∧
        ∃ f : M ⧸ CFSG.pCore 2 M →* MulAut (CFSG.pCore 2 M) ⧸
            (MulAut.conj : CFSG.pCore 2 M →* MulAut (CFSG.pCore 2 M)).range,
          Function.Injective f ∧
            ∀ m : M, f m = (MulAut.conjNormal m : MulAut (CFSG.pCore 2 M)) := by
  intro Q ZQ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQeq : CFSG.Open.pCoreOf 2 M = Q := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  rw [hQeq] at hsym
  obtain ⟨hQ2, hcyc⟩ := hsym
  have hQM : Q ≤ M := map_subtype_le _
  have hsub : Q.subgroupOf M = CFSG.pCore 2 M :=
    comap_map_eq_self_of_injective (subtype_injective _) _
  have hMQ : M ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQM).mp (by rw [hsub]; infer_instance)
  have hmemQ : ∀ m : M, (m : G) ∈ Q ↔ m ∈ CFSG.pCore 2 M := fun m =>
    mem_map_iff_mem (subtype_injective M)
  obtain ⟨U, hU1, hU2, hMU⟩ := hM.1
  have hUM : U ≤ M := by rw [hMU]; exact le_normalizer
  have hUQ : U ≤ Q := by
    have hn : (U.subgroupOf M).Normal :=
      (normal_subgroupOf_iff_le_normalizer hUM).mpr (by rw [hMU])
    have h2 : IsPGroup 2 (U.subgroupOf M) := hU2.of_equiv (subgroupOfEquivOfLe hUM).symm
    have h3 := CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup hn h2
    intro u hu
    exact ⟨⟨u, hUM hu⟩, h3 (mem_subgroupOf.mpr hu), rfl⟩
  have hQne : Q ≠ ⊥ := fun h => hU1 (eq_bot_iff.mpr (h ▸ hUQ))
  have hZcyc : IsCyclic (center Q) := hcyc (center Q) inferInstance inferInstance
  have hZQcyc : IsCyclic ZQ :=
    isCyclic_of_surjective ((center Q).equivMapOfInjective Q.subtype
      (subtype_injective Q)).toMonoidHom (MulEquiv.surjective _)
  have : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQne
  have : Nontrivial (center Q) := hQ2.center_nontrivial
  obtain ⟨k, hk⟩ := (hQ2.to_subgroup (center Q)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card (α := center Q)).ne' hk
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  set z : G := ((c : Q) : G) with hzdef
  have hzZ : z ∈ ZQ := ⟨c, c.2, rfl⟩
  have hzord : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have huniq : ∀ y ∈ ZQ, orderOf y = 2 → y = z := by
    rintro _ ⟨c', hc', rfl⟩ hy
    have hy' : orderOf (⟨c', hc'⟩ : center Q) = 2 := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
      exact hy
    exact congrArg (fun w : center Q => ((w : Q) : G)) (eq_of_orderOf_eq_two_of_isCyclic hy' hc)
  have hzQ : z ∈ Q := (c : Q).2
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzord; exact absurd hzord (by norm_num)
  have hconj : ∀ g ∈ normalizer (Q : Set G), g * z * g⁻¹ = z := fun g hg =>
    conj_eq_of_unique_involution_center hzZ huniq hzord hg
  have hcent : ∀ g : G, g * z * g⁻¹ = z → g ∈ centralizer ({z} : Set G) := fun g h => by
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  have hMz : M ≤ centralizer ({z} : Set G) := fun m hm => hcent m (hconj m (hMQ hm))
  have hCN : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) :=
    CFSG.Quasithin.SteinbergCC.le_normalizer_of_conj_mem fun g hg y hy => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      have h1 : g * z * g⁻¹ = z := by
        rw [mem_centralizer_singleton_iff] at hg
        rw [hg, mul_inv_cancel_right]
      rw [← conj_zpow, h1]
      exact zpow_mem (mem_zpowers z) j
  have hloc : CFSG.Open.IsTwoLocal (normalizer (zpowers z : Set G)) :=
    ⟨zpowers z, fun h => hz1 (by rw [← mem_bot, ← h]; exact mem_zpowers z),
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one]), rfl⟩
  have hNzM : normalizer (zpowers z : Set G) = M := hM.2 _ hloc (hMz.trans hCN)
  have hMC : M = centralizer {z} := le_antisymm hMz (hCN.trans hNzM.le)
  have hMNQ : M = normalizer (Q : Set G) :=
    le_antisymm hMQ fun g hg => hMC ▸ hcent g (hconj g hg)
  have hMZQ : M ≤ normalizer (ZQ : Set G) :=
    CFSG.Quasithin.SteinbergCC.le_normalizer_of_conj_mem fun m hm y hy =>
      conj_mem_center_map (hMQ hm) hy
  have hMNZ : M = normalizer (ZQ : Set G) := by
    refine le_antisymm hMZQ fun g hg => hMC ▸ hcent g ?_
    refine huniq _ ((mem_normalizer_iff.mp hg z).mp hzZ) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hzord]
  have hCMQ : M ⊓ centralizer (Q : Set G) = ZQ := by
    refine le_antisymm (fun x hx => ?_) (le_inf ((map_subtype_le _).trans hQM) ?_)
    · obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
      have h1 : (⟨x, hxM⟩ : M) ∈ centralizer (CFSG.pCore 2 M : Set M) := by
        rw [mem_centralizer_iff]
        intro q hq
        exact Subtype.ext ((mem_centralizer_iff.mp hxC) q ((hmemQ q).mpr hq))
      have hxQ : x ∈ Q := (hmemQ _).mpr (hchar h1)
      exact ⟨⟨x, hxQ⟩, mem_center_iff.mpr fun q =>
        Subtype.ext ((mem_centralizer_iff.mp hxC) q q.2), rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨q, hq⟩)
  refine ⟨hQne, hZQcyc, z, hzZ, hzord, huniq, hMC, hMNQ, hMNZ, ?_, hCMQ,
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore M 2).mp hchar, ?_⟩
  ·
    intro T hT
    obtain ⟨hTM, hT2, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
    have hQT : Q ≤ T := by
      have h := CFSG.Quasithin.SteinbergCC.eq_of_isSylowOf_of_le hT (sup_le hTM hQM)
        (hT2.to_sup_of_normal_right' hQ2 (hTM.trans hMQ)) le_sup_left
      rw [← h]
      exact le_sup_right
    have hZT : (center T).map T.subtype ≤ ZQ := by
      rintro _ ⟨x, hx, rfl⟩
      refine hCMQ ▸ mem_inf.mpr ⟨hTM x.2, ?_⟩
      rw [mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨q, hQT hq⟩)
    have hzT : z ∈ T := hQT hzQ
    have hzC : z ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      have h1 := hMC ▸ hTM ht
      exact mem_centralizer_singleton_iff.mp h1
    have hz2 : z ^ 2 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    have hΩ : omegaOneCenterOf 2 T = zpowers z := by
      refine le_antisymm (fun y hy => ?_) (zpowers_le.mpr ⟨hzT, hzC, hz2⟩)
      obtain ⟨hyT, hyC, hy2⟩ := hy
      have hyZ : y ∈ ZQ := hZT ⟨⟨y, hyT⟩, mem_center_iff.mpr fun t =>
        Subtype.ext ((mem_centralizer_iff.mp hyC) t t.2), rfl⟩
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem _
      · rw [huniq y hyZ (orderOf_eq_prime hy2 hy1)]
        exact mem_zpowers z
    have hNT : normalizer (T : Set G) ≤ M := by
      intro g hg
      refine hMC ▸ hcent g ?_
      have h1 : g * z * g⁻¹ ∈ omegaOneCenterOf 2 T := by
        refine ⟨(mem_normalizer_iff.mp hg z).mp hzT, ?_, by rw [conj_pow, hz2, mul_one,
          mul_inv_cancel]⟩
        rw [mem_centralizer_iff]
        intro t ht
        have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ T := (mem_normalizer_iff.mp (inv_mem hg) t).mp ht
        rw [inv_inv] at ht'
        have h2 := (mem_centralizer_iff.mp hzC) _ ht'
        calc t * (g * z * g⁻¹) = g * (g⁻¹ * t * g * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
          _ = g * z * g⁻¹ * t := by group
      rw [hΩ] at h1
      rcases eq_one_or_eq_of_mem_zpowers hzord h1 with h | h
      · exfalso
        apply hz1
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      · exact h
    obtain ⟨S, hTS⟩ := hT2.exists_le_sylow
    have hTeq : T = S := by
      by_contra hne
      have hlt : T.subgroupOf S < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hTS fun s hs => ?_)
        have h1 : (⟨s, hs⟩ : S) ∈ T.subgroupOf S := htop ▸ mem_top _
        exact mem_subgroupOf.mp h1
      have h1 := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition
        S.isPGroup' hlt
      rw [← subgroupOf_normalizer_eq hTS] at h1
      have h2 : (normalizer (T : Set G)).subgroupOf S = T.subgroupOf S := by
        rw [← inf_subgroupOf_left]
        congr 1
        exact CFSG.Quasithin.SteinbergCC.eq_of_isSylowOf_of_le hT (inf_le_right.trans hNT)
          (S.isPGroup'.to_le inf_le_left) (le_inf hTS le_normalizer)
      exact absurd h1 (by rw [h2]; exact lt_irrefl _)
    refine ⟨?_, hZT, hΩ⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right, hTeq]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  ·
    let ψ : M →* MulAut (CFSG.pCore 2 M) ⧸
        (MulAut.conj : CFSG.pCore 2 M →* MulAut (CFSG.pCore 2 M)).range :=
      (QuotientGroup.mk' _).comp MulAut.conjNormal
    have hψ : CFSG.pCore 2 M ≤ ψ.ker := fun q hq => by
      rw [MonoidHom.mem_ker]
      change ((MulAut.conjNormal q : MulAut (CFSG.pCore 2 M)) : MulAut (CFSG.pCore 2 M) ⧸
        (MulAut.conj : CFSG.pCore 2 M →* MulAut (CFSG.pCore 2 M)).range) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨⟨q, hq⟩, MulEquiv.ext fun x => Subtype.ext rfl⟩
    refine ⟨QuotientGroup.lift _ ψ hψ, ?_, fun m => QuotientGroup.lift_mk _ hψ m⟩
    rw [injective_iff_map_eq_one]
    intro v hv
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.lift_mk] at hv
    change ((MulAut.conjNormal m : MulAut (CFSG.pCore 2 M)) : MulAut (CFSG.pCore 2 M) ⧸
      (MulAut.conj : CFSG.pCore 2 M →* MulAut (CFSG.pCore 2 M)).range) = 1 at hv
    rw [QuotientGroup.eq_one_iff] at hv
    obtain ⟨q, hq⟩ := hv
    have h1 : (q : M)⁻¹ * m ∈ centralizer (CFSG.pCore 2 M : Set M) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h2 := congrArg (fun φ : MulAut (CFSG.pCore 2 M) => ((φ ⟨x, hx⟩ : CFSG.pCore 2 M) : M))
        hq
      change (q : M) * x * (q : M)⁻¹ = m * x * m⁻¹ at h2
      calc x * ((q : M)⁻¹ * m) = (q : M)⁻¹ * ((q : M) * x * (q : M)⁻¹) * m := by group
        _ = (q : M)⁻¹ * (m * x * m⁻¹) * m := by rw [h2]
        _ = (q : M)⁻¹ * m * x := by group
    rw [QuotientGroup.eq_one_iff]
    rw [show m = (q : M) * ((q : M)⁻¹ * m) by group]
    exact mul_mem q.2 (hchar h1)

end CFSG.LocalAnalysis.GorensteinLyons
