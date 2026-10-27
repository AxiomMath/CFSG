module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUDecomp
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

section Generic

variable {G : Type} [Group G]

theorem card_mem_subgroupOf_sq_eq {C M : Subgroup G} (hCM : C ≤ M) (m : M) :
    Nat.card {v : M // v ∈ C.subgroupOf M ∧ v ^ 2 = m} =
      Nat.card {w : G // w ∈ C ∧ w ^ 2 = (m : G)} :=
  Nat.card_congr
    { toFun := fun v => ⟨v.1, Subgroup.mem_subgroupOf.mp v.2.1, by
        rw [← Subgroup.coe_pow, v.2.2]⟩
      invFun := fun w => ⟨⟨w.1, hCM w.2.1⟩, Subgroup.mem_subgroupOf.mpr w.2.1,
        Subtype.ext (by simpa using w.2.2)⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }

theorem normalizer_le_normalizer_centralizer_inf (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (S : Set G) ⊓ S : Subgroup G) : Set G) := by
  refine normalizer_le_normalizer_of_characteristic inf_le_right ?_
  have h : (Subgroup.centralizer (S : Set G) ⊓ S).subgroupOf S = Subgroup.center S := by
    ext v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_center_iff]
    constructor
    · rintro ⟨hv, -⟩ g
      exact Subtype.ext (hv g g.2)
    · intro hv
      exact ⟨fun g hg => congrArg Subtype.val (hv ⟨g, hg⟩), v.2⟩
  rw [h]
  infer_instance

theorem nonempty_mulEquiv_of_range_eq_map_subtype {A B : Type*} [Group A] [Group B] {ψ : A →* B}
    (hψ : Function.Injective ψ) {J : Subgroup B} {Q : Subgroup J}
    (h : ψ.range = Q.map J.subtype) : Nonempty (A ≃* Q) :=
  ⟨(MonoidHom.ofInjective hψ).trans ((MulEquiv.subgroupCongr h).trans
    (Q.equivMapOfInjective J.subtype J.subtype_injective).symm)⟩

theorem inv_mul_mul_mem_of_mem_normalizer {S : Subgroup G} {n z : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (hz : z ∈ S) : n⁻¹ * z * n ∈ S := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) z).mp hz
  rwa [inv_inv] at h

end Generic

section Setting

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
include hset hz hesc hJ hzJ

theorem false_of_sylow_le_component_sup_centralizer
    (hS : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)))
    {q n : ℕ} (hq : Even q) (hn : 0 < n)
    (hroot : ∀ R : Sylow 2 J, BenderRootData (R : Subgroup J) q n)
    (hcase : n ≠ q ∨ ∀ R : Sylow 2 J, BenderCenterSqOne (R : Subgroup J)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq' := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have := hq'.component_normal hJ hzJ
  set M := Subgroup.centralizer ({z} : Set G) with hMdef
  set K := Subgroup.centralizer (J : Set (EscapingQuotient z)) with hKdef
  have hSM : (S : Subgroup G) ≤ M := hz.le_centralizer
  set P : Subgroup M := (S : Subgroup G).subgroupOf M with hPdef
  set Sbar : Sylow 2 (EscapingQuotient z) :=
    (S.subtype hSM).mapSurjective (QuotientGroup.mk'_surjective _) with hSbardef
  have hSbar : (Sbar : Subgroup (EscapingQuotient z)) = P.map (escapingMk z) := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  set R : Subgroup M := J.comap (escapingMk z) ⊓ P with hRdef
  set T : Subgroup M := K.comap (escapingMk z) ⊓ P with hTdef
  set zM : M := escapingSelf z with hzMdef
  have hinj : ∀ a ∈ P, ∀ b ∈ P, escapingMk z a = escapingMk z b → a = b :=
    fun a ha b hb h => escapingMk_injOn_twoGroup S.isPGroup' (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb) h
  have hJK := hq'.component_inf_centralizer_eq_bot hJ hzJ
  have hcomm : ∀ x ∈ R, ∀ k ∈ T, x * k = k * x := by
    intro x hx k hk
    refine hinj _ (P.mul_mem hx.2 hk.2) _ (P.mul_mem hk.2 hx.2) ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hk.1 _ hx.1
  have hdisj : ∀ g ∈ R, g ∈ T → g = 1 := by
    intro g hgR hgT
    refine hinj _ hgR.2 _ P.one_mem ?_
    have h : escapingMk z g ∈ J ⊓ K := Subgroup.mem_inf.mpr ⟨hgR.1, hgT.1⟩
    rw [hJK, Subgroup.mem_bot] at h
    rw [h, map_one]
  have hgen : ∀ w ∈ P, ∃ x ∈ R, ∃ k ∈ T, x * k = w := by
    intro w hw
    have hS' : (Sbar : Subgroup (EscapingQuotient z)) ≤ J ⊔ K := by
      rw [hSbar]
      exact hS
    have hwS : escapingMk z w ∈ (Sbar : Subgroup (EscapingQuotient z)) := by
      rw [hSbar]
      exact Subgroup.mem_map_of_mem _ hw
    obtain ⟨x', hx', k', hk', hxk'⟩ := exists_mul_eq_of_le_sup_centralizer Sbar hJK hS' hwS
    have hx'S : x' ∈ P.map (escapingMk z) := hSbar ▸ (Subgroup.mem_inf.mp hx').1
    have hk'S : k' ∈ P.map (escapingMk z) := hSbar ▸ (Subgroup.mem_inf.mp hk').1
    obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hx'S
    obtain ⟨k, hkP, rfl⟩ := Subgroup.mem_map.mp hk'S
    exact ⟨x, ⟨(Subgroup.mem_inf.mp hx').2, hxP⟩, k, ⟨(Subgroup.mem_inf.mp hk').2, hkP⟩,
      hinj _ (P.mul_mem hxP hkP) _ hw (by rw [map_mul, hxk'])⟩
  have hzMP : zM ∈ P := Subgroup.mem_subgroupOf.mpr hz.1
  have hzMT : zM ∈ T := ⟨hq'.bar_mem_component_centralizer, hzMP⟩
  have hzM2 : orderOf zM = 2 := orderOf_escapingSelf hz.2.1
  have hzM1 : zM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzM2
    exact absurd hzM2 (by norm_num)
  have hzMsq : zM ^ 2 = 1 := hzM2 ▸ pow_orderOf_eq_one zM
  have hTinv : ∀ k ∈ T, k ^ 2 = 1 → k = 1 ∨ k = zM := by
    intro k hk hk2
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · exact Or.inr (hinj _ hk.2 _ hzMP (hq'.eq_bar_of_mem_component_centralizer hJ hzJ hk.1
        (escaping_orderOf_mk z (orderOf_eq_prime hk2 hk1))))
  have hT2 : IsPGroup 2 T := (S.isPGroup'.comap_subtype (K := M)).to_le inf_le_right
  set R' := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal Sbar J
  have hR'map := CFSG.ProperTwoGeneratedCore.normal_sylow_intersection_eq Sbar J
  let ψ : R →* EscapingQuotient z := (escapingMk z).comp R.subtype
  have hψ : Function.Injective ψ := fun a b h => Subtype.ext (hinj _ a.2.2 _ b.2.2 h)
  have hψr : ψ.range = (R' : Subgroup J).map J.subtype := by
    rw [hR'map]
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, r.2.1⟩
      rw [hSbar]
      exact Subgroup.mem_map_of_mem _ r.2.2
    · intro hy
      have hyS : y ∈ P.map (escapingMk z) := hSbar ▸ (Subgroup.mem_inf.mp hy).1
      obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hyS
      exact ⟨⟨x, (Subgroup.mem_inf.mp hy).2, hxP⟩, rfl⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_of_range_eq_map_subtype hψ hψr
  have hrootR : BenderRootData R q n := (hroot R').congr θ.symm
  have hcaseR : n ≠ q ∨ BenderCenterSqOne R := hcase.imp_right fun h => (h R').congr θ.symm
  set ZS : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ S with hZSdef
  have hZSM : ZS ≤ M := inf_le_right.trans hSM
  have hZ : ∀ v, v ∈ ZS.subgroupOf M ↔ v ∈ P ∧ ∀ y ∈ P, v * y = y * v := by
    intro v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hc, hvS⟩
      exact ⟨hvS, fun y hy => Subtype.ext (hc y (Subgroup.mem_subgroupOf.mp hy)).symm⟩
    · rintro ⟨hvS, hc⟩
      refine ⟨fun g hg => ?_, hvS⟩
      exact (congrArg Subtype.val (hc ⟨g, hSM hg⟩ (Subgroup.mem_subgroupOf.mpr hg))).symm
  set A : Set M := {m | ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
    g⁻¹ * z * g = (m : G)} with hAdef
  have hA : Odd (Nat.card A) := by
    have e : A ≃ {w : G // ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
        g⁻¹ * z * g = w} :=
      { toFun := fun m => ⟨m.1, m.2⟩
        invFun := fun w => ⟨⟨w.1, hSM (by
          obtain ⟨g, hg, hgw⟩ := w.2
          rw [← hgw]
          exact inv_mul_mul_mem_of_mem_normalizer hg hz.1)⟩, w.2⟩
        left_inv := fun m => rfl
        right_inv := fun w => rfl }
    rw [Nat.card_congr e]
    exact sylow_normalizer_class_card_odd S hz.1 hz.2.2
  have hzA : zM ∈ A := ⟨1, Subgroup.one_mem _, by rw [inv_one, one_mul, mul_one]⟩
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz.2.1
  have hAinv : ∀ w ∈ A, w ∈ P ∧ w ^ 2 = 1 ∧ w ≠ 1 := by
    rintro w ⟨g, hg, hgw⟩
    refine ⟨Subgroup.mem_subgroupOf.mpr (hgw ▸ inv_mul_mul_mem_of_mem_normalizer hg hz.1),
      Subtype.ext ?_, fun h => ?_⟩
    · rw [Subgroup.coe_pow, ← hgw, Subgroup.coe_one]
      calc (g⁻¹ * z * g) ^ 2 = g⁻¹ * (z * z) * g := by rw [pow_two]; group
        _ = 1 := by rw [hz2]; group
    · have h1 : g⁻¹ * z * g = 1 := by rw [hgw, h, Subgroup.coe_one]
      have h2 : z = 1 := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have h3 := hz.2.1
      rw [h2, orderOf_one] at h3
      exact absurd h3 (by norm_num)
  have hAP : ∀ w ∈ A, Nat.card {v : M // v ∈ P ∧ v ^ 2 = w} =
      Nat.card {v : M // v ∈ P ∧ v ^ 2 = zM} := by
    rintro w ⟨g, hg, hgw⟩
    rw [card_mem_subgroupOf_sq_eq hSM, card_mem_subgroupOf_sq_eq hSM, ← hgw]
    exact card_pow_eq_conj_of_mem_normalizer _ hg 2 z
  have hAZ : ∀ w ∈ A, Nat.card {v : M // v ∈ ZS.subgroupOf M ∧ v ^ 2 = w} =
      Nat.card {v : M // v ∈ ZS.subgroupOf M ∧ v ^ 2 = zM} := by
    rintro w ⟨g, hg, hgw⟩
    rw [card_mem_subgroupOf_sq_eq hZSM, card_mem_subgroupOf_sq_eq hZSM, ← hgw]
    exact card_pow_eq_conj_of_mem_normalizer _
      (normalizer_le_normalizer_centralizer_inf (S : Subgroup G) hg) 2 z
  have hcent : ∀ r ∈ R, r ^ 2 = 1 → ∀ s ∈ (S : Subgroup G), s * (r : G) = (r : G) * s := by
    intro r hr hr2 s hs
    obtain ⟨x, hx, t, ht, hxt⟩ := hgen ⟨s, hSM hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
    have hrx : r * x = x * r := congrArg Subtype.val
      (hrootR.comm ⟨r, hr⟩ (Subtype.ext (by simpa using hr2)) ⟨x, hx⟩)
    have h : (⟨s, hSM hs⟩ : M) * r = r * ⟨s, hSM hs⟩ := by
      rw [← hxt, mul_assoc, ← hcomm r hr t ht, ← mul_assoc, ← hrx, mul_assoc]
    exact congrArg Subtype.val h
  obtain ⟨v, hzv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hset.simple hset.nonabelian hz.2.1
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hvz : (v : G) ≠ z := fun h => hvbar (by rw [eq_escapingSelf h])
  have hJc := hq'.caseOneConfig hJ hzJ
  have hzbar : escapingMk z zM = escapingBar z := rfl
  have hfus : (∀ r ∈ R, r ^ 2 = 1 → r ≠ 1 → r ∈ A) ∨
      (∀ r ∈ R, r ^ 2 = 1 → r ≠ 1 → r * zM ∈ A) := by
    rcases hJc.involution_mem _ (escaping_orderOf_mk z hv2') with hvJ | hvJ
    · refine Or.inl fun r hr hr2 hr1 => ?_
      have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
      have hrc : IsCentralInvolution (S : Subgroup G) (r : G) :=
        ⟨Subgroup.mem_subgroupOf.mp hr.2, by rw [Subgroup.orderOf_coe]; exact hro,
          hcent r hr hr2⟩
      obtain ⟨g, hg, -, hgr⟩ := coreSetting_centralInvolution_fusion hset hz hrc
        (hzv.trans (hJc.isConj_of_mk_mem hv2' hro hvJ hr.1))
      exact ⟨g, hg, hgr⟩
    · refine Or.inr fun r hr hr2 hr1 => ?_
      have hro : orderOf r = 2 := orderOf_eq_prime hr2 hr1
      have hrz : r ≠ zM := by
        intro h
        apply hzJ
        have h1 := hr.1
        rw [h] at h1
        exact h1
      have hrzc : Commute r zM := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.2)
      have hrzo : orderOf (r * zM) = 2 := orderOf_mul_eq_two_of_commute hro hzM2 hrzc hrz
      have hrzJ : escapingBar z * escapingMk z (r * zM) ∈ J := by
        have h : escapingBar z * escapingMk z (r * zM) = escapingMk z r := by
          rw [map_mul, hzbar, ← mul_assoc, ← (commute_escapingBar (escapingMk z r)).eq,
            mul_assoc, escapingBar_mul_self hz.2.1, mul_one]
        rw [h]
        exact hr.1
      have hrzz : ((r * zM : M) : G) ≠ z := by
        intro h
        apply hr1
        apply Subtype.ext
        change (r : G) * z = z at h
        rw [Subgroup.coe_one]
        exact mul_eq_right.mp h
      have hrzS : IsCentralInvolution (S : Subgroup G) ((r * zM : M) : G) := by
        refine ⟨(S : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.mp hr.2) hz.1,
          by rw [Subgroup.orderOf_coe]; exact hrzo, fun s hs => ?_⟩
        change s * ((r : G) * z) = (r : G) * z * s
        rw [← mul_assoc, hcent r hr hr2 s hs, mul_assoc, hz.2.2 s hs, mul_assoc]
      obtain ⟨g, hg, -, hgr⟩ := coreSetting_centralInvolution_fusion hset hz hrzS
        (hzv.trans (hJc.isConj_of_bar_mul_mk_mem hz.2.1 hv2' hrzo hvJ hrzJ hvz hrzz))
      exact ⟨g, hg, hgr⟩
  exact false_of_bender_root_counts inf_le_right inf_le_right hcomm hdisj hgen hzMT hzM1 hzMsq
    hTinv hT2 hq hn hrootR hcaseR hZ A hA hzA hAinv hAP hAZ hfus

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37
