module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsE6
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_le_card_dvd_of_le_fixSubgroup_quot (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M : Subgroup G} (hZ : Odd (Nat.card (center M))) {X : Type*}
    [Group X] (eM : M ⧸ center M ≃* X) (htM : t ∈ normalizer (M : Set G)) {J : Subgroup X}
    (hJ : ⁅J, J⁆ = J) (hJfix : J ≤ E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) :
    ∃ P : Subgroup G, P ≤ L ∧ P ≤ M ⊓ centralizer ({t} : Set G) ∧ Nat.card J ∣ Nat.card P := by
  have : Finite X := Finite.of_equiv _ eM.toEquiv
  set π : M →* X := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  set S : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hS
  have hSπ : S.map π = E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) :=
    E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  set Q : Subgroup M := S ⊓ J.comap π with hQ
  have hQπ : Q.map π = J := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le π J)
    · intro j hj
      have hj' : j ∈ S.map π := hSπ ▸ hJfix hj
      obtain ⟨s, hs, rfl⟩ := hj'
      exact ⟨s, ⟨hs, hj⟩, rfl⟩
  have hP'π : (perfectCore Q).map π = J := by
    rw [CFSG.Quasithin.map_perfectCore, hQπ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hJ]
  have hQS : ∀ x ∈ perfectCore Q, (x : G) ∈ centralizer ({t} : Set G) := fun x hx =>
    mem_subgroupOf.1 (mem_inf.1 (CFSG.Quasithin.perfectCore_le Q hx)).1
  refine ⟨(perfectCore Q).map M.subtype, ?_, ?_, ?_⟩
  · refine std_perfect_le hset hOut htC ht ?_ ?_
    · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    · rintro _ ⟨x, hx, rfl⟩
      exact hQS x hx
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.2 ⟨x.2, hQS x hx⟩
  · rw [← hP'π, Subgroup.card_map_of_injective M.subtype_injective]
    exact Subgroup.card_map_dvd (perfectCore Q) π

theorem inf_centralizer_eq_of_quot_of_card (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {X : Type*} [Group X] (eM : M ⧸ center M ≃* X)
    (htM : t ∈ normalizer (M : Set G))
    (hperf : ⁅E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩),
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)⁆ =
        E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩))
    (hcard : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) = Nat.card L) :
    M ⊓ centralizer ({t} : Set G) = L := by
  obtain ⟨P, hPL, hPM, hdvd⟩ :=
    exists_le_card_dvd_of_le_fixSubgroup_quot hset hOut htC ht hZ eM htM hperf le_rfl
  rw [hcard] at hdvd
  have hPeq : P = L := Subgroup.eq_of_le_of_card_ge hPL (Nat.le_of_dvd Nat.card_pos hdvd)
  have hLM : L ≤ M ⊓ centralizer ({t} : Set G) := hPeq ▸ hPM
  set π : M →* X := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  set S : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hS
  have hSπ : S.map π = E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) :=
    E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hinj : Set.InjOn π S := by
    intro x hx y hy hxy
    have hxy' : y⁻¹ * x ∈ center M := by
      have h1 : (QuotientGroup.mk' (center M)) x = (QuotientGroup.mk' (center M)) y :=
        eM.injective hxy
      exact QuotientGroup.eq.1 h1.symm
    have hcL : ((y⁻¹ * x : M) : G) ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hlM : l ∈ M := (hLM hl).1
      have := mem_center_iff.1 hxy' ⟨l, hlM⟩
      exact congrArg Subtype.val this
    have hct : ((y⁻¹ * x : M) : G) ∈ centralizer ({t} : Set G) :=
      mul_mem (inv_mem (mem_subgroupOf.1 hy)) (mem_subgroupOf.1 hx)
    have hz : ((y⁻¹ * x : M) : G) ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hcL, hct⟩
    have hodd : Odd (orderOf (y⁻¹ * x)) := E6Pilot.odd_orderOf_of_mem_center hZ hxy'
    have hdvd2 : orderOf ((y⁻¹ * x : M) : G) ∣ 2 := by
      rw [← ht]
      exact orderOf_dvd_of_mem_zpowers hz
    rw [Subgroup.orderOf_coe] at hdvd2
    have h1 : orderOf (y⁻¹ * x) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1.symm
  have hcardS : Nat.card S = Nat.card L := by
    rw [← hcard, ← hSπ]
    exact (Nat.card_congr (Equiv.Set.imageOfInjOn π S hinj)).trans rfl
  refine (Subgroup.eq_of_le_of_card_ge hLM ?_).symm
  rw [← hcardS, ← Subgroup.card_map_of_injective M.subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm]

end Lift

section E6

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_inner_quot_E6_row (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : adjointGroup .E6 K₂ →* MulAut (adjointGroup .E6 K₂)).range := by
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  rintro ⟨c, hc⟩
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := E6Pilot.eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := E6Pilot.normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨u, hu⟩ : ∃ u : adjointGroup .E6 K₂, orderOf u = 2 :=
        ⟨_, E6Pilot.orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1)⟩
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [E6Pilot.mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := E6Pilot.odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : adjointGroup .E6 K₂ := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set (adjointGroup .E6 K₂)) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := E6Pilot.exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [E6Pilot.mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  have hdvd : 2 ^ (26 * f) ∣ Nat.card (centralizer ({t} : Set G)) := by
    refine (E6Pilot.two_pow_dvd_card_centralizer_E6 hK₂ hŵ).trans ?_
    refine (card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [← card_map_of_injective M.subtype_injective]
    exact card_dvd_of_le hleG
  exact not_two_pow_dvd_card_centralizer_F4 hset hf hK e htC ht hKt hdvd

theorem false_of_field_or_graphField_E6_quot (hset : StandardSetting G L) {f : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {K₂ : Type}
    [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K₂)
    (htM : t ∈ normalizer (M : Set G)) {σ : K₂ ≃+* K₂} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    {ε : ℕ} (hε : ε < 2) {φ : MulAut (adjointGroup TwistTag.E6.tag K₂)}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ =
      diagramConjAut TwistTag.E6 K₂ ^ ε * entrywiseAdjointAut TwistTag.E6.tag σ) : False := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  have hf := one_le_of_natCard_eq_two_pow hK₂
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨-, -, -, -, -, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K₂
  obtain ⟨⟨e', he'⟩, hσc, hcardk⟩ := hfield 2 f Nat.prime_two hf hK₂ σ hσ2 hσ1
  have hfe : f / 2 = e' := by omega
  have he1 : 1 ≤ e' := by omega
  have hK₂' : Nat.card K₂ = 2 ^ (2 * e') := by rw [hK₂, he', two_mul]
  have hσ' : ∀ c, σ c = c ^ (2 ^ e') := fun c => by rw [hσc, hfe]
  have hL : Nat.card L = CFSG.Open.ordF4 (2 ^ (2 * e')) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, he',
      two_mul]
  obtain ⟨hD0, hD1⟩ :=
    even_E6_canonical_field_graph_field_derived_fixed_subgroups he1 K₂ hK₂' σ hσ'
  set β := diagramConjAut TwistTag.E6 K₂ ^ ε * entrywiseAdjointAut TwistTag.E6.tag σ with hβ
  have hmap := map_eqLocus_eq_of_conj hφ
  have key : ∀ J : Subgroup (ModGL TwistTag.E6.tag K₂),
      DerivedFixedSubgroupData (adjointGroup TwistTag.E6.tag K₂) J β →
      4 ∣ Nat.card J → Nat.card J ∣ CFSG.Open.ordF4 (2 ^ (2 * e')) := by
    intro J hD h4
    obtain ⟨-, hJC, hder, -, hJs, -⟩ := hD
    have hJF : J.subgroupOf (adjointGroup TwistTag.E6.tag K₂) ≤ β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K₂)) := by
      rw [← hder]
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hJJ : ⁅J.subgroupOf (adjointGroup TwistTag.E6.tag K₂), J.subgroupOf (adjointGroup TwistTag.E6.tag K₂)⁆ = J.subgroupOf (adjointGroup TwistTag.E6.tag K₂) := by
      have hJtop := commutator_eq_top_of_isSimpleGroup_of_four_dvd hJs h4
      apply Subgroup.map_injective (adjointGroup TwistTag.E6.tag K₂).subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hJC, ← Subgroup.map_subtype_commutator, hJtop,
        ← MonoidHom.range_eq_map, range_subtype]
    set J' := (J.subgroupOf (adjointGroup TwistTag.E6.tag K₂)).map φ.symm.toMonoidHom with hJ'
    have hJ'fix : J' ≤ E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := hJF hy
      rw [← hmap] at hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      have hzy' : φ.symm y = z := by
        rw [MulEquiv.symm_apply_eq]
        exact hzy.symm
      change φ.symm y ∈ _
      rw [hzy']
      exact hz
    have hJ'perf : ⁅J', J'⁆ = J' := by rw [hJ', ← map_commutator, hJJ]
    obtain ⟨P, hPL, -, hdvd⟩ :=
      exists_le_card_dvd_of_le_fixSubgroup_quot hset hOut htC ht hZ eM htM hJ'perf hJ'fix
    have hcardJ' : Nat.card J' = Nat.card J := by
      rw [hJ', card_map_of_injective φ.symm.injective,
        Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv]
    rw [← hcardJ', ← hL]
    exact hdvd.trans (Subgroup.card_dvd_of_le hPL)
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    have hk : Nat.card (fixSubfield σ) = 2 ^ e' := by
      rw [← hfe, ← hcardk]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun c => Iff.rfl)
    have hJcard : Nat.card (fixedFieldImage TwistTag.E6.tag σ) = CFSG.Open.ordE6 (2 ^ e') := by
      rw [← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]
      have : Finite (fixSubfield σ) := Finite.of_injective _ Subtype.val_injective
      exact (CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6 (K := fixSubfield σ)).trans
        (by rw [hk])
    have h4 : 4 ∣ Nat.card (fixedFieldImage TwistTag.E6.tag σ) := by
      obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordE6' he1).two
      rw [hJcard, hr]
      exact Dvd.dvd.mul_right (dvd_trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2)
        (pow_dvd_pow 2 (by omega))) _
    have := key _ hD0 h4
    rw [hJcard] at this
    exact not_ordE6_dvd_ordF4 he1 this
  ·
    have hK₂'' : Nat.card K₂ = (2 ^ e') ^ 2 := by rw [hK₂', ← pow_mul, mul_comm]
    have hJcard : Nat.card (graphFixedRootGroup TwistTag.E6 K₂ σ.toRingHom) =
        CFSG.Open.ordTwistedE6 (2 ^ e') :=
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two he1 hK₂'' σ.toRingHom hσ'
    have h4 : 4 ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K₂ σ.toRingHom) := by
      obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordTwistedE6' he1).two
      rw [hJcard, hr]
      exact Dvd.dvd.mul_right (dvd_trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2)
        (pow_dvd_pow 2 (by omega))) _
    have := key _ hD1 h4
    rw [hJcard] at this
    exact not_ordTwistedE6_dvd_ordF4 he1 this

theorem inf_centralizer_eq_or_xi_E6_quot (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    (M ⊓ centralizer ({t} : Set G) = L ∧
      ∃ η : MulAut (adjointGroup TwistTag.E6.tag K₂),
        (∀ h : adjointGroup TwistTag.E6.tag K₂, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K₂),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = η) ∨
      ∃ η : MulAut (adjointGroup TwistTag.E6.tag K₂),
        (∀ h : adjointGroup TwistTag.E6.tag K₂, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K₂)
          (φ : MulAut (adjointGroup TwistTag.E6.tag K₂)),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η := by
  have := finite_of_natCard_eq_two_pow hK
  have := finite_of_natCard_eq_two_pow hK₂
  have := charP_two_of_natCard_eq_two_pow hK₂
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hα2 : normalizerQuotMulAut eM ⟨t, htM⟩ ^ 2 = 1 :=
    E6Pilot.normalizerQuotMulAut_sq_eq_one eM ht htM
  have hαo : normalizerQuotMulAut eM ⟨t, htM⟩ ∉ inner (adjointGroup TwistTag.E6.tag K₂) :=
    not_inner_quot_E6_row hset hf hK e htC ht hKt hMp hZ hK₂ eM htM
  rcases E6Pilot.outer_involution_cases_E6 (by omega) K₂ hK₂ _ hα2 hαo with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨hx, φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · refine Or.inl ⟨?_, η, hη, φ, hφ⟩
    have h2 : (2 : K₂) = 0 := CharTwo.two_eq_zero
    have hcan := canonicalGraphFixedSubgroup_adjointGroup K₂ (by omega) hK₂ h2
    obtain ⟨hperf, hcard⟩ := eqLocus_perfect_card_of_canonicalGraphFixedSubgroup hcan hη
      (graphFixedImageF4Equiv (RingHom.id K₂) h2) (CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 K₂)
    have hmap := map_eqLocus_eq_of_conj hφ
    refine inf_centralizer_eq_of_quot_of_card hset hOut htC ht hKt hZ eM htM ?_ ?_
    · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      change (⁅(normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _),
          (normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)⁆).map
            φ.toMonoidHom =
        ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)).map φ.toMonoidHom
      rw [map_commutator, hmap, hperf]
    · change Nat.card ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)) = _
      rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective, hmap, hcard,
        Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, hK₂]
  · exact Or.inr ⟨η, hη, hx, φ, hφ⟩
  · exact (false_of_field_or_graphField_E6_quot hset hK e htC ht hZ hK₂ eM htM hσ2 hσ1
      (ε := 0) (φ := φ) (by norm_num) (by rw [pow_zero, one_mul]; exact hφ)).elim
  · exact (false_of_field_or_graphField_E6_quot hset hK e htC ht hZ hK₂ eM htM hσ2 hσ1
      (ε := 1) (φ := φ) (by norm_num) (by rw [pow_one]; exact hφ)).elim

end E6

section TwistedE6

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inf_centralizer_eq_or_xi_twistedE6_quot (hset : StandardSetting G L) {f : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2)
    (σ : K₂ →+* K₂) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (htM : t ∈ normalizer (M : Set G))
    (hout : normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K₂ σ →* _).range) :
    (M ⊓ centralizer ({t} : Set G) = L ∧
      ∃ η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
          φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = η) ∨
      ∃ (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ)
        (φ η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)),
        (∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
          diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹) ∧
        φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η := by
  have := finite_of_natCard_eq_two_pow hK
  have hf : 1 ≤ f := one_le_of_natCard_eq_two_pow hK
  have hK₂' : Nat.card K₂ = 2 ^ (2 * f) := by rw [hK₂, ← pow_mul, mul_comm]
  have := charP_two_of_natCard_eq_two_pow hK₂'
  have : Finite K₂ := finite_of_natCard_eq_two_pow hK₂'
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hσσ := TwistedE6Pilot.apply_apply_eq hK₂ hσ
  rcases (TwistedE6Pilot.conj_etaAut_or_xiAut_of_outer hf hK₂ σ hσ).1 _
      (E6Pilot.normalizerQuotMulAut_sq_eq_one eM ht htM) hout with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · refine Or.inl ⟨?_, TwistedE6Pilot.etaAut σ hσσ, TwistedE6Pilot.coe_etaAut σ hσσ, φ, hφ⟩
    have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK₂
    let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
    have hk2 : ringChar (GaloisField 2 f) = 2 := ringChar.eq (GaloisField 2 f) 2
    have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
    have hcan := canonicalGraphFixedSubgroup_graphFixedRootGroup hf hk hK₂ hσ hk2
    obtain ⟨hperf, hcard⟩ := eqLocus_perfect_card_of_canonicalGraphFixedSubgroup hcan
      (TwistedE6Pilot.coe_etaAut σ hσσ)
      (graphFixedImageF4Equiv (algebraMap (GaloisField 2 f) K₂) h2)
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 (GaloisField 2 f))
    have hmap := map_eqLocus_eq_of_conj hφ
    refine inf_centralizer_eq_of_quot_of_card hset hOut htC ht hKt hZ eM htM ?_ ?_
    · apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      change (⁅(normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _),
          (normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)⁆).map
            φ.toMonoidHom =
        ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)).map φ.toMonoidHom
      rw [map_commutator, hmap, hperf]
    · change Nat.card ((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus (MonoidHom.id _)) = _
      rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective, hmap, hcard,
        Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
        CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK, hk]
  · exact Or.inr ⟨TwistedE6Pilot.pinnedX_highRoot_one_mem σ, φ, TwistedE6Pilot.etaAut σ hσσ,
      TwistedE6Pilot.coe_etaAut σ hσσ, hφ⟩

end TwistedE6

end CFSG.SeitzReduction.F4Pilot
