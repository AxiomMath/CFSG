module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem inf_center_ne_bot' [Finite G] {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := mem_inf.1 hy
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, mem_inf.2 ⟨mem_subgroupOf.1 hyU,
    mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun t ht => ?_⟩⟩⟩, fun h => hy1 ?_⟩
  · have := mem_center_iff.1 hyZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  · have h' : (y : G) = 1 := congrArg Subtype.val h
    have h'' : y = 1 := Subtype.ext h'
    exact Subtype.ext h''

theorem mem_gammaOneOn_of_commute_of_mem {U A : Subgroup G} {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    {x : G} (hxA : x ∈ A) (hx : x * u = u * x) : x ∈ gammaOneOn U A := by
  have hz : zpowers u ≠ ⊥ := fun h => hu1 (by
    have : u ∈ zpowers u := mem_zpowers u
    rwa [h, mem_bot] at this)
  have hle : A ⊓ normalizer (zpowers u : Set G) ≤ gammaOneOn U A :=
    le_iSup₂_of_le (zpowers u) ((zpowers_le).2 hu) (le_iSup_of_le hz le_rfl)
  refine hle (mem_inf.2 ⟨hxA, ?_⟩)
  rw [mem_normalizer_iff]
  intro y
  have hxu : Commute x u := hx
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    rw [(hxu.zpow_right n).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers u) n
  · intro hy
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hy
    have h2 : x * y * x⁻¹ = x * u ^ n * x⁻¹ := by
      rw [← hn, (hxu.zpow_right n).eq, mul_inv_cancel_right]
    have : y = u ^ n := by simpa using h2
    rw [this]
    exact zpow_mem (mem_zpowers u) n

theorem mem_gammaOneOn_of_commute {U : Subgroup G} {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) {x : G}
    (hx : x * u = u * x) : x ∈ gammaOneOn U ⊤ :=
  mem_gammaOneOn_of_commute_of_mem hu hu1 (mem_top x) hx

theorem frattini_map_le_of_sq [Finite G] {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hsq : ∀ x ∈ R, x ^ 2 ∈ K) : (frattini R).map R.subtype ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  rw [map_le_iff_le_comap, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
    closure_le]
  have hcomm : _root_.commutator R ≤ K.comap R.subtype := by
    rw [_root_.commutator_def, commutator_le]
    intro x _ y _
    rw [mem_comap, commutatorElement_def]
    simp only [coe_subtype, coe_mul, coe_inv]
    have e : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ =
        ((x : G) * x) * (((x : G)⁻¹ * y) * ((x : G)⁻¹ * y)) * ((y : G)⁻¹ * (y : G)⁻¹) := by
      group
    rw [e, ← sq, ← sq, ← sq]
    exact mul_mem (mul_mem (hsq _ x.2) (hsq _ (mul_mem (inv_mem x.2) y.2)))
      (hsq _ (inv_mem y.2))
  rintro x (hx | ⟨y, rfl⟩)
  · exact hcomm hx
  · rw [SetLike.mem_coe, mem_comap]
    simpa using hsq _ y.2

theorem exists_two_ne_one {T : Subgroup G} (hT : 4 ≤ Nat.card T) :
    ∃ u ∈ T, ∃ v ∈ T, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype T := Fintype.ofFinite T
  have h3 : 2 < (Finset.univ.erase (1 : T)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.1 (by omega : 1 < (Finset.univ.erase (1 : T)).card)
  rw [Finset.mem_erase] at ha hb
  exact ⟨a, a.2, b, b.2, fun h => ha.1 (Subtype.ext h), fun h => hb.1 (Subtype.ext h),
    fun h => hab (Subtype.ext h)⟩

theorem mem_normalizer_center {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((R ⊓ centralizer (R : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxR, hxC⟩
    refine ⟨(mem_normalizer_iff.1 hg x).1 hxR, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ R := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    have := mem_centralizer_iff.1 hxC _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * y := by group
  · rintro ⟨hxR, hxC⟩
    refine ⟨(mem_normalizer_iff.1 hg x).2 hxR, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g * y * g⁻¹ ∈ R := (mem_normalizer_iff.1 hg y).1 hy
    have := mem_centralizer_iff.1 hxC _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = x * y := by group

theorem lemma24In [Finite G] {A R U : Subgroup G} (hRA : R ≤ A) (hUA : U ≤ A)
    (hR : IsPGroup 2 R) (hU : IsElemAbelian 2 U) (hU4 : Nat.card U = 4)
    (hcomm : ∀ g ∈ A, rightConjugate R g ≠ R → ⁅R, rightConjugate R g⁆ = ⊥)
    (hΦ : frattini R ≠ ⊥) :
    (U ⊓ normalizer (R : Set G) ≠ ⊥ ∨ (frattini R).map R.subtype ≤ gammaOneOn U A) ∧
      gammaOneOn U A ⊓ (R ⊓ centralizer (R : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : ∀ x ∈ U, x ^ 2 = 1 := hU.2
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => by
    have h : (⟨x, hx⟩ : U) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hU.1.is_comm.comm _ _
    simpa using congrArg Subtype.val h
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU2 x hx)
  have hRw : ∀ w ∈ A, w ∉ normalizer (R : Set G) → ∀ a ∈ R, ∀ b ∈ rightConjugate R w,
      a * b = b * a := by
    intro w hwA hw a ha b hb
    have h := hcomm w hwA (fun h => hw ((rightConjugate_eq_self_iff R w).1 h))
    have hc : ⁅a, b⁆ ∈ ⁅R, rightConjugate R w⁆ := commutator_mem_commutator ha hb
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hRne : R ≠ ⊥ := fun h => hΦ (by
    rw [eq_bot_iff]
    intro x _
    have : (x : G) ∈ (⊥ : Subgroup G) := h ▸ x.2
    rw [mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this)
  have hfirst : U ⊓ normalizer (R : Set G) ≠ ⊥ ∨
      (frattini R).map R.subtype ≤ gammaOneOn U A := by
    by_cases hN : U ⊓ normalizer (R : Set G) = ⊥
    · right
      have hnot : ∀ w ∈ U, w ≠ 1 → w ∉ normalizer (R : Set G) := fun w hw hw1 hwN =>
        hw1 (by
          have : w ∈ U ⊓ normalizer (R : Set G) := mem_inf.2 ⟨hw, hwN⟩
          rwa [hN, mem_bot] at this)
      obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_ne_one (T := U) (by omega)
      have huvU : u * v ∈ U := mul_mem hu hv
      have huv1 : u * v ≠ 1 := fun h => huv (by
        rw [eq_inv_of_mul_eq_one_left h, hinv v hv])
      apply frattini_map_le_of_sq hR
      intro r hr
      have hu2 : u * u = 1 := by rw [← sq]; exact hU2 u hu
      have hv2 : v * v = 1 := by rw [← sq]; exact hU2 v hv
      have huv2 : (u * v) * (u * v) = 1 := by rw [← sq]; exact hU2 _ huvU
      have hvu : v * u = u * v := (hUc u hu v hv).symm
      have hconj : ∀ w : G, w * r * w⁻¹ ∈ rightConjugate R w⁻¹ := fun w => by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hr
      have hrA : r ∈ A := hRA hr
      have hwA : ∀ w ∈ A, w * r * w⁻¹ ∈ A := fun w hw => mul_mem (mul_mem hw hrA) (inv_mem hw)
      have hnot' : ∀ w ∈ U, w ≠ 1 → w⁻¹ ∉ normalizer (R : Set G) := fun w hw hw1 h =>
        hnot w hw hw1 (by simpa using inv_mem h)
      set ru := u * r * u⁻¹ with hru
      set rv := v * r * v⁻¹ with hrv
      set ruv := (u * v) * r * (u * v)⁻¹ with hruv
      have c1 : r * ru = ru * r :=
        hRw u⁻¹ (inv_mem (hUA hu)) (hnot' u hu hu1) r hr ru (hconj u)
      have c2 : r * ruv = ruv * r :=
        hRw _ (inv_mem (hUA huvU)) (hnot' _ huvU huv1) r hr ruv (hconj _)
      have c3 : ru * ruv = ruv * ru := by
        have h := hRw v⁻¹ (inv_mem (hUA hv)) (hnot' v hv hv1) r hr rv (hconj v)
        have e1 : ru * ruv = u * (r * rv) * u⁻¹ := by rw [hru, hruv, hrv]; group
        have e2 : ruv * ru = u * (rv * r) * u⁻¹ := by rw [hru, hruv, hrv]; group
        rw [e1, e2, h]
      have hcomm_of : ∀ w x : G, w * x * w⁻¹ = x → x * w = w * x := fun w x h => by
        calc x * w = w * x * w⁻¹ * w := by rw [h]
          _ = w * x := by group
      have h1 : r * ru ∈ gammaOneOn U A := by
        refine mem_gammaOneOn_of_commute_of_mem hu hu1
          (mul_mem hrA (hwA u (hUA hu))) (hcomm_of u _ ?_)
        calc u * (r * ru) * u⁻¹ = ru * ((u * u) * r * (u * u)⁻¹) := by rw [hru]; group
          _ = r * ru := by rw [hu2, one_mul, inv_one, mul_one, c1]
      have h2 : ru⁻¹ * ruv⁻¹ ∈ gammaOneOn U A := by
        refine mem_gammaOneOn_of_commute_of_mem hv hv1
          (mul_mem (inv_mem (hwA u (hUA hu))) (inv_mem (hwA _ (hUA huvU))))
          (hcomm_of v _ ?_)
        have ev1 : v * ru * v⁻¹ = ruv := by
          rw [hru, hruv]
          calc v * (u * r * u⁻¹) * v⁻¹ = (v * u) * r * (v * u)⁻¹ := by group
            _ = (u * v) * r * (u * v)⁻¹ := by rw [hvu]
        have ev2 : v * ruv * v⁻¹ = ru := by
          rw [hru, hruv]
          calc v * ((u * v) * r * (u * v)⁻¹) * v⁻¹ = (v * u * v) * r * (v * u * v)⁻¹ := by group
            _ = (u * v * v) * r * (u * v * v)⁻¹ := by rw [hvu]
            _ = u * r * u⁻¹ := by rw [mul_assoc u v v, hv2, mul_one]
        calc v * (ru⁻¹ * ruv⁻¹) * v⁻¹ = (v * ru * v⁻¹)⁻¹ * (v * ruv * v⁻¹)⁻¹ := by group
          _ = ruv⁻¹ * ru⁻¹ := by rw [ev1, ev2]
          _ = ru⁻¹ * ruv⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, c3]
      have h3 : r * ruv ∈ gammaOneOn U A := by
        refine mem_gammaOneOn_of_commute_of_mem huvU huv1
          (mul_mem hrA (hwA _ (hUA huvU))) (hcomm_of (u * v) _ ?_)
        calc (u * v) * (r * ruv) * (u * v)⁻¹ =
            ruv * (((u * v) * (u * v)) * r * ((u * v) * (u * v))⁻¹) := by rw [hruv]; group
          _ = r * ruv := by rw [huv2, one_mul, inv_one, mul_one, c2]
      have hprod : r ^ 2 = (r * ru) * (ru⁻¹ * ruv⁻¹) * (r * ruv) := by
        have hc : ruv⁻¹ * r = r * ruv⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← c2, mul_inv_cancel_right]
        calc r ^ 2 = r * (r * ruv⁻¹) * ruv := by rw [sq]; group
          _ = r * (ruv⁻¹ * r) * ruv := by rw [hc]
          _ = (r * ru) * (ru⁻¹ * ruv⁻¹) * (r * ruv) := by group
      rw [hprod]
      exact mul_mem (mul_mem h1 h2) h3
    · exact Or.inl hN
  refine ⟨hfirst, ?_⟩
  have hZne : R ⊓ centralizer (R : Set G) ≠ ⊥ := by
    have h := inf_center_ne_bot' hR le_rfl le_normalizer hRne
    intro h'
    apply h
    rw [h', inf_bot_eq]
  rcases hfirst with hN | hΦΓ
  ·
    set U₀ := U ⊓ normalizer (R : Set G) with hU₀
    have hU₀2 : IsPGroup 2 U₀ :=
      (IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)).to_le inf_le_left
    have hP : IsPGroup 2 ↥(U₀ ⊔ R) := hU₀2.to_sup_of_normal_right' hR inf_le_right
    have hZP : R ⊓ centralizer (R : Set G) ≤ U₀ ⊔ R := inf_le_left.trans le_sup_right
    have hPN : U₀ ⊔ R ≤ normalizer ((R ⊓ centralizer (R : Set G) : Subgroup G) : Set G) :=
      sup_le (fun g hg => mem_normalizer_center (mem_inf.1 hg).2)
        (fun g hg => mem_normalizer_center (le_normalizer hg))
    have h := inf_center_ne_bot' hP hZP hPN hZne
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    obtain ⟨hzZ, hzP⟩ := mem_inf.1 hz
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
    have hzu : (z : G) * u₀ = u₀ * z :=
      (mem_centralizer_iff.1 (mem_inf.1 hzP).2 u₀ (mem_sup_left u₀.2)).symm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨z, mem_inf.2 ⟨mem_gammaOneOn_of_commute_of_mem
      (mem_inf.1 u₀.2).1 (fun h => hu₀1 (Subtype.ext h)) (hRA (mem_inf.1 hzZ).1) hzu, hzZ⟩⟩,
      fun h => hz1 ?_⟩
    have h' : z = 1 := congrArg Subtype.val h
    exact Subtype.ext h'
  ·
    have hΦne : (frattini R).map R.subtype ≠ ⊥ := by
      intro h
      apply hΦ
      rwa [Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective] at h
    have hΦR : (frattini R).map R.subtype ≤ R := map_subtype_le _
    have hRΦ : R ≤ normalizer (((frattini R).map R.subtype : Subgroup G) : Set G) := by
      intro r hr
      rw [mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨r, hr⟩ * y * ⟨r, hr⟩⁻¹, (inferInstance : (frattini R).Normal).conj_mem y hy _, ?_⟩
        simp
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hx
        have hxR : x ∈ R := by
          have h1 : r * x * r⁻¹ ∈ R := hyx ▸ y.2
          have : x = r⁻¹ * (r * x * r⁻¹) * r := by group
          rw [this]
          exact mul_mem (mul_mem (inv_mem hr) h1) hr
        refine ⟨⟨x, hxR⟩, ?_, rfl⟩
        have h2 := (inferInstance : (frattini R).Normal).conj_mem y hy ⟨r, hr⟩⁻¹
        have e : (⟨r, hr⟩⁻¹ * y * (⟨r, hr⟩⁻¹)⁻¹ : R) = ⟨x, hxR⟩ := by
          apply Subtype.ext
          simp only [coe_mul, coe_inv, inv_inv]
          rw [show (y : G) = r * x * r⁻¹ from hyx]
          group
        rwa [e] at h2
    have h := inf_center_ne_bot' hR hΦR hRΦ hΦne
    intro h'
    apply h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxΦ, hxZ⟩ := mem_inf.1 hx
    have : x ∈ gammaOneOn U A ⊓ (R ⊓ centralizer (R : Set G)) := mem_inf.2 ⟨hΦΓ hxΦ, hxZ⟩
    rwa [h'] at this

theorem lemma24 [Finite G] {R U : Subgroup G} (hR : IsPGroup 2 R) (hU : IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4)
    (hcomm : ∀ g : G, rightConjugate R g ≠ R → ⁅R, rightConjugate R g⁆ = ⊥)
    (hΦ : frattini R ≠ ⊥) :
    (U ⊓ normalizer (R : Set G) ≠ ⊥ ∨ (frattini R).map R.subtype ≤ gammaOneOn U ⊤) ∧
      gammaOneOn U ⊤ ⊓ (R ⊓ centralizer (R : Set G)) ≠ ⊥ :=
  lemma24In le_top le_top hR hU hU4 (fun g _ => hcomm g) hΦ

end CFSG.ComponentClassification.Asc76X
