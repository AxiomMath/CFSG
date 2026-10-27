module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G]

theorem self_mem_centralizer_singleton (h : G) : h ∈ centralizer ({h} : Set G) :=
  mem_centralizer_iff.2 fun w hw => by rw [Set.mem_singleton_iff.1 hw]

abbrev selfZpowers (h : G) : Subgroup (centralizer ({h} : Set G)) :=
  zpowers ⟨h, self_mem_centralizer_singleton h⟩

theorem selfZpowers_le_center (h : G) :
    selfZpowers h ≤ center (centralizer ({h} : Set G)) := by
  rw [zpowers_le]
  exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 y.2 h rfl).symm

instance selfZpowers_normal (h : G) : (selfZpowers h).Normal :=
  ⟨fun n hn g => by
    rw [mem_center_iff.1 (selfZpowers_le_center h hn) g, mul_inv_cancel_right]
    exact hn⟩

theorem mem_selfZpowers_iff {h : G} (hh : orderOf h = 2) {y : centralizer ({h} : Set G)} :
    y ∈ selfZpowers h ↔ y = 1 ∨ (y : G) = h := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have ho : orderOf (⟨h, self_mem_centralizer_singleton h⟩ : centralizer ({h} : Set G)) =
        2 := by rw [Subgroup.orderOf_mk, hh]
    rw [← zpow_mod_orderOf, ho, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero]
    · right
      rw [hk, zpow_one]
  · rintro (rfl | hy)
    · exact one_mem _
    · have : y = ⟨h, self_mem_centralizer_singleton h⟩ := Subtype.ext hy
      rw [this]
      exact mem_zpowers _

theorem conj_commute_of_commute {y a b : G} (h : a * b = b * a) :
    (y * a * y⁻¹) * (y * b * y⁻¹) = (y * b * y⁻¹) * (y * a * y⁻¹) :=
  calc (y * a * y⁻¹) * (y * b * y⁻¹) = y * (a * b) * y⁻¹ := by group
    _ = y * (b * a) * y⁻¹ := by rw [h]
    _ = (y * b * y⁻¹) * (y * a * y⁻¹) := by group

theorem conj_sq_eq_of_conj_eq_mul {h x y : G} (hyh : y * h = h * y) (hh2 : h * h = 1)
    (hy : y * x * y⁻¹ = h * x) : y * y * x * (y * y)⁻¹ = x :=
  calc y * y * x * (y * y)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by group
    _ = y * (h * x) * y⁻¹ := by rw [hy]
    _ = (y * h * y⁻¹) * (y * x * y⁻¹) := by group
    _ = h * (h * x) := by rw [hy, hyh, mul_inv_cancel_right]
    _ = x := by rw [← mul_assoc, hh2, one_mul]

theorem conj_inv_mul_eq_of_conj_eq_mul {h x y₁ y₂ : G} (hyh : y₁ * h = h * y₁)
    (hh2 : h * h = 1) (hy₁ : y₁ * x * y₁⁻¹ = h * x) (hy₂ : y₂ * x * y₂⁻¹ = h * x) :
    y₁⁻¹ * y₂ * x * (y₁⁻¹ * y₂)⁻¹ = x := by
  have hh' : y₁⁻¹ * h * y₁ = h := by rw [mul_assoc, ← hyh, inv_mul_cancel_left]
  have e1 : x = h * (y₁⁻¹ * x * y₁) :=
    calc x = y₁⁻¹ * (y₁ * x * y₁⁻¹) * y₁ := by group
      _ = y₁⁻¹ * (h * x) * y₁ := by rw [hy₁]
      _ = (y₁⁻¹ * h * y₁) * (y₁⁻¹ * x * y₁) := by group
      _ = h * (y₁⁻¹ * x * y₁) := by rw [hh']
  have hx1 : y₁⁻¹ * x * y₁ = h * x :=
    calc y₁⁻¹ * x * y₁ = h * h * (y₁⁻¹ * x * y₁) := by rw [hh2, one_mul]
      _ = h * x := by rw [mul_assoc, ← e1]
  calc y₁⁻¹ * y₂ * x * (y₁⁻¹ * y₂)⁻¹ = y₁⁻¹ * (y₂ * x * y₂⁻¹) * y₁ := by group
    _ = y₁⁻¹ * (h * x) * y₁ := by rw [hy₂]
    _ = (y₁⁻¹ * h * y₁) * (y₁⁻¹ * x * y₁) := by group
    _ = h * (h * x) := by rw [hh', hx1]
    _ = x := by rw [← mul_assoc, hh2, one_mul]

theorem index_le_two_of_inv_mul_mem {A : Type*} [Group A] {B : Subgroup A}
    (h : ∀ a b : A, a ∉ B → b ∉ B → a⁻¹ * b ∈ B) : B.index ≤ 2 := by
  classical
  by_cases hB : ∀ a, a ∈ B
  · have hBt : B = ⊤ := eq_top_iff.2 fun a _ => hB a
    rw [hBt, index_top]
    norm_num
  · push Not at hB
    obtain ⟨a, ha⟩ := hB
    have hsurj : Function.Surjective
        (fun b : Bool => if b then (a : A ⧸ B) else ((1 : A) : A ⧸ B)) := by
      intro z
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
      by_cases hc : c ∈ B
      · exact ⟨false, QuotientGroup.eq.2 (by simpa using hc)⟩
      · exact ⟨true, QuotientGroup.eq.2 (h a c ha hc)⟩
    calc B.index = Nat.card (A ⧸ B) := rfl
      _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
      _ = 2 := by simp

theorem central_involution_quotient_local_normal_two_subgroup [Finite G] {h x : G}
    (hh : orderOf h = 2) (_hx : orderOf x = 2) (_hne : h ≠ x)
    (hxh : x ∈ centralizer ({h} : Set G)) {U : Subgroup G}
    (hUC : U ≤ centralizer ({h, x} : Set G))
    (hUn : (U.subgroupOf (centralizer ({h, x} : Set G))).Normal) (hU2 : IsPGroup 2 U)
    (hhU : h ∉ U)
    (hCU : IsPGroup 2 ↥(centralizer ({h, x} : Set G) ⊓ centralizer (U : Set G))) :
    let D := centralizer ({h} : Set G) ⧸ selfZpowers h
    let t : D := QuotientGroup.mk ⟨x, hxh⟩
    let H := centralizer ({t} : Set D)
    CFSG.IsCharacteristicP 2 H ∧ (∀ K : Subgroup H, ¬ CFSG.IsComponent K) ∧
      ordProj[2] (Nat.card H) ≤ ordProj[2] (Nat.card (centralizer ({h, x} : Set G))) := by
  intro D t H
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ch := centralizer ({h} : Set G) with hChdef
  set N := selfZpowers h with hNdef
  set q : Ch →* D := QuotientGroup.mk' N with hqdef
  set C := centralizer ({h, x} : Set G) with hCdef
  have hh2 : h * h = 1 := by rw [← sq, ← hh, pow_orderOf_eq_one]
  have hCCh : C ≤ Ch := centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hmemC : ∀ y : Ch, (y : G) ∈ C ↔ x * y = y * x := fun y => by
    rw [mem_centralizer_iff]
    constructor
    · intro hy
      exact hy x (Set.mem_insert_of_mem _ rfl)
    · intro hy w hw
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact mem_centralizer_iff.1 y.2 w rfl
      · rw [Set.mem_singleton_iff.1 hw]
        exact hy
  have hyh : ∀ y : Ch, (y : G) * h = h * y := fun y => (mem_centralizer_iff.1 y.2 h rfl).symm
  have hY : ∀ y : Ch, q y ∈ H → x * y = y * x ∨ (y : G) * x * (y : G)⁻¹ = h * x := by
    intro y hy
    have hN : y * ⟨x, hxh⟩ * y⁻¹ * (⟨x, hxh⟩ : Ch)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 := mem_centralizer_iff.1 hy t rfl
      change q y * t * (q y)⁻¹ * t⁻¹ = 1
      rw [← h1]
      group
    rcases (mem_selfZpowers_iff hh).1 hN with h1 | h1
    · left
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h2
      calc x * y = (y * x * (y : G)⁻¹ * x⁻¹)⁻¹ * (y * x) := by group
        _ = y * x := by rw [h2, inv_one, one_mul]
    · right
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (y : G) * x * (y : G)⁻¹ = (y * x * (y : G)⁻¹ * x⁻¹) * x := by group
        _ = h * x := by rw [h1]
  have hnotC : ∀ y : Ch, q y ∈ H → (y : G) ∉ C → (y : G) * x * (y : G)⁻¹ = h * x :=
    fun y hy hyC => (hY y hy).resolve_left fun h1 => hyC ((hmemC y).2 h1)
  set C' := C.subgroupOf Ch with hC'def
  set C0 := C'.map q with hC0def
  have hmemC' : ∀ y : Ch, y ∈ C' ↔ (y : G) ∈ C := fun y => Subgroup.mem_subgroupOf
  have hC0H : C0 ≤ H := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.1 hw]
    have h1 := (hmemC c).1 ((hmemC' c).1 hc)
    have h2 : (⟨x, hxh⟩ : Ch) * c = c * ⟨x, hxh⟩ := Subtype.ext h1
    change q ⟨x, hxh⟩ * q c = q c * q ⟨x, hxh⟩
    rw [← map_mul, h2, map_mul]
  have hsq : ∀ g ∈ H, g ^ 2 ∈ C0 := by
    intro g hg
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N g
    refine ⟨y ^ 2, (hmemC' _).2 ((hmemC _).2 ?_), map_pow _ _ _⟩
    rcases hY y hg with h1 | h1
    · rw [Subgroup.coe_pow, sq, ← mul_assoc, h1, mul_assoc, h1, mul_assoc]
    · have h2 := conj_sq_eq_of_conj_eq_mul (hyh y) hh2 h1
      rw [Subgroup.coe_pow, sq]
      calc x * ((y : G) * y) = (y : G) * y * x * ((y : G) * y)⁻¹ * ((y : G) * y) := by
            rw [h2]
        _ = (y : G) * y * x := by group
  have hcos : ∀ g₁ ∈ H, ∀ g₂ ∈ H, g₁ ∉ C0 → g₂ ∉ C0 → g₁⁻¹ * g₂ ∈ C0 := by
    intro g₁ hg₁ g₂ hg₂ hn₁ hn₂
    obtain ⟨y₁, rfl⟩ := QuotientGroup.mk'_surjective N g₁
    obtain ⟨y₂, rfl⟩ := QuotientGroup.mk'_surjective N g₂
    have hy₁ : (y₁ : G) ∉ C := fun h1 => hn₁ ⟨y₁, (hmemC' _).2 h1, rfl⟩
    have hy₂ : (y₂ : G) ∉ C := fun h1 => hn₂ ⟨y₂, (hmemC' _).2 h1, rfl⟩
    have h2 := conj_inv_mul_eq_of_conj_eq_mul (hyh y₁) hh2 (hnotC y₁ hg₁ hy₁) (hnotC y₂ hg₂ hy₂)
    refine ⟨y₁⁻¹ * y₂, (hmemC' _).2 ((hmemC _).2 ?_), by rw [map_mul, map_inv]⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * ((y₁ : G)⁻¹ * y₂) = (y₁ : G)⁻¹ * y₂ * x * ((y₁ : G)⁻¹ * y₂)⁻¹ * ((y₁ : G)⁻¹ * y₂) :=
          by rw [h2]
      _ = (y₁ : G)⁻¹ * y₂ * x := by group
  have hUCh : U ≤ Ch := hUC.trans hCCh
  have hcenU : ∀ d ∈ C0, d ∈ centralizer ((U.subgroupOf Ch).map q : Set D) →
      ∃ k : ℕ, d ^ 2 ^ k = 1 := by
    rintro _ ⟨c, hc, rfl⟩ hd
    have hcC := (hmemC' c).1 hc
    have hcU : (c : G) ∈ centralizer (U : Set G) := by
      rw [mem_centralizer_iff]
      intro u hu
      have h1 := mem_centralizer_iff.1 hd (q ⟨u, hUCh hu⟩) ⟨⟨u, hUCh hu⟩, hu, rfl⟩
      have hN : c * ⟨u, hUCh hu⟩ * c⁻¹ * (⟨u, hUCh hu⟩ : Ch)⁻¹ ∈ N := by
        rw [← QuotientGroup.eq_one_iff]
        change q c * q ⟨u, hUCh hu⟩ * (q c)⁻¹ * (q ⟨u, hUCh hu⟩)⁻¹ = 1
        rw [← h1]
        group
      have hUmem : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ U := by
        have h3 := hUn.conj_mem ⟨u, hUC hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨c, hcC⟩
        exact mul_mem (Subgroup.mem_subgroupOf.1 h3) (inv_mem hu)
      rcases (mem_selfZpowers_iff hh).1 hN with h2 | h2
      · have h4 := congrArg Subtype.val h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h4
        calc u * c = ((c : G) * u * (c : G)⁻¹ * u⁻¹)⁻¹ * (c * u) := by group
          _ = c * u := by rw [h4, inv_one, one_mul]
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
        exact absurd (h2 ▸ hUmem) hhU
    obtain ⟨k, hk⟩ := hCU ⟨c, mem_inf.2 ⟨hcC, hcU⟩⟩
    refine ⟨k, ?_⟩
    have hk' : c ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [← map_pow, hk', map_one]
  set O := (CFSG.pCore 2 C).map C.subtype with hOdef
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hO2 : IsPGroup 2 O := (CFSG.pCore_isPGroup).map _
  have hOn : (O.subgroupOf C).Normal := by
    rw [hOdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact CFSG.pCore_normal
  have hUO : U ≤ O := by
    have h1 : U.subgroupOf C ≤ CFSG.pCore 2 C :=
      le_pCore hUn (hU2.comap_of_injective C.subtype C.subtype_injective)
    intro u hu
    exact ⟨⟨u, hUC hu⟩, h1 (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  have hnormC : ∀ y : Ch, q y ∈ H → ∀ c ∈ C, (y : G) * c * (y : G)⁻¹ ∈ C := by
    intro y hy c hc
    have hcCh : c ∈ Ch := hCCh hc
    have hc' : (⟨c, hcCh⟩ : Ch) ∈ C' := (hmemC' _).2 hc
    refine (hmemC (y * ⟨c, hcCh⟩ * y⁻¹)).2 ?_
    have hxc : x * c = c * x := (hmemC ⟨c, hcCh⟩).1 hc
    have hhc : h * c = c * h := (hyh ⟨c, hcCh⟩).symm
    change x * ((y : G) * c * (y : G)⁻¹) = (y : G) * c * (y : G)⁻¹ * x
    have e1 := conj_commute_of_commute (y := (y : G)) hxc
    rcases hY y hy with h1 | h1
    · have hx' : (y : G) * x * (y : G)⁻¹ = x := by rw [← h1, mul_inv_cancel_right]
      rw [hx'] at e1
      exact e1
    · have e2 := conj_commute_of_commute (y := (y : G)) hhc
      have hyhy : (y : G) * h * (y : G)⁻¹ = h := by rw [hyh y, mul_inv_cancel_right]
      rw [h1] at e1
      rw [hyhy] at e2
      calc x * ((y : G) * c * (y : G)⁻¹) = h⁻¹ * ((h * x) * ((y : G) * c * (y : G)⁻¹)) := by
            group
        _ = h⁻¹ * (((y : G) * c * (y : G)⁻¹) * (h * x)) := by rw [e1]
        _ = h⁻¹ * ((((y : G) * c * (y : G)⁻¹) * h) * x) := by group
        _ = h⁻¹ * ((h * ((y : G) * c * (y : G)⁻¹)) * x) := by rw [e2]
        _ = (y : G) * c * (y : G)⁻¹ * x := by group
  have hnormO : ∀ y : Ch, q y ∈ H → ∀ o ∈ O, (y : G) * o * (y : G)⁻¹ ∈ O := by
    intro y hy o ho
    have hyinv : q y⁻¹ ∈ H := by rw [map_inv]; exact inv_mem hy
    set W := conjSub (y : G) O with hWdef
    have hWC : W ≤ C := by
      rintro _ ⟨o', ho', rfl⟩
      exact hnormC y hy o' (hOC ho')
    have hWn : (W.subgroupOf C).Normal := by
      refine ⟨fun w hw c => ?_⟩
      obtain ⟨o', ho', ho'w⟩ := Subgroup.mem_subgroupOf.1 hw
      rw [Subgroup.mem_subgroupOf]
      have hc' : (y : G)⁻¹ * c * (y : G) ∈ C := by
        have := hnormC y⁻¹ hyinv c c.2
        simpa using this
      have h1 := hOn.conj_mem ⟨o', hOC ho'⟩ (Subgroup.mem_subgroupOf.2 ho') ⟨_, hc'⟩
      rw [Subgroup.mem_subgroupOf] at h1
      refine ⟨_, h1, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at ho'w ⊢
      rw [← ho'w]
      group
    have hW2 : IsPGroup 2 W := hO2.map _
    have hWle : W.subgroupOf C ≤ CFSG.pCore 2 C :=
      le_pCore hWn (hW2.comap_of_injective C.subtype C.subtype_injective)
    have hyo : (y : G) * o * (y : G)⁻¹ ∈ W := ⟨o, ho, rfl⟩
    exact ⟨⟨_, hWC hyo⟩, hWle (Subgroup.mem_subgroupOf.2 hyo), rfl⟩
  set R := (O.subgroupOf Ch).map q with hRdef
  have hRH : R ≤ H := by
    have : O.subgroupOf Ch ≤ C' := fun o ho => (hmemC' o).2 (hOC (Subgroup.mem_subgroupOf.1 ho))
    exact (map_mono this).trans hC0H
  have hR2 : IsPGroup 2 R :=
    ((hO2.comap_of_injective Ch.subtype Ch.subtype_injective).map q)
  have hRn : (R.subgroupOf H).Normal := by
    refine ⟨fun r hr g => ?_⟩
    obtain ⟨o, ho, hor⟩ := Subgroup.mem_subgroupOf.1 hr
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (g : D)
    have hyH : q y ∈ H := hy ▸ g.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨y * o * y⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact hnormO y hyH o (Subgroup.mem_subgroupOf.1 ho)
    · rw [map_mul, map_mul, map_inv, hy, hor]
      rfl
  have hUR : (U.subgroupOf Ch).map q ≤ R :=
    map_mono fun u hu => Subgroup.mem_subgroupOf.2 (hUO (Subgroup.mem_subgroupOf.1 hu))
  set CR := centralizer ((R.subgroupOf H : Subgroup H) : Set H) with hCRdef
  have hCR2 : IsPGroup 2 CR := by
    intro g
    have hgH : ((g : H) : D) ∈ H := (g : H).2
    have hsq' := hsq _ hgH
    have hgc : ((g : H) : D) ^ 2 ∈ centralizer ((U.subgroupOf Ch).map q : Set D) := by
      refine pow_mem ?_ 2
      rw [mem_centralizer_iff]
      intro d hd
      have hdR := hUR hd
      have hdH := hRH hdR
      have := mem_centralizer_iff.1 g.2 ⟨d, hdH⟩ (Subgroup.mem_subgroupOf.2 hdR)
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hcenU _ hsq' hgc
    refine ⟨k + 1, Subtype.ext (Subtype.ext ?_)⟩
    rw [pow_succ', pow_mul]
    simpa using hk
  have hRP : R.subgroupOf H ≤ CFSG.pCore 2 H :=
    le_pCore hRn (hR2.comap_of_injective H.subtype H.subtype_injective)
  have hCRn : CR.Normal := by
    rw [hCRdef]
    infer_instance
  have hCRP : CR ≤ CFSG.pCore 2 H := le_pCore hCRn hCR2
  have hchar : CFSG.IsCharacteristicP 2 H :=
    (centralizer_le hRP).trans hCRP
  refine ⟨hchar, fun K hK => ?_, ?_⟩
  ·
    have hsolv : Group.IsSolvable (CFSG.pCore 2 H) := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := H)).isNilpotent
      infer_instance
    rcases component_normal_subgroup hK (CFSG.pCore_normal (p := 2) (G := H)) with h1 | h1
    · exact not_le_of_isComponent_of_isSolvable hK hsolv h1
    · exact not_le_of_isComponent_of_isSolvable hK hsolv
        ((commutator_eq_bot_iff_le_centralizer.1 h1).trans hchar)
  ·
    have hNC' : N ≤ C' := by
      rw [zpowers_le]
      refine (hmemC' _).2 ((hmemC _).2 ?_)
      exact (mem_centralizer_iff.1 hxh h rfl).symm
    have hNcard : Nat.card N = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hh]
    have hC0card : Nat.card C0 * 2 = Nat.card C := by
      set φ := q.comp C'.subtype with hφ
      have hrange : φ.range = C0 := by rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
      have hker : φ.ker.map C'.subtype = N := by
        ext y
        constructor
        · rintro ⟨c, hc, rfl⟩
          have hc' : q (c : Ch) = 1 := MonoidHom.mem_ker.1 hc
          rw [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
          exact hc'
        · intro hy
          refine ⟨⟨y, hNC' hy⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
          change q y = 1
          rw [hqdef, QuotientGroup.mk'_apply]
          exact (QuotientGroup.eq_one_iff _).2 hy
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange,
        ← Subgroup.card_map_of_injective C'.subtype_injective, hker, hNcard] at h1
      rw [← h1, hC'def]
      exact Nat.card_congr (subgroupOfEquivOfLe hCCh).toEquiv
    have hidx : (C0.subgroupOf H).index ≤ 2 := by
      refine index_le_two_of_inv_mul_mem fun a b ha hb => ?_
      rw [Subgroup.mem_subgroupOf] at ha hb ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hcos _ a.2 _ b.2 ha hb
    have hidx0 : (C0.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hHcard : Nat.card C0 * (C0.subgroupOf H).index = Nat.card H := by
      rw [← Subgroup.card_mul_index (C0.subgroupOf H)]
      congr 1
      exact (Nat.card_congr (subgroupOfEquivOfLe hC0H).toEquiv).symm
    have hidx1 : 1 ≤ (C0.subgroupOf H).index := Nat.pos_of_ne_zero hidx0
    have hdvd : Nat.card H ∣ Nat.card C := by
      rw [← hHcard, ← hC0card]
      interval_cases (C0.subgroupOf H).index
      · exact ⟨2, by ring⟩
      · exact dvd_rfl
    have hCpos : Nat.card C ≠ 0 := Nat.card_pos.ne'
    exact Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd hCpos hdvd 2)

end CFSG.LocalAnalysis.ComponentInitial
