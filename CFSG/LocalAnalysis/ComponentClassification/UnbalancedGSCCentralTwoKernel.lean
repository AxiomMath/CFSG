module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace CentralTwoActionKernel

open Subgroup
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

instance oddCore_characteristic : (oddCore G).Characteristic := by
  rw [oddCore_eq_piCore]
  infer_instance

@[expose] noncomputable def descendHom (N : Subgroup G) [N.Characteristic] :
    MulAut G →* MulAut (G ⧸ N) where
  toFun φ := QuotientGroup.congr N N φ ((Subgroup.characteristic_iff_map_eq.mp inferInstance) φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem descendHom_mk (N : Subgroup G) [N.Characteristic] (φ : MulAut G) (g : G) :
    descendHom N φ (g : G ⧸ N) = (φ g : G ⧸ N) := rfl

end General

variable {H : Type*} [Group H] (E : Subgroup H) [E.Normal]

abbrev OddQuot := ↥E ⧸ oddCore ↥E

abbrev OddQuotT := OddQuot E ⧸ center (OddQuot E)

@[expose] noncomputable def actA : H →* MulAut (OddQuot E) :=
  (descendHom (oddCore E)).comp MulAut.conjNormal

@[expose] noncomputable def betaHom : H →* MulAut (OddQuotT E) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (OddQuot E)).comp (actA E)

theorem actA_mk (h : H) (e : E) :
    actA E h (e : OddQuot E) = ((MulAut.conjNormal h e : E) : OddQuot E) := rfl

theorem betaHom_mk (h : H) (e : E) :
    betaHom E h ((e : OddQuot E) : OddQuotT E) =
      (((MulAut.conjNormal h e : E) : OddQuot E) : OddQuotT E) := rfl

abbrev oddCoreIn : Subgroup H := (oddCore E).map E.subtype

instance oddCoreIn_normal : (oddCoreIn E).Normal :=
  ConjAct.normal_of_characteristic_of_normal

omit [E.Normal] in
theorem mem_oddCoreIn {x : H} : x ∈ oddCoreIn E ↔ ∃ hx : x ∈ E, (⟨x, hx⟩ : E) ∈ oddCore E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [E.Normal] in
theorem oddCoreIn_le : oddCoreIn E ≤ E := map_subtype_le _

theorem actA_eq_one_iff (h : H) :
    actA E h = 1 ↔ ∀ e ∈ E, ⁅e, h⁆ ∈ oddCoreIn E := by
  constructor
  · intro h1 e he
    have h2 := congrArg (fun φ : MulAut (OddQuot E) => φ ((⟨e⁻¹, inv_mem he⟩ : E) : OddQuot E)) h1
    simp only [actA_mk, MulAut.one_apply] at h2
    rw [QuotientGroup.eq] at h2
    have h3 : (h * e⁻¹ * h⁻¹)⁻¹ * e⁻¹ ∈ oddCoreIn E := (mem_oddCoreIn E).mpr ⟨_, h2⟩
    have h4 := inv_mem h3
    convert h4 using 1
    simp only [commutatorElement_def]
    group
  · intro hc
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H e =>
      rw [actA_mk, MulAut.one_apply, QuotientGroup.eq]
      have h1 := hc (e⁻¹ : E) (inv_mem e.2)
      have h2 := inv_mem h1
      obtain ⟨hx, hmem⟩ := (mem_oddCoreIn E).mp h2
      convert hmem using 1
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, coe_mul, coe_inv, commutatorElement_def]
      group

theorem betaHom_eq_one_iff [Group.IsPerfect (OddQuot E)] (h : H) :
    betaHom E h = 1 ↔ actA E h = 1 := by
  constructor
  · intro h1
    apply CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
      (OddQuot E)
    rw [map_one]
    exact h1
  · intro h1
    change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom _ (actA E h) = 1
    rw [h1, map_one]

theorem oddCore_inf_eq [Finite H] : oddCore H ⊓ E = oddCoreIn E := by
  apply le_antisymm
  · rintro x ⟨hxU, hxE⟩
    have hdvd : Nat.card ((oddCore H).subgroupOf E) ∣ Nat.card (oddCore H) := by
      rw [← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    have hle : (oddCore H).subgroupOf E ≤ oddCore E :=
      CFSG.ComponentClassification.SmallLocal.le_oddCore_of_normal_odd
        (Normal.subgroupOf inferInstance E)
        (CFSG.ComponentClassification.SmallLocal.odd_card_oddCore.of_dvd_nat hdvd)
    exact (mem_oddCoreIn E).mpr ⟨hxE, hle (mem_subgroupOf.mpr hxU)⟩
  · refine le_inf ?_ (oddCoreIn_le E)
    apply CFSG.ComponentClassification.SmallLocal.le_oddCore_of_normal_odd (oddCoreIn_normal E)
    rw [card_map_of_injective E.subtype_injective]
    exact CFSG.ComponentClassification.SmallLocal.odd_card_oddCore

theorem commutator_mem_of_mem_oddCore [Finite H] {u : H} (hu : u ∈ oddCore H) (e : H)
    (he : e ∈ E) : ⁅e, u⁆ ∈ oddCoreIn E := by
  rw [← oddCore_inf_eq E]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have := (inferInstance : (oddCore H).Normal).conj_mem _ hu e
    have h2 : ⁅e, u⁆ = (e * u * e⁻¹) * u⁻¹ := by rw [commutatorElement_def]
    rw [h2]
    exact mul_mem this (inv_mem hu)
  · have := (inferInstance : E.Normal).conj_mem _ (inv_mem he) u
    have h2 : ⁅e, u⁆ = e * (u * e⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem he this

omit [E.Normal] in
theorem commutator_mem_of_mem_center {a : H} (ha : a ∈ center H) (e : H) :
    ⁅e, a⁆ ∈ oddCoreIn E := by
  have h := mem_center_iff.mp ha e
  rw [commutatorElement_def, h, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem card_sup_mul_card_inf_of_commute [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) = Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem kernel_decomposition [Finite H] {a : H} (haZ : a ∈ center H) (ha2 : orderOf a = 2)
    (K : Subgroup H) (hK : ∀ h, h ∈ K ↔ ∀ e ∈ E, ⁅e, h⁆ ∈ oddCoreIn E)
    (hP : ∃ P : Sylow 2 K, Nat.card P = 2) :
    oddCore H ≤ K ∧ zpowers a ≤ K ∧ oddCore H ⊔ zpowers a = K ∧ oddCore H ⊓ zpowers a = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUK : oddCore H ≤ K := fun u hu =>
    (hK u).mpr fun e he => commutator_mem_of_mem_oddCore E hu e he
  have haK : a ∈ K := (hK a).mpr fun e _ => commutator_mem_of_mem_center E haZ e
  have hzK : zpowers a ≤ K := (zpowers_le).mpr haK
  have hUodd := CFSG.ComponentClassification.SmallLocal.odd_card_oddCore (H := H)
  have hinf : oddCore H ⊓ zpowers a = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [Nat.card_zpowers, ha2]
    exact Nat.coprime_two_right.mpr hUodd
  refine ⟨hUK, hzK, ?_, hinf⟩
  have hKker : K = (actA E).ker := by
    ext h
    rw [hK, MonoidHom.mem_ker, actA_eq_one_iff]
  have : K.Normal := by rw [hKker]; infer_instance
  obtain ⟨P, hPcard⟩ := hP
  have hfac : (Nat.card K).factorization 2 = 1 := by
    have h := Sylow.card_eq_multiplicity P
    rw [hPcard] at h
    have h2 : (2 : ℕ) ^ 1 = 2 ^ (Nat.card K).factorization 2 := by rw [pow_one]; exact h
    exact (Nat.pow_right_injective le_rfl h2).symm
  set m := Nat.card K / 2 with hm
  have hKcard : Nat.card K = 2 * m := by
    have := Nat.ordProj_mul_ordCompl_eq_self (Nat.card K) 2
    rw [hfac, pow_one] at this
    exact this.symm
  have hmodd : Nat.Coprime 2 m := by
    have hco := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := K)).ne'
    rw [hfac, pow_one] at hco
    exact hco
  set A' := (zpowers a).subgroupOf K with hA'
  have hA'card : Nat.card A' = 2 := by
    rw [hA', ← card_map_of_injective K.subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr hzK, Nat.card_zpowers, ha2]
  have hA'index : A'.index = m := by
    have h := A'.card_mul_index
    rw [hA'card, hKcard] at h
    omega
  have hA'center : A' ≤ center K := by
    intro x hx
    rw [mem_subgroupOf] at hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    refine mem_center_iff.mpr fun y => Subtype.ext ?_
    simp only [coe_mul]
    rw [← hn]
    exact (mem_center_iff.mp (zpow_mem haZ n) y)
  obtain ⟨W, hWcard, -, -, hWmem, hWchar, -⟩ :=
    CFSG.LyonsUnitaryFour.central_hall_direct_complement A' hA'center
      (by rw [hA'card, hA'index]; exact hmodd)
  rw [hA'index] at hWcard hWmem
  set W' := W.map K.subtype with hW'
  have hW'normal : W'.Normal := ConjAct.normal_of_characteristic_of_normal
  have hW'card : Nat.card W' = m := by rw [hW', card_map_of_injective K.subtype_injective, hWcard]
  have hW'le : W' ≤ oddCore H :=
    CFSG.ComponentClassification.SmallLocal.le_oddCore_of_normal_odd hW'normal (by
      rw [hW'card]
      exact Nat.coprime_two_left.mp hmodd)
  have hleW' : oddCore H ≤ W' := by
    intro u hu
    refine ⟨⟨u, hUK hu⟩, (hWmem _).mpr ?_, rfl⟩
    apply Subtype.ext
    simp only [coe_pow, coe_one]
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h1 : orderOf u ∣ Nat.card (oddCore H) := Subgroup.orderOf_dvd_natCard (oddCore H) hu
    have h2 : orderOf u ∣ 2 * m := by
      rw [← hKcard, ← Subgroup.orderOf_mk u (hUK hu)]
      exact orderOf_dvd_natCard _
    have h3 : Nat.Coprime (orderOf u) 2 :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_right.mpr hUodd)
    exact h3.dvd_of_dvd_mul_left h2
  have hUcard : Nat.card (oddCore H) = m := by
    rw [le_antisymm hleW' hW'le, hW'card]
  have hcomm : ∀ x ∈ oddCore H, ∀ y ∈ zpowers a, x * y = y * x := fun x _ y hy =>
    (mem_center_iff.mp (zpowers_le.mpr haZ hy) x)
  have hsup := card_sup_mul_card_inf_of_commute (oddCore H) (zpowers a) hcomm
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, ha2, hUcard] at hsup
  exact eq_of_le_of_card_ge (sup_le hUK hzK) (by rw [hKcard, hsup, mul_comm])

omit [E.Normal] in
open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem center_oddQuotT_eq_bot [Group.IsPerfect (OddQuot E)] : center (OddQuotT E) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have h : centerQuotientHom (OddQuot E) (MulAut.conj x) = 1 := by
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H w =>
      change onCenterQuotient (MulAut.conj x) (QuotientGroup.mk' _ w) = QuotientGroup.mk' _ w
      rw [onCenterQuotient_apply_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have := mem_center_iff.mp hy (QuotientGroup.mk' _ w)
      change QuotientGroup.mk' _ w * QuotientGroup.mk' _ x = QuotientGroup.mk' _ x *
        QuotientGroup.mk' _ w at this
      rw [← this, mul_inv_cancel_right]
  have h1 := CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
    (OddQuot E) (h.trans (map_one _).symm)
  have hx : x ∈ center (OddQuot E) := by
    refine mem_center_iff.mpr fun g => ?_
    have h2 := congrArg (fun φ : MulAut (OddQuot E) => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * x = x * g * x⁻¹ * x := by rw [h2]
      _ = x * g := by group
  rw [mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem betaHom_of_mem (e : E) :
    betaHom E e = MulAut.conj (((e : OddQuot E) : OddQuotT E)) := by
  refine MulEquiv.ext fun z => ?_
  induction z using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H v =>
      rw [MulAut.conj_apply]
      change (((MulAut.conjNormal (e : H) v : E) : OddQuot E) : OddQuotT E) = _
      have hv : (MulAut.conjNormal (e : H) v : E) = e * v * e⁻¹ := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        rfl
      rw [hv]
      rfl

theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] (g : G) :
    MulAut.conj g = 1 ↔ g ∈ center G := by
  constructor
  · intro h
    refine mem_center_iff.mpr fun z => ?_
    have h2 := congrArg (fun φ : MulAut G => φ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc z * g = g * z * g⁻¹ * g := by rw [h2]
      _ = g * z := by group
  · intro h
    refine MulEquiv.ext fun z => ?_
    rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.mp h z, mul_inv_cancel_right]

theorem map_betaHom_eq_range :
    E.map (betaHom E) = (MulAut.conj : OddQuotT E →* MulAut (OddQuotT E)).range := by
  ext φ
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, (betaHom_of_mem E ⟨e, he⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨v, v.2, betaHom_of_mem E v⟩

theorem mk_mem_zpowers_iff {a : H} (haE : a ∈ E) (haZ : a ∈ center H) (e : E) :
    (e : OddQuot E) ∈ zpowers ((⟨a, haE⟩ : E) : OddQuot E) ↔
      (e : H) ∈ oddCoreIn E ⊔ zpowers a := by
  rw [mem_sup_of_normal_left]
  constructor
  · rintro ⟨n, hn⟩
    dsimp only at hn
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hn
    refine ⟨(e : H) * (a ^ n)⁻¹, ?_, a ^ n, zpow_mem_zpowers a n, inv_mul_cancel_right _ _⟩
    have hc : (e : H) * (a ^ n)⁻¹ = (a ^ n)⁻¹ * e :=
      mem_center_iff.mp (inv_mem (zpow_mem haZ n)) e
    rw [hc]
    refine (mem_oddCoreIn E).mpr ⟨mul_mem (inv_mem (zpow_mem haE n)) e.2, ?_⟩
    convert hn using 1
  · rintro ⟨o, ho, z, ⟨n, rfl⟩, he⟩
    refine ⟨n, ?_⟩
    obtain ⟨hoE, hoO⟩ := (mem_oddCoreIn E).mp ho
    have he' : e = ⟨o, hoE⟩ * (⟨a, haE⟩ : E) ^ n := Subtype.ext (by
      rw [coe_mul, coe_zpow]
      exact he.symm)
    change ((⟨a, haE⟩ : E) : OddQuot E) ^ n = (e : OddQuot E)
    rw [he', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hoO, one_mul,
      QuotientGroup.mk_zpow]

theorem ker_betaHom_restrict [Group.IsPerfect (OddQuot E)] {a : H} (haE : a ∈ E)
    (haZ : a ∈ center H) (hZ : center (OddQuot E) = zpowers ((⟨a, haE⟩ : E) : OddQuot E)) :
    ((betaHom E).comp E.subtype).ker = (oddCoreIn E ⊔ zpowers a).subgroupOf E := by
  ext e
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, betaHom_of_mem,
    mem_subgroupOf, conj_eq_one_iff_mem_center, center_oddQuotT_eq_bot, mem_bot,
    QuotientGroup.eq_one_iff, hZ, mk_mem_zpowers_iff E haE haZ]

theorem exists_map_mk_equiv [Finite H] :
    ∃ ι : E.map (QuotientGroup.mk' (oddCore H)) ≃* OddQuot E,
      ∀ e : E, ι ⟨QuotientGroup.mk' (oddCore H) e, mem_map_of_mem _ e.2⟩ = (e : OddQuot E) := by
  let φ : E →* H ⧸ oddCore H := (QuotientGroup.mk' (oddCore H)).comp E.subtype
  have hker : φ.ker = oddCore E := by
    ext e
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro he
      have : (e : H) ∈ oddCore H ⊓ E := ⟨he, e.2⟩
      rw [oddCore_inf_eq] at this
      exact ((mem_oddCoreIn E).mp this).2
    · intro he
      have : (e : H) ∈ oddCoreIn E := (mem_oddCoreIn E).mpr ⟨e.2, he⟩
      rw [← oddCore_inf_eq] at this
      exact this.1
  have hrange : φ.range = E.map (QuotientGroup.mk' (oddCore H)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)), fun e => ?_⟩
  simp only [MulEquiv.trans_apply]
  have h1 : (MulEquiv.subgroupCongr hrange).symm
      ⟨QuotientGroup.mk' (oddCore H) e, mem_map_of_mem _ e.2⟩ = ⟨φ e, e, rfl⟩ :=
    Subtype.ext rfl
  have h2 : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ e, e, rfl⟩ = (e : E ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1, h2, QuotientGroup.quotientMulEquivOfEq_mk]

end CentralTwoActionKernel

open Subgroup CentralTwoActionKernel
open scoped commutatorElement

theorem perfect_odd_quotient_central_two_action_kernel {H : Type*} [Group H] [Finite H]
    (E : Subgroup H) [E.Normal] {a : H} (haE : a ∈ E) (haZ : a ∈ center H)
    (ha2 : orderOf a = 2) [Group.IsPerfect (OddQuot E)]
    (hZ : center (OddQuot E) = zpowers ((⟨a, haE⟩ : E) : OddQuot E))
    (K : Subgroup H) (hK : ∀ h, h ∈ K ↔ ∀ e ∈ E, ⁅e, h⁆ ∈ oddCoreIn E)
    (hP : ∃ P : Sylow 2 K, Nat.card P = 2) :
    oddCore H ⊓ E = oddCoreIn E ∧
    (oddCore H ≤ K ∧ zpowers a ≤ K ∧ oddCore H ⊔ zpowers a = K ∧ oddCore H ⊓ zpowers a = ⊥ ∧
      ∀ x ∈ oddCore H, ∀ y ∈ zpowers a, x * y = y * x) ∧
    (∀ (h : H) (e : E), betaHom E h ((e : OddQuot E) : OddQuotT E) =
      (((MulAut.conjNormal h e : E) : OddQuot E) : OddQuotT E)) ∧
    (betaHom E).ker = K ∧
    center (OddQuotT E) = ⊥ ∧
    E.map (betaHom E) = (MulAut.conj : OddQuotT E →* MulAut (OddQuotT E)).range ∧
    ((betaHom E).comp E.subtype).ker = (oddCoreIn E ⊔ zpowers a).subgroupOf E ∧
    (∃ ι : E ⧸ ((betaHom E).comp E.subtype).ker ≃*
        (MulAut.conj : OddQuotT E →* MulAut (OddQuotT E)).range,
      ∀ e : E, (ι e : MulAut (OddQuotT E)) = betaHom E e) ∧
    (E.map (QuotientGroup.mk' (oddCore H))).Normal ∧
    (∃ ι : E.map (QuotientGroup.mk' (oddCore H)) ≃* OddQuot E,
      ∀ e : E, ι ⟨QuotientGroup.mk' (oddCore H) e, mem_map_of_mem _ e.2⟩ = (e : OddQuot E)) ∧
    (∃ βbar : H ⧸ oddCore H →* MulAut (OddQuotT E),
      (∀ h : H, βbar h = betaHom E h) ∧
      βbar.ker = zpowers (QuotientGroup.mk' (oddCore H) a) ∧
      zpowers (QuotientGroup.mk' (oddCore H) a) ≤ center (H ⧸ oddCore H) ∧
      Nat.card (zpowers (QuotientGroup.mk' (oddCore H) a)) = 2) ∧
    center (H ⧸ oddCore H) = zpowers (QuotientGroup.mk' (oddCore H) a) := by
  obtain ⟨hUK, hzK, hsup, hinf⟩ := kernel_decomposition E haZ ha2 K hK hP
  have hcomm : ∀ x ∈ oddCore H, ∀ y ∈ zpowers a, x * y = y * x := fun x _ y hy =>
    (mem_center_iff.mp (zpowers_le.mpr haZ hy) x)
  have hker : (betaHom E).ker = K := by
    ext h
    rw [MonoidHom.mem_ker, betaHom_eq_one_iff, actA_eq_one_iff, hK]
  have hmemK : ∀ h : H, h ∈ K ↔
      QuotientGroup.mk' (oddCore H) h ∈ zpowers (QuotientGroup.mk' (oddCore H) a) := by
    intro h
    rw [← hsup, mem_sup_of_normal_left]
    constructor
    · rintro ⟨u, hu, z, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      change QuotientGroup.mk' (oddCore H) a ^ n = QuotientGroup.mk' (oddCore H) (u * a ^ n)
      rw [map_mul,
        show QuotientGroup.mk' (oddCore H) u = 1 from (QuotientGroup.eq_one_iff u).mpr hu,
        one_mul, map_zpow]
    · rintro ⟨n, hn⟩
      change QuotientGroup.mk' (oddCore H) a ^ n = QuotientGroup.mk' (oddCore H) h at hn
      rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hn
      refine ⟨h * (a ^ n)⁻¹, ?_, a ^ n, zpow_mem_zpowers a n, inv_mul_cancel_right _ _⟩
      have hc : h * (a ^ n)⁻¹ = (a ^ n)⁻¹ * h := mem_center_iff.mp (inv_mem (zpow_mem haZ n)) h
      rw [hc]
      exact hn
  have hUker : (oddCore H) ≤ (betaHom E).ker := hker ▸ hUK
  have haU : QuotientGroup.mk' (oddCore H) a ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have : a ∈ (oddCore H) ⊓ zpowers a := ⟨h1, mem_zpowers a⟩
    rw [hinf, mem_bot] at this
    rw [this, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haU2 : QuotientGroup.mk' (oddCore H) a ^ 2 = 1 := by
    rw [← map_pow, ← ha2, pow_orderOf_eq_one, map_one]
  have hordU : orderOf (QuotientGroup.mk' (oddCore H) a) = 2 := orderOf_eq_prime haU2 haU
  have hzcenter : zpowers (QuotientGroup.mk' (oddCore H) a) ≤ center (H ⧸ (oddCore H)) := by
    rw [zpowers_le]
    refine mem_center_iff.mpr fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) y
    rw [← map_mul, ← map_mul, mem_center_iff.mp haZ g]
  refine ⟨oddCore_inf_eq E, ⟨hUK, hzK, hsup, hinf, hcomm⟩, betaHom_mk E, hker,
    center_oddQuotT_eq_bot E, map_betaHom_eq_range E, ker_betaHom_restrict E haE haZ hZ, ?_,
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _),
    exists_map_mk_equiv E, ?_, ?_⟩
  ·
    let φ := (betaHom E).comp E.subtype
    have hrange : φ.range = (MulAut.conj : OddQuotT E →* MulAut (OddQuotT E)).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, map_betaHom_eq_range]
    exact ⟨(QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange),
      fun e => rfl⟩
  · refine ⟨QuotientGroup.lift (oddCore H) (betaHom E) hUker,
      fun h => QuotientGroup.lift_mk _ _ _, ?_,
      hzcenter, by rw [Nat.card_zpowers, hordU]⟩
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk, ← MonoidHom.mem_ker,
      hker, hmemK]
    rfl
  · apply le_antisymm _ hzcenter
    intro x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
    rw [← hmemK, hK]
    intro e he
    rw [← oddCore_inf_eq E]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxe := mem_center_iff.mp hx (QuotientGroup.mk' (oddCore H) e)
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_def, hxe, mul_inv_cancel_right, mul_inv_cancel]
    · rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact mul_mem he ((inferInstance : E.Normal).conj_mem _ (inv_mem he) h |> fun h' => by
        simpa [mul_assoc] using h')

end CFSG.ComponentClassification.UnbalancedGS
