module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KFour
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec5KSeven
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PKProper
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs SL44

section OddCore

variable {X : Type} [Group X]

theorem pow_odd_of_mul_self {n : X} (hn : n * n = 1) {k : ℕ} (hk : Odd k) : n ^ k = n := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, sq, hn, one_pow, one_mul]

theorem oddCore_quotient_eq_bot (N : Subgroup X) [N.Normal] (hN : Nat.card N = 2)
    (hcen : ∀ n ∈ N, ∀ x : X, n * x = x * n) (hcore : standardComponentOddCore X = ⊥) :
    standardComponentOddCore (X ⧸ N) = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun M hM => ?_)
  obtain ⟨hMn, hModd⟩ := hM
  set π := QuotientGroup.mk' N with hπ
  set Q : Subgroup X := M.comap π with hQ
  have hQn : Q.Normal := Subgroup.Normal.comap hMn π
  have hNQ : N ≤ Q := fun n hn => by
    change π n ∈ M
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn]
    exact one_mem M
  set N' : Subgroup Q := N.subgroupOf Q with hN'def
  have hN'n : N'.Normal := Subgroup.Normal.subgroupOf inferInstance Q
  have hN' : Nat.card N' = 2 := by
    rw [hN'def, Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv, hN]
  have hcardQ : Nat.card Q = 2 * Nat.card M := by
    let f : Q →* M := (π.comp Q.subtype).codRestrict M fun q => q.2
    have hf : Function.Surjective f := by
      rintro ⟨m, hm⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N m
      exact ⟨⟨x, hm⟩, rfl⟩
    have hker : f.ker = N' := by
      ext q
      rw [MonoidHom.mem_ker, hN'def, mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h1)
    rw [← Subgroup.card_ker_mul_card_range f, hker, hN', MonoidHom.range_eq_top.2 hf, card_top]
  have hidx : N'.index = Nat.card M := by
    have h1 := N'.card_mul_index
    rw [hN', hcardQ] at h1
    omega
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card N') N'.index by
      rw [hN', hidx]
      exact Nat.coprime_two_left.2 hModd)
  have hcardC : Nat.card C = Nat.card M := by
    have h1 := hC.card_mul_card
    rw [hN', hcardQ] at h1
    omega
  set C' : Subgroup X := C.map Q.subtype with hC'
  have hcardC' : Nat.card C' = Nat.card M := by
    rw [hC', card_map_of_injective Q.subtype_injective, hcardC]
  have hC'n : C'.Normal := by
    refine ⟨fun c hc x => ?_⟩
    have hcQ : c ∈ Q := map_subtype_le C hc
    have hqQ : x * c * x⁻¹ ∈ Q := hQn.conj_mem c hcQ x
    obtain ⟨⟨⟨n, hn⟩, ⟨c₁, hc₁⟩⟩, hq, -⟩ := hC.existsUnique ⟨x * c * x⁻¹, hqQ⟩
    have hq' : (n : X) * (c₁ : X) = x * c * x⁻¹ := congrArg Subtype.val hq
    have hnN : (n : X) ∈ N := hn
    have hoc : Odd (orderOf c) := by
      have h1 : orderOf (⟨c, hc⟩ : C') ∣ Nat.card C' := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hcardC'] at h1
      exact Odd.of_dvd_nat hModd h1
    have hoq : Odd (orderOf (x * c * x⁻¹)) := by
      rw [show x * c * x⁻¹ = MulAut.conj x c from rfl, MulEquiv.orderOf_eq]
      exact hoc
    have hoc₁ : Odd (orderOf (c₁ : X)) := by
      set c₁' : C' := ⟨(c₁ : X), ⟨c₁, hc₁, rfl⟩⟩
      have h1 : orderOf c₁' ∣ Nat.card C' := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe, hcardC'] at h1
      exact Odd.of_dvd_nat hModd h1
    have hnn : (n : X) * n = 1 := by
      have h1 := pow_card_eq_one' (G := N) (x := ⟨n, hnN⟩)
      rw [hN, sq] at h1
      exact congrArg Subtype.val h1
    have hn1 : (n : X) = 1 := by
      have hcomm : Commute (n : X) (c₁ : X) := hcen _ hnN _
      have h1 : (x * c * x⁻¹) ^ orderOf (c₁ : X) = n := by
        rw [← hq', hcomm.mul_pow, pow_orderOf_eq_one, mul_one, pow_odd_of_mul_self hnn hoc₁]
      have h2 : ((x * c * x⁻¹) ^ orderOf (c₁ : X)) ^ orderOf (x * c * x⁻¹) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
      rw [h1, pow_odd_of_mul_self hnn hoq] at h2
      exact h2
    rw [← hq', hn1, one_mul]
    exact ⟨c₁, hc₁, rfl⟩
  have hC'le : C' ≤ standardComponentOddCore X := le_sSup ⟨hC'n, by rw [hcardC']; exact hModd⟩
  rw [hcore, le_bot_iff] at hC'le
  have h1 : Nat.card M = 1 := by rw [← hcardC', hC'le, card_bot]
  exact (Subgroup.card_eq_one.1 h1).le

end OddCore

@[expose] def GomiLemma1PInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Assembly.KProper CFSG.Blueprint.Catalog X →
    ∀ (t : X) (Y : Subgroup X),
    standardComponentOddCore X = ⊥ → orderOf t = 2 → CFSG.Blueprint.LieModel Y .PSp 2 2 2 →
    t ∈ normalizer (Y : Set X) →
    (¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹) →
    centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t →
    CFSG.Blueprint.LieModel (genFittingLayer X) .PSp 2 2 2 ∧
      centralizer (genFittingLayer X : Set X) = standardComponentOddCore X

section Quotient

variable {G : Type} [Group G]

theorem card_zpowersC {a : G} (ha : orderOf a = 2) : Nat.card (zpowersC a) = 2 := by
  rw [zpowersC, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2
    (mem_centralizer_singleton_iff.2 rfl))).toEquiv, Nat.card_zpowers, ha]

theorem mk_eq_one_iff {a : G} (x : centralizer ({a} : Set G)) :
    (QuotientGroup.mk' (zpowersC a) x = 1) ↔ (x : G) ∈ zpowers a := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

theorem mk_a {a : G} :
    QuotientGroup.mk' (zpowersC a) ⟨a, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
  (mk_eq_one_iff _).2 (mem_zpowers a)

end Quotient

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem exists_decomp (h : d.Hyp) {a : G} (haH : a ∈ d.H) (ha1 : a * a = 1)
    (haf : h.act ⟨a, haH⟩ = fld) {x : G} (hxH : x ∈ d.H) (hxa : x * a = a * x) :
    ∃ l ∈ d.L, l * a = a * l ∧ ∃ c ∈ zpowers d.t, x = l * c ∨ x = l * c * a := by
  have hca : ∀ c ∈ zpowers d.t, c * a = a * c := fun c hc => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact ((Commute.zpow_left (t_comm_of_mem_H haH).symm k)).eq
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha1
  by_cases hσ : h.fieldFactor ⟨x, hxH⟩ = 1
  · obtain ⟨l, hl, c, hc, hx⟩ := (h.fieldFactor_eq_one_iff _).1 hσ
    rw [h.centralizer_inf_H_eq] at hc
    have hx' : x = l * c := hx
    refine ⟨l, hl, ?_, c, hc, Or.inl hx'⟩
    have hl' : l = x * c⁻¹ := by rw [hx']; group
    rw [hl']
    exact (Commute.mul_left (hxa : Commute x a) (Commute.inv_left (hca c hc : Commute c a))).eq
  · have hfa : h.fieldFactor ⟨a, haH⟩ = barEquiv := by
      change UnitaryFiveTwo.fieldFactor (h.act ⟨a, haH⟩) = _
      rw [haf, fieldFactor_fld]
    have hfx : h.fieldFactor ⟨x, hxH⟩ = barEquiv :=
      (ringEquiv_eq_one_or_eq_barEquiv _).resolve_left hσ
    have hxaH : x * a⁻¹ ∈ d.H := mul_mem hxH (inv_mem haH)
    have hσ' : h.fieldFactor ⟨x * a⁻¹, hxaH⟩ = 1 := by
      have e : (⟨x * a⁻¹, hxaH⟩ : d.H) = ⟨x, hxH⟩ * (⟨a, haH⟩ : d.H)⁻¹ := rfl
      rw [e, map_mul, map_inv, hfx, hfa, mul_inv_cancel]
    obtain ⟨l, hl, c, hc, hx⟩ := (h.fieldFactor_eq_one_iff _).1 hσ'
    rw [h.centralizer_inf_H_eq] at hc
    have hx' : x * a⁻¹ = l * c := hx
    have hx'' : x = l * c * a := by rw [← hx', inv_mul_cancel_right]
    refine ⟨l, hl, ?_, c, hc, Or.inr hx''⟩
    have hxa' : x * a = l * c := by rw [hx'', mul_assoc, ha1, mul_one]
    have hl' : l = x * a * c⁻¹ := by rw [hxa']; group
    rw [hl']
    exact (Commute.mul_left (Commute.mul_left (hxa : Commute x a) (Commute.refl a))
      (Commute.inv_left (hca c hc : Commute c a))).eq

theorem mem_pull_CfldSub (h : d.Hyp) {a : G} (haH : a ∈ d.H) (haf : h.act ⟨a, haH⟩ = fld)
    {l : G} (hl : l ∈ d.L) (hla : l * a = a * l) : l ∈ d.pull CfldSub := by
  rw [← d.range_ι] at hl
  obtain ⟨s, rfl⟩ := hl
  refine ⟨s, mem_CfldSub.2 (d.ι_injective ?_), rfl⟩
  have e := h.ι_act_apply ⟨a, haH⟩ s
  rw [haf] at e
  rw [e]
  calc a * d.ι s * a⁻¹ = (a * d.ι s) * a⁻¹ := rfl
    _ = (d.ι s * a) * a⁻¹ := by rw [hla]
    _ = d.ι s := by group

theorem gomiOnePConclusion_of_input (h1P : GomiLemma1PInput) (h : d.Hyp) (hK : d.KLinear)
    {a : G} (haH : a ∈ d.H) (ha1 : a * a = 1) (haf : h.act ⟨a, haH⟩ = fld)
    (hag : IsGraphOn d.K a) (hta : IsFieldOn d.K (d.t * a)) : GomiOnePConclusion a := by
  classical
  obtain ⟨φ, hφ⟩ := hK.graphField
  obtain ⟨H, C, hC, hHC⟩ := h.exists_symplectic hK φ haH ha1 haf hag
  have hNa := h.mem_normalizer_K_of_act_fld haH haf
  obtain ⟨A, hA⟩ := exists_actsOn_graph φ hNa hag
  have haK := a_not_mem_K φ hA
  have hfld1 : fld ≠ 1 := fun e => by
    have h1 := fieldFactor_fld
    rw [e, map_one] at h1
    exact barEquiv_ne_one h1.symm
  have ha2 : orderOf a = 2 := by
    refine orderOf_eq_prime (by rw [sq, ha1]) fun h1 => hfld1 ?_
    rw [← haf, show (⟨a, haH⟩ : d.H) = 1 from Subtype.ext h1, map_one]
  have hta' : d.t * a = a * d.t := (t_comm_of_mem_H haH).symm
  set X := centralizer ({a} : Set G) with hX
  set π := QuotientGroup.mk' (zpowersC a) with hπ
  have htX : d.t ∈ X := mem_centralizer_singleton_iff.2 hta'
  set tX : X := ⟨d.t, htX⟩ with htXdef
  set tb : CBar a := π tX with htb
  set CK : Subgroup G := d.K ⊓ centralizer ({a} : Set G) with hCK
  have hCKX : CK ≤ X := inf_le_right
  set Y : Subgroup (CBar a) := (CK.subgroupOf X).map π with hY
  have hKa : ∀ y ∈ d.K, y ∈ zpowers a → y = 1 := fun y hyK hya => by
    rcases CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha2 hya
      with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyK) haK
  have hO : standardComponentOddCore (CBar a) = ⊥ :=
    oddCore_quotient_eq_bot (zpowersC a) (card_zpowersC ha2) (fun n hn x => zpowersC_comm hn x)
      (h.core a ha2)
  have htt : tX * tX = 1 := Subtype.ext h.t_mul_t
  have ht2 : orderOf tb = 2 := by
    refine orderOf_eq_prime (by rw [htb, ← map_pow, sq, htt, map_one]) fun h1 => ?_
    rw [htb, mk_eq_one_iff] at h1
    rcases CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha2 h1
      with h2 | h2
    · exact h.t_ne_one h2
    · apply hfld1
      rw [← haf, ← h.act_t]
      congr 1
      exact Subtype.ext h2.symm
  let f : CK →* CBar a := π.comp (inclusion hCKX)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : ((inclusion hCKX y : X) : G) ∈ zpowers a := (mk_eq_one_iff _).1 hy
    exact Subtype.ext (hKa _ y.2.1 h1)
  have hfrange : f.range = Y := by
    rw [MonoidHom.range_comp, hY]
    congr 1
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_range]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have eY : CK ≃* Y := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hfrange)
  have hYm : CFSG.Blueprint.LieModel Y .PSp 2 2 2 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eY (lieModel_CK φ hC hHC)
  have htCK : ∀ z ∈ CK, d.t * z * d.t⁻¹ ∈ CK := fun z hz => by
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 h.t_mem_normalizer_K z).1 hz.1,
      mem_centralizer_singleton_iff.2 ?_⟩
    have hza : z * a = a * z := mem_centralizer_singleton_iff.1 hz.2
    calc d.t * z * d.t⁻¹ * a = d.t * (z * a) * d.t⁻¹ := by
          rw [mul_assoc (d.t * z), show d.t⁻¹ * a = a * d.t⁻¹ from
            (Commute.inv_left (hta' : Commute d.t a)).eq]
          group
      _ = d.t * (a * z) * d.t⁻¹ := by rw [hza]
      _ = a * (d.t * z * d.t⁻¹) := by rw [← mul_assoc, hta']; group
  have hconjY : ∀ yb ∈ Y, tb * yb * tb⁻¹ ∈ Y := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : (z : G) ∈ CK := hz
    refine ⟨tX * z * tX⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact htCK _ hz'
  have htt' : tb * tb = 1 := by rw [htb, ← map_mul, htt, map_one]
  have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htt'
  have htN : tb ∈ normalizer (Y : Set (CBar a)) := by
    rw [mem_normalizer_iff]
    intro yb
    refine ⟨hconjY yb, fun hy => ?_⟩
    have h1 := hconjY _ hy
    have e : tb * (tb * yb * tb⁻¹) * tb⁻¹ = yb := by
      rw [htinv]
      calc tb * (tb * yb * tb) * tb = (tb * tb) * yb * (tb * tb) := by group
        _ = yb := by rw [htt', one_mul, mul_one]
    rwa [e] at h1
  have hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, tb * z * tb⁻¹ = y * z * y⁻¹ := by
    rintro ⟨_, ⟨y, hy, rfl⟩, hall⟩
    have hy' : (y : G) ∈ CK := hy
    refine not_inner_on_CK hφ hC hHC ⟨y, hy', fun z hz => ?_⟩
    have hzX : z ∈ X := hCKX hz
    have h1 := hall (π ⟨z, hzX⟩) ⟨⟨z, hzX⟩, (hz : ((⟨z, hzX⟩ : X) : G) ∈ CK), rfl⟩
    rw [htb, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : (y * z * y⁻¹)⁻¹ * (d.t * z * d.t⁻¹) ∈ zpowers a := by
      have h3 : ((tX * ⟨z, hzX⟩ * tX⁻¹)⁻¹ * (y * ⟨z, hzX⟩ * y⁻¹) : X) ∈ zpowersC a := h1
      have h4 : ((((tX * ⟨z, hzX⟩ * tX⁻¹)⁻¹ * (y * ⟨z, hzX⟩ * y⁻¹) : X)) : G) ∈ zpowers a := h3
      have h5 := inv_mem h4
      simpa [mul_assoc] using h5
    have h6 := hKa _ (mul_mem (inv_mem ((mem_normalizer_iff.1 (le_normalizer
      (show (y : G) ∈ d.K from hy'.1)) z).1 hz.1))
      ((mem_normalizer_iff.1 h.t_mem_normalizer_K z).1 hz.1)) h2
    rw [inv_mul_eq_one] at h6
    exact h6.symm
  have hcent : centralizer ({tb} : Set (CBar a)) =
      (Y ⊓ centralizer ({tb} : Set (CBar a))) ⊔ zpowers tb := by
    refine le_antisymm ?_ (sup_le inf_le_right (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)))
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zpowersC a) xb
    have hxt : π x * tb = tb * π x := mem_centralizer_singleton_iff.1 hxb
    rw [htb, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hxt
    have hxt' : ((x : G) * d.t)⁻¹ * (d.t * x) ∈ zpowers a := hxt
    rcases CFSG.LocalAnalysis.SteinbergBK.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha2 hxt'
      with h1 | h1
    ·
      have hxtc : (x : G) * d.t = d.t * x := by
        rw [inv_mul_eq_one] at h1
        exact h1
      have hxH : (x : G) ∈ d.H := mem_centralizer_singleton_iff.2 hxtc
      obtain ⟨l, hl, hla, c, hc, hx⟩ := h.exists_decomp haH ha1 haf hxH
        (mem_centralizer_singleton_iff.1 x.2)
      have hlK₃ : l ∈ d.K₃ := pull_CfldSub_le_K₃ hK (h.mem_pull_CfldSub haH haf hl hla)
      rw [← hK.centralizer_eq] at hlK₃
      have hlX : l ∈ X := mem_centralizer_singleton_iff.2 hla
      have hcX : c ∈ X := zpowers_le.2 htX hc
      have hlY : π ⟨l, hlX⟩ ∈ Y ⊓ centralizer ({tb} : Set (CBar a)) := by
        refine mem_inf.2 ⟨⟨⟨l, hlX⟩, (⟨hlK₃.1, hlX⟩ : l ∈ CK), rfl⟩,
          mem_centralizer_singleton_iff.2 ?_⟩
        rw [htb, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.1 hlK₃.2)
      have hcY : π ⟨c, hcX⟩ ∈ zpowers tb := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc
        refine mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [htb, ← map_zpow]
        congr 1
        exact Subtype.ext (by simpa using hk)
      rcases hx with hx | hx
      · have e : x = ⟨l, hlX⟩ * ⟨c, hcX⟩ := Subtype.ext hx
        rw [e, map_mul]
        exact mul_mem (mem_sup_left hlY) (mem_sup_right hcY)
      · have e : x = ⟨l, hlX⟩ * ⟨c, hcX⟩ * ⟨a, mem_centralizer_singleton_iff.2 rfl⟩ :=
          Subtype.ext hx
        rw [e, map_mul, map_mul, mk_a, mul_one]
        exact mul_mem (mem_sup_left hlY) (mem_sup_right hcY)
    ·
      exfalso
      refine h.not_conj_t_eq_mul hK haH ha1 haf hta x ?_
      calc (x : G)⁻¹ * d.t * x = d.t * (((x : G) * d.t)⁻¹ * (d.t * x)) := by
            rw [mul_inv_rev, h.t_inv]
            calc (x : G)⁻¹ * d.t * x = (d.t * d.t) * ((x : G)⁻¹ * d.t * x) := by
                  rw [h.t_mul_t, one_mul]
              _ = d.t * (d.t * (x : G)⁻¹ * (d.t * x)) := by group
        _ = d.t * a := by rw [h1]
  exact h1P (CBar a) (kProper_catalog_CBar h.setting.setting.kProper a) tb Y hO ht2 hYm htN hout
    hcent

end Data.Hyp

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem false_of_gomiLemma1P
    (hPSp2 : ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel X .PSp 2 2 f)
    (h1P : GomiLemma1PInput) (h : d.Hyp) (hK : d.KLinear) (hH : ¬ d.H ≤ d.L ⊔ zpowers d.t) :
    False :=
  h.false_of_gomiOneP hPSp2 hK hH fun _ haH ha1 haf hag hta =>
    h.gomiOnePConclusion_of_input h1P hK haH ha1 haf hag hta

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
