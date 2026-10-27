module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdClaimGSL
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Layer
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Basic
public import CFSG.GH74.GLS.Stage2.Local.P34OneG

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.ClaimG

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20
  CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_S1_iff bar_S1_le_S)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (em_le_LC)
open CFSG.GH74.GLS.Stage1.Thm6.Prod (LC_normal)

section GLevel

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_zpowers_of_odd_mul {s k a : G} (hsk : s = k * a) (hka : a * k = k * a)
    (hodd : Odd (orderOf a)) {e : ℕ} (hs : s ^ (2 ^ e) = 1) : s ∈ zpowers k := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [pow_zero, pow_one] at hs
    rw [hs]; exact one_mem _
  have hcop : Nat.Coprime (orderOf a) (2 ^ e) := (Nat.coprime_two_right.2 hodd).pow_right e
  have h1 : 1 < 2 ^ e := Nat.one_lt_two_pow he.ne'
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  have hN : orderOf a * j = 1 + 2 ^ e * (orderOf a * j / 2 ^ e) := by
    have := Nat.div_add_mod (orderOf a * j) (2 ^ e)
    omega
  have hsN : s ^ (orderOf a * j) = s := by
    rw [hN, pow_add, pow_one, pow_mul, hs, one_pow, mul_one]
  have hcomm : Commute k a := hka.symm
  have haN : a ^ (orderOf a * j) = 1 := by rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have : s = k ^ (orderOf a * j) := by
    calc s = s ^ (orderOf a * j) := hsN.symm
      _ = (k * a) ^ (orderOf a * j) := by rw [hsk]
      _ = k ^ (orderOf a * j) * a ^ (orderOf a * j) := hcomm.mul_pow _
      _ = k ^ (orderOf a * j) := by rw [haN, mul_one]
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _

theorem odd_orderOf_oddCore {a : G} (ha : a ∈ OddCore z) : Odd (orderOf a) := by
  obtain ⟨a', ha', rfl⟩ := ha
  show Odd (orderOf (a' : G))
  rw [Subgroup.orderOf_coe]
  exact P34.odd_orderOf_of_mem_pPrimeCore ha'

structure LDat (z : G) (K₁ K₂ : Subgroup G) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  le₁ : K₁ ≤ Cen z
  le₂ : K₂ ≤ Cen z
  bar₁ : barOf z K₁ = L₁
  bar₂ : barOf z K₂ = L₂
  layer : Em (Cen z) = K₁ ⊔ K₂
  oddcomm : ∀ a ∈ OddCore z, ∀ l ∈ Em (Cen z), a * l = l * a

omit [Finite G] in
theorem LDat.symm {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)} (h : LDat z K₁ K₂ L₁ L₂) :
    LDat z K₂ K₁ L₂ L₁ :=
  ⟨h.le₂, h.le₁, h.bar₂, h.bar₁, by rw [h.layer, sup_comm], h.oddcomm⟩

theorem LDat.of_compData {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (h : CompData z K₁ K₂ L₁ L₂) : LDat z K₁ K₂ L₁ L₂ :=
  ⟨h.le₁, h.le₂, h.bar₁, h.bar₂, h.layer, h.oddcomm⟩

structure PDat (z : G) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  odd : Odd q
  sl₁ : HasSL2Model ↥L₁ (fun r => r = q)
  sl₂ : HasSL2Model ↥L₂ (fun r => r = q)
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  card : Nat.card ↥(L₁ ⊓ L₂) = 2
  sup : L₁ ⊔ L₂ = LBar z

omit [Finite G] in
theorem PDat.symm {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} (h : PDat z q L₁ L₂) : PDat z q L₂ L₁ :=
  ⟨h.odd, h.sl₂, h.sl₁, fun a ha b hb => (h.comm b hb a ha).symm, by rw [inf_comm]; exact h.card,
    by rw [sup_comm]; exact h.sup⟩

theorem PDat.of_stage1Pair {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) : PDat z q L₁ L₂ :=
  ⟨hP.odd, hP.sl₁, hP.sl₂, hP.prod.2.1, hP.prod.2.2, hP.prod.1⟩

omit [Finite G] in
theorem barOf_sup_eq {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)} (h : LDat z K₁ K₂ L₁ L₂) :
    barOf z (K₁ ⊔ K₂) = L₁ ⊔ L₂ := by
  unfold barOf
  rw [Subgroup.subgroupOf_sup h.le₁ h.le₂, Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) h.bar₁ h.bar₂

theorem mem_layer_of_bar_mem {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) {K₁ K₂ : Subgroup G}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hL : LDat z K₁ K₂ L₁ L₂) {s : G} (hsS : s ∈ S)
    (hsC : s ∈ Cen z) (hs : toBar z ⟨s, hsC⟩ ∈ L₁ ⊔ L₂) : s ∈ K₁ ⊔ K₂ := by
  rw [← barOf_sup_eq hL] at hs
  obtain ⟨k, hkC, hkE, hk⟩ := bar_mem_barOf_iff.1 hs
  have hA : k⁻¹ * s ∈ OddCore z := by
    have h1 : toBar z ⟨k⁻¹ * s, (Cen z).mul_mem ((Cen z).inv_mem hkC) hsC⟩ = 1 := by
      have : (⟨k⁻¹ * s, (Cen z).mul_mem ((Cen z).inv_mem hkC) hsC⟩ : ↥(Cen z)) =
          (⟨k, hkC⟩ : ↥(Cen z))⁻¹ * ⟨s, hsC⟩ := rfl
      rw [this, map_mul, map_inv, hk]
      group
    have h2 : (⟨k⁻¹ * s, (Cen z).mul_mem ((Cen z).inv_mem hkC) hsC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
      (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨_, h2, rfl⟩
  have hodd : Odd (orderOf (k⁻¹ * s)) := odd_orderOf_oddCore hA
  have hcomm : (k⁻¹ * s) * k = k * (k⁻¹ * s) := hL.oddcomm _ hA k (by rw [hL.layer]; exact hkE)
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨s, hsS⟩
  have hse : s ^ (2 ^ e) = 1 := by
    have h1 : (⟨s, hsS⟩ : ↥S) ^ (2 ^ e) = 1 := by rw [← he]; exact pow_orderOf_eq_one _
    have := congrArg Subtype.val h1
    simpa using this
  have hmem := mem_zpowers_of_odd_mul (s := s) (k := k) (a := k⁻¹ * s) (by group) hcomm hodd hse
  exact (Subgroup.zpowers_le.2 hkE) hmem

omit [Finite G] in
theorem eq_one_of_odd_of_two_pow {a : G} (hodd : Odd (orderOf a)) {e : ℕ} (he : orderOf a = 2 ^ e) :
    a = 1 := by
  have : e = 0 := by
    by_contra hne
    rw [he] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [this, pow_zero] at he
  exact orderOf_eq_one_iff.1 he

omit [Finite G] in
theorem mem_oddCore_of_toBar_eq' {u v : G} (hu : u ∈ Cen z) (hv : v ∈ Cen z)
    (h : toBar z ⟨u, hu⟩ = toBar z ⟨v, hv⟩) : u⁻¹ * v ∈ OddCore z := by
  have h1 : toBar z ⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ = 1 := by
    have : (⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ : ↥(Cen z)) =
        (⟨u, hu⟩ : ↥(Cen z))⁻¹ * ⟨v, hv⟩ := rfl
    rw [this, map_mul, map_inv, h]
    group
  have h2 : (⟨u⁻¹ * v, (Cen z).mul_mem ((Cen z).inv_mem hu) hv⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
    (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h2, rfl⟩

theorem eq_of_toBar_eq {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) {u v : G} (hu : u ∈ S) (hv : v ∈ S)
    (huC : u ∈ Cen z) (hvC : v ∈ Cen z) (h : toBar z ⟨u, huC⟩ = toBar z ⟨v, hvC⟩) : u = v := by
  have hA : u⁻¹ * v ∈ OddCore z := mem_oddCore_of_toBar_eq' huC hvC h
  have hodd : Odd (orderOf (u⁻¹ * v)) := odd_orderOf_oddCore hA
  have hS : u⁻¹ * v ∈ S := S.mul_mem (S.inv_mem hu) hv
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨u⁻¹ * v, hS⟩
  have he' : orderOf (u⁻¹ * v) = 2 ^ e := by
    rw [← Subgroup.orderOf_coe (⟨u⁻¹ * v, hS⟩ : ↥S)] at he
    exact he
  have := eq_one_of_odd_of_two_pow hodd he'
  exact (inv_mul_eq_one.1 this)

variable {k : Kind} {S : Subgroup G} {q : ℕ} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem exists_sylow_lifts (ctx : Stage2Ctx G z k S) (hL : LDat z K₁ K₂ L₁ L₂) (hD : PDat z q L₁ L₂) :
    ∃ Q : Sylow 2 ↥L₁, ∀ x ∈ (Q : Subgroup ↥L₁), ∃ (r : G) (hr : r ∈ Cen z),
      r ∈ S ⊓ (K₁ ⊔ K₂) ∧ toBar z ⟨r, hr⟩ = (x : CentralizerBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  obtain ⟨T, hT⟩ := barIn_sylow (Cen z) ctx.sylow_top hSC
  have hSbar : IsSylowOf 2 (barOf z S) (⊤ : Subgroup (CentralizerBar z)) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · have h := T.isPGroup'
      rw [hT] at h
      exact h
    · rw [Subgroup.relIndex_top_right]
      have h := T.not_dvd_index
      rw [hT] at h
      exact h
  have hLnorm : (LBar z).Normal := by
    have h1 : ((LC z).subgroupOf (Cen z)).Normal := LC_normal z
    exact h1.map (toBar z) (QuotientGroup.mk'_surjective _)
  have h2 : IsSylowOf 2 (barOf z S ⊓ LBar z) (LBar z) :=
    hSbar.inf_of_le_normalizer le_top (fun x _ => Subgroup.mem_normalizer_iff.2 fun h =>
      ⟨fun hh => hLnorm.conj_mem h hh x, fun hh => by
        have h1 := hLnorm.conj_mem _ hh x⁻¹
        have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
        rwa [e] at h1⟩)
  have hLle : L₁ ≤ LBar z := hD.sup ▸ le_sup_left
  have hKN : LBar z ≤ normalizer (L₁ : Set (CentralizerBar z)) := by
    rw [← hD.sup]
    refine sup_le Subgroup.le_normalizer (fun b hb => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : b * x * b⁻¹ = x := by rw [← hD.comm x hx b hb]; group
      rw [this]; exact hx
    · intro hx'
      have h1 : (b * x * b⁻¹) * b = b * (b * x * b⁻¹) := hD.comm _ hx' b hb
      have : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [h1]
          _ = b * x * b⁻¹ := by group
      rw [this]; exact hx'
  have h3 : IsSylowOf 2 ((barOf z S ⊓ LBar z) ⊓ L₁) L₁ := h2.inf_of_le_normalizer hLle hKN
  obtain ⟨Q, hQ⟩ := h3.exists_sylow_eq_subgroupOf
  refine ⟨Q, fun x hx => ?_⟩
  rw [hQ] at hx
  have hx' : (x : CentralizerBar z) ∈ (barOf z S ⊓ LBar z) ⊓ L₁ := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨s, hsC, hsS, hs⟩ := bar_mem_barOf_iff.1 hx'.1.1
  have hxL : (x : CentralizerBar z) ∈ L₁ ⊔ L₂ := by rw [hD.sup]; exact hx'.1.2
  exact ⟨s, hsC, ⟨hsS, mem_layer_of_bar_mem ctx.sylow.isPGroup hL hsS hsC (hs ▸ hxL)⟩, hs⟩

theorem RC_eq_inf_layer (hS2 : IsPGroup 2 ↥S) (hSC : S ≤ Cen z) (hL : LDat z K₁ K₂ L₁ L₂)
    (hD : PDat z q L₁ L₂) : RC S z = S ⊓ (K₁ ⊔ K₂) := by
  ext r
  constructor
  · intro hr
    have hrS : r ∈ S := hr.1
    have hrC : r ∈ Cen z := hSC hrS
    have hbar : toBar z ⟨r, hrC⟩ ∈ L₁ ⊔ L₂ := by
      rw [hD.sup]
      exact bar_mem_barOf_iff.2 ⟨r, hrC, hr.2, rfl⟩
    exact ⟨hrS, mem_layer_of_bar_mem hS2 hL hrS hrC hbar⟩
  · intro hr
    refine ⟨hr.1, em_le_LC z ?_⟩
    rw [hL.layer]; exact hr.2

theorem mem_inf_of_central_of_layer (ctx : Stage2Ctx G z k S) (hL : LDat z K₁ K₂ L₁ L₂)
    (hD : PDat z q L₁ L₂) {u : G} (huS : u ∈ S ⊓ (K₁ ⊔ K₂)) (hu2 : u * u = 1)
    (huc : ∀ r ∈ S ⊓ (K₁ ⊔ K₂), u * r = r * u) :
    ∃ hu : u ∈ Cen z, toBar z ⟨u, hu⟩ ∈ L₁ ⊓ L₂ := by
  have huC : u ∈ Cen z := ctx.S_le_Cen huS.1
  refine ⟨huC, ?_⟩
  have hbar : toBar z ⟨u, huC⟩ ∈ L₁ ⊔ L₂ := by
    rw [← barOf_sup_eq hL]; exact bar_mem_barOf_iff.2 ⟨u, huC, huS.2, rfl⟩
  obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ :=
    CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hD.comm hbar
  have hsqb : toBar z ⟨u, huC⟩ * toBar z ⟨u, huC⟩ = 1 := by
    rw [← map_mul, show (⟨u, huC⟩ : ↥(Cen z)) * ⟨u, huC⟩ = 1 from Subtype.ext hu2, map_one]
  rw [hll] at hsqb
  have hc12 : l₁ * l₂ = l₂ * l₁ := hD.comm l₁ hl₁ l₂ hl₂
  have hsq : (l₁ * l₁) * (l₂ * l₂) = 1 := by
    calc (l₁ * l₁) * (l₂ * l₂) = l₁ * (l₁ * l₂) * l₂ := by group
      _ = l₁ * (l₂ * l₁) * l₂ := by rw [hc12]
      _ = (l₁ * l₂) * (l₁ * l₂) := by group
      _ = 1 := hsqb
  have hsq₁ : l₁ * l₁ ∈ L₁ ⊓ L₂ := ⟨L₁.mul_mem hl₁ hl₁, by
      have : l₁ * l₁ = (l₂ * l₂)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]; exact L₂.inv_mem (L₂.mul_mem hl₂ hl₂)⟩
  have hsq₂ : l₂ * l₂ ∈ L₁ ⊓ L₂ := ⟨by
      have : l₂ * l₂ = (l₁ * l₁)⁻¹ := eq_inv_of_mul_eq_one_right hsq
      rw [this]; exact L₁.inv_mem (L₁.mul_mem hl₁ hl₁), L₂.mul_mem hl₂ hl₂⟩
  have hl₁4 : l₁ ^ 4 = 1 := by
    have h1 := mul_self_eq_one_of_card_le_two' hD.card.le (⟨l₁ * l₁, hsq₁⟩ : ↥(L₁ ⊓ L₂))
    have h2 : (l₁ * l₁) * (l₁ * l₁) = 1 := congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : CentralizerBar z)) h1
    calc l₁ ^ 4 = (l₁ * l₁) * (l₁ * l₁) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := h2
  have hl₂4 : l₂ ^ 4 = 1 := by
    have h1 := mul_self_eq_one_of_card_le_two' hD.card.le (⟨l₂ * l₂, hsq₂⟩ : ↥(L₁ ⊓ L₂))
    have h2 : (l₂ * l₂) * (l₂ * l₂) = 1 := congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : CentralizerBar z)) h1
    calc l₂ ^ 4 = (l₂ * l₂) * (l₂ * l₂) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := h2
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_lifts ctx hL hD
  obtain ⟨Q₂, hQ₂⟩ := exists_sylow_lifts ctx hL.symm hD.symm
  have hcen₁ : ∀ x ∈ (Q₁ : Subgroup ↥L₁), l₁ * (x : CentralizerBar z) = (x : CentralizerBar z) * l₁ := by
    intro x hx
    obtain ⟨r, hr, hrR, hrx⟩ := hQ₁ x hx
    have h1 : toBar z ⟨u, huC⟩ * toBar z ⟨r, hr⟩ = toBar z ⟨r, hr⟩ * toBar z ⟨u, huC⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (huc r hrR)
    rw [hrx, hll] at h1
    have h2 : (x : CentralizerBar z) * l₂ = l₂ * x := hD.comm x x.2 l₂ hl₂
    have h3 : (l₁ * x) * l₂ = (x * l₁) * l₂ := by
      calc (l₁ * x) * l₂ = l₁ * (x * l₂) := by group
        _ = l₁ * (l₂ * x) := by rw [h2]
        _ = (l₁ * l₂) * x := by group
        _ = x * (l₁ * l₂) := h1
        _ = (x * l₁) * l₂ := by group
    exact mul_right_cancel h3
  have hcen₂ : ∀ x ∈ (Q₂ : Subgroup ↥L₂), l₂ * (x : CentralizerBar z) = (x : CentralizerBar z) * l₂ := by
    intro x hx
    obtain ⟨r, hr, hrR, hrx⟩ := hQ₂ x hx
    have hrR' : r ∈ S ⊓ (K₁ ⊔ K₂) := ⟨hrR.1, by rw [sup_comm]; exact hrR.2⟩
    have h1 : toBar z ⟨u, huC⟩ * toBar z ⟨r, hr⟩ = toBar z ⟨r, hr⟩ * toBar z ⟨u, huC⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (huc r hrR')
    rw [hrx, hll] at h1
    have h2 : l₁ * (x : CentralizerBar z) = (x : CentralizerBar z) * l₁ := hD.comm l₁ hl₁ x x.2
    have h3 : l₁ * (l₂ * x) = l₁ * (x * l₂) := by
      calc l₁ * (l₂ * x) = (l₁ * l₂) * x := by group
        _ = x * (l₁ * l₂) := h1
        _ = (x * l₁) * l₂ := by group
        _ = (l₁ * x) * l₂ := by rw [h2]
        _ = l₁ * (x * l₂) := by group
    exact mul_left_cancel h3
  have hl₁₂ : l₁ ∈ L₂ := mem_inf_of_central_sylow hD.odd hD.sl₁ hD.card Q₁ hl₁ hl₁4 hcen₁
  have hl₂₁ : l₂ ∈ L₁ :=
    mem_inf_of_central_sylow hD.symm.odd hD.symm.sl₁ hD.symm.card Q₂ hl₂ hl₂4 hcen₂
  rw [hll]
  exact (L₁ ⊓ L₂).mul_mem ⟨hl₁, hl₁₂⟩ ⟨hl₂₁, hl₂⟩

omit [Finite G] in
theorem eq_one_or_eq_of_zpowers' {z y : G} (hz2 : z * z = 1) (h : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have hsq : z ^ 2 = 1 := by rw [sq]; exact hz2
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← Int.emod_add_mul_ediv n 2, h0, zero_add, zpow_mul]
    simp [hsq]
  · right
    rw [← Int.emod_add_mul_ediv n 2, h1, zpow_add, zpow_mul]
    simp [hsq]

theorem isFourSubgroup_zpowers_sup {z w : G} (hz : z * z = 1) (hw : w * w = 1) (hzw : z * w = w * z)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hne : z ≠ w) : IVK.IsFourSubgroup (zpowers z ⊔ zpowers w) := by
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow (show Commute z w from hzw) i j)).eq
  have hsq : ∀ x ∈ zpowers z ⊔ zpowers w, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hcomm hx
    have ha2 : a * a = 1 := by
      rcases eq_one_or_eq_of_zpowers' hz ha with h | h <;> rw [h] <;> simp [hz]
    have hb2 : b * b = 1 := by
      rcases eq_one_or_eq_of_zpowers' hw hb with h | h <;> rw [h] <;> simp [hw]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hc : ∀ x ∈ zpowers z ⊔ zpowers w, ∀ y ∈ zpowers z ⊔ zpowers w, x * y = y * x := by
    intro x hx y hy
    have hxy := hsq (x * y) ((zpowers z ⊔ zpowers w).mul_mem hx hy)
    have hxx := hsq x hx
    have hyy := hsq y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    rw [this, mul_inv_rev, hxi, hyi]
  refine ⟨?_, ?_⟩
  · have hc' : IsMulCommutative ↥(zpowers z ⊔ zpowers w) :=
      isMulCommutative_iff.mpr (fun a b => Subtype.ext (hc a a.2 b b.2))
    refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext ?_)⟩
    rw [Subgroup.coe_pow, pow_two]
    exact hsq g g.2
  · have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
    have hw2' : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw) hw1
    have hinf : zpowers z ⊓ zpowers w = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rcases eq_one_or_eq_of_zpowers' hz hx1 with h | h
      · simp [h]
      · rcases eq_one_or_eq_of_zpowers' hw hx2 with h' | h'
        · exact absurd (h.symm.trans h') hz1
        · exact absurd (h.symm.trans h') hne
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers z) (zpowers w) hcomm).1
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hz2', hw2'] at hprod
    omega

end GLevel

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.ClaimG

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20
  CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.ClaimG
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_S1_iff bar_S1_le_S)
open CFSG.GH74.GLS.Stage1.Thm6.Prod (LC_normal)

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem claimG (ctx : Stage2Ctx G z k S) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hK : CompData z K₁ K₂ L₁ L₂) :
    ∀ w ∈ S, orderOf w = 2 → (∀ r ∈ S ⊓ (K₁ ⊔ K₂), w * r = r * w) → w = z := by
  intro w hwS hw2 hwR
  by_contra hwz
  have hfinrel : ∀ A B : Subgroup G, A.IsFiniteRelIndex B := fun A B =>
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hL := LDat.of_compData hK
  have hD := PDat.of_stage1Pair hP
  have hPS := PairShape.of_stage1Pair hP
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have hSp : IsPGroup 2 ↥S := ctx.sylow.isPGroup
  have hz2 : orderOf z = 2 := ctx.orderOf_z
  have hRC : RC S z = S ⊓ (K₁ ⊔ K₂) := RC_eq_inf_layer hSp hSC hL hD
  set R : Subgroup G := S ⊓ (K₁ ⊔ K₂) with hRdef
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at this
  have hzS : z ∈ S := ctx.z_mem
  have hzR : z ∈ R := by
    rw [← hRC]
    exact ⟨hzS, one_z_mem_LC hP hz2⟩
  have hSz : ∀ s ∈ S, s * z = z * s := fun s hs => ctx.S_comm_z hs
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hw1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hw2; omega
  have hZR : ∀ u ∈ R, u * u = 1 → (∀ r ∈ R, u * r = r * u) → u = 1 ∨ u = z := by
    intro u huR hu2 huc
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    right
    obtain ⟨huC, hub⟩ := mem_inf_of_central_of_layer ctx hL hD huR hu2 huc
    obtain ⟨hzC, hzb⟩ :=
      mem_inf_of_central_of_layer ctx hL hD hzR hzsq (fun r hr => (hSz r hr.1).symm)
    have hu_ne : toBar z ⟨u, huC⟩ ≠ 1 := by
      intro h
      apply hu1
      refine eq_of_toBar_eq hSp huR.1 S.one_mem huC (Cen z).one_mem ?_
      rw [h]
      exact (map_one (toBar z)).symm
    have hz_ne : toBar z ⟨z, hzC⟩ ≠ 1 := one_toBar_z_ne_one hz2
    have := eq_of_card_two hD.card (a := ⟨_, hub⟩) (b := ⟨_, hzb⟩)
      (fun h => hu_ne (congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : CentralizerBar z)) h))
      (fun h => hz_ne (congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : CentralizerBar z)) h))
    exact eq_of_toBar_eq hSp huR.1 hzS huC hzC
      (congrArg (fun w : ↥(L₁ ⊓ L₂) => (w : CentralizerBar z)) this)
  set Y : Subgroup G := S ⊓ centralizer (R : Set G) with hYdef
  have hwY : w ∈ Y := ⟨hwS, Subgroup.mem_centralizer_iff.2 (fun r hr => (hwR r hr).symm)⟩
  have hRn : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs r hr
    rw [← hRC] at hr ⊢
    refine ⟨S.mul_mem (S.mul_mem hs hr.1) (S.inv_mem hs), ?_⟩
    have hLn := LC_normal z
    have := hLn.conj_mem ⟨r, hSC hr.1⟩ (Subgroup.mem_subgroupOf.2 hr.2) ⟨s, hSC hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hYn : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
    intro s hs y hy
    refine ⟨S.mul_mem (S.mul_mem hs hy.1) (S.inv_mem hs), Subgroup.mem_centralizer_iff.2 (fun r hr => ?_)⟩
    have h1 := hRn s⁻¹ (S.inv_mem hs) r hr
    rw [inv_inv] at h1
    have h2 := Subgroup.mem_centralizer_iff.1 hy.2 _ h1
    calc r * (s * y * s⁻¹) = s * ((s⁻¹ * r * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * r * s)) * s⁻¹ := by rw [h2]
      _ = (s * y * s⁻¹) * r := by group
  obtain ⟨Q₁, hQ₁⟩ := exists_sylow_lifts ctx hL hD
  have hYS1 : ∀ y ∈ Y, y ∈ S1 S z := by
    intro y hy
    have hyS : y ∈ S := hy.1
    have hyC : y ∈ Cen z := hSC hyS
    have hyR : ∀ r ∈ R, y * r = r * y := fun r hr =>
      (Subgroup.mem_centralizer_iff.1 hy.2 r hr).symm
    have hfix₁ : cj (toBar z ⟨y, hyC⟩) L₁ = L₁ := by
      rcases hPS.cj_cases (toBar z ⟨y, hyC⟩) with h | h
      · exact h
      · exfalso
        refine no_swap_of_sylow hD.odd hD.sl₁ hD.card Q₁ (c := toBar z ⟨y, hyC⟩) ?_ ?_
        · intro x hx
          obtain ⟨r, hr, hrR, hrx⟩ := hQ₁ x hx
          have h1 : toBar z ⟨y, hyC⟩ * toBar z ⟨r, hr⟩ = toBar z ⟨r, hr⟩ * toBar z ⟨y, hyC⟩ := by
            rw [← map_mul, ← map_mul]
            congr 1
            exact Subtype.ext (hyR r hrR)
          rw [hrx] at h1
          rw [h1]; group
        · intro x hx
          have h1 : (toBar z ⟨y, hyC⟩)⁻¹ * (toBar z ⟨y, hyC⟩ * x * (toBar z ⟨y, hyC⟩)⁻¹) *
              toBar z ⟨y, hyC⟩ ∈ L₁ := by
            rw [show (toBar z ⟨y, hyC⟩)⁻¹ * (toBar z ⟨y, hyC⟩ * x * (toBar z ⟨y, hyC⟩)⁻¹) *
              toBar z ⟨y, hyC⟩ = x by group]
            exact hx
          have h2 := mem_cj.2 h1
          rwa [h] at h2
    have hfix₂ : cj (toBar z ⟨y, hyC⟩) L₂ = L₂ := hPS.cj_fix hfix₁
    rw [bar_mem_S1_iff]
    refine ⟨hyS, hyC, fun K hK' _ => ?_⟩
    rcases hPS.comps K hK' with rfl | rfl
    · exact cj_eq_iff.1 hfix₁
    · exact cj_eq_iff.1 hfix₂
  have hRS1 : R ≤ S1 S z := by
    intro r hr
    have hrC : r ∈ Cen z := hSC hr.1
    have hbar : toBar z ⟨r, hrC⟩ ∈ L₁ ⊔ L₂ := by
      rw [← barOf_sup_eq hL]; exact bar_mem_barOf_iff.2 ⟨r, hrC, hr.2, rfl⟩
    have h1 : cj (toBar z ⟨r, hrC⟩) L₁ = L₁ := hPS.cj_fix_of_mem_sup hbar
    have h2 : cj (toBar z ⟨r, hrC⟩) L₂ = L₂ := hPS.cj_fix h1
    rw [bar_mem_S1_iff]
    refine ⟨hr.1, hrC, fun K hK' _ => ?_⟩
    rcases hPS.comps K hK' with rfl | rfl
    · exact cj_eq_iff.1 h1
    · exact cj_eq_iff.1 h2
  obtain ⟨s₀, hs₀S, hsw⟩ := hP.swap
  have hs₀ : s₀ ∉ S1 S z := by
    intro hs₀1
    obtain ⟨ht, h1, h2⟩ := hsw
    obtain ⟨-, ht', hn⟩ := bar_mem_S1_iff.1 hs₀1
    have hnorm := hn L₁ hPS.c₁ (hD.sup ▸ le_sup_left)
    apply hP.ne
    ext x
    rw [← h1, SL2Bound.bar_mem_conjugate_iff]
    exact Subgroup.mem_normalizer_iff.1 hnorm x
  have hrel4 : R.relIndex S ≤ 4 := by rw [← hRC]; exact hidx
  have hrel2 : R.relIndex (S1 S z) ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_relIndex R (S1 S z) S hRS1 bar_S1_le_S
    have h2 : (S1 S z).relIndex S ≠ 1 := fun h => hs₀ ((Subgroup.relIndex_eq_one.1 h) hs₀S)
    have h3 : (S1 S z).relIndex S ≠ 0 := Subgroup.relIndex_ne_zero
    have h4 : 2 ≤ (S1 S z).relIndex S := by omega
    by_contra hcon
    push Not at hcon
    nlinarith
  have hY2 : R.relIndex Y ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right (fun y hy => hYS1 y hy) Subgroup.relIndex_ne_zero).trans hrel2
  have hwR' : w ∉ R := by
    intro hwr
    rcases hZR w hwr hww (fun r hr => hwR r hr) with h | h
    · exact hw1 h
    · exact hwz h
  have hrelY : R.relIndex Y = 2 := by
    have h1 : R.relIndex Y ≠ 1 := fun h => hwR' ((Subgroup.relIndex_eq_one.1 h) hwY)
    have h2 : R.relIndex Y ≠ 0 := Subgroup.relIndex_ne_zero
    omega
  have hzw : z * w = w * z := (hSz w hwS).symm
  have hinvY : ∀ y ∈ Y, y * y = 1 → y = 1 ∨ y = z ∨ y = w ∨ y = z * w := by
    intro y hy hy2
    by_cases hyR : y ∈ R
    · rcases hZR y hyR hy2 (fun r hr => (Subgroup.mem_centralizer_iff.1 hy.2 r hr).symm) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨c, hcdef⟩ : ∃ c, c = w⁻¹ * y := ⟨_, rfl⟩
      have hc : c ∈ R := by rw [hcdef]; exact inv_mul_mem_of_relIndex_two hrelY hwY hy hwR' hyR
      have hcY : c ∈ Y := by rw [hcdef]; exact Y.mul_mem (Y.inv_mem hwY) hy
      have hcc : ∀ r ∈ R, c * r = r * c := fun r hr =>
        (Subgroup.mem_centralizer_iff.1 hcY.2 r hr).symm
      have hwc : w * c = c * w := hwR c hc
      have hyw : y = w * c := by rw [hcdef]; group
      have hcsq : c * c = 1 := by
        have h1 : (w * c) * (w * c) = (w * w) * (c * c) := by
          calc (w * c) * (w * c) = w * (c * w) * c := by group
            _ = w * (w * c) * c := by rw [← hwc]
            _ = (w * w) * (c * c) := by group
        rw [hww, one_mul, ← hyw] at h1
        rw [← h1]; exact hy2
      rcases hZR c hc hcsq hcc with h | h
      · right; right; left
        rw [hyw, h, mul_one]
      · right; right; right
        rw [hyw, h, ← hzw]
  have hFour : IVK.IsFourSubgroup (zpowers z ⊔ zpowers w) :=
    isFourSubgroup_zpowers_sup hzsq hww hzw hz1 hw1 (Ne.symm hwz)
  have hUS : zpowers z ⊔ zpowers w ≤ S :=
    sup_le (Subgroup.zpowers_le.2 hzS) (Subgroup.zpowers_le.2 hwS)
  have hUn : ∀ s ∈ S, ∀ u ∈ zpowers z ⊔ zpowers w, s * u * s⁻¹ ∈ zpowers z ⊔ zpowers w := by
    intro s hs u hu
    have hzs : s * z * s⁻¹ = z := by rw [hSz s hs]; group
    have hws : s * w * s⁻¹ ∈ zpowers z ⊔ zpowers w := by
      have hy : s * w * s⁻¹ ∈ Y := hYn s hs w hwY
      have hysq : (s * w * s⁻¹) * (s * w * s⁻¹) = 1 := by
        calc (s * w * s⁻¹) * (s * w * s⁻¹) = s * (w * w) * s⁻¹ := by group
          _ = 1 := by rw [hww]; group
      rcases hinvY _ hy hysq with h | h | h | h
      · rw [h]; exact (zpowers z ⊔ zpowers w).one_mem
      · rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      · rw [h]
        exact (zpowers z ⊔ zpowers w).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    have hle : zpowers z ⊔ zpowers w ≤
        (zpowers z ⊔ zpowers w).comap (MulAut.conj s).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_comap]
        change s * z * s⁻¹ ∈ zpowers z ⊔ zpowers w
        rw [hzs]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      · rw [Subgroup.mem_comap]
        exact hws
    have := hle hu
    rw [Subgroup.mem_comap] at this
    exact this
  have hULC : zpowers z ⊔ zpowers w ≤ LC z := hP.base.four_le _ hUS hFour hUn
  have hwLC : w ∈ LC z := hULC (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  apply hwR'
  rw [← hRC]
  exact ⟨hwS, hwLC⟩

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
