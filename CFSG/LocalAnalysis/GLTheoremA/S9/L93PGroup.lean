module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l93_three_S1 {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center (PQuot p L))) :
    ∀ g ∈ L, (∀ l ∈ L, ⁅l, g⁆ ∈ GLAPPrimeCoreOf p L) → g ∈ GLAPPrimeCoreOf p L := by
  intro g hgL hg
  haveI : Fact p.Prime := ⟨hp⟩
  set O' : Subgroup ↥L := GLAPPrimeCore p ↥L with hO'
  set Z : Subgroup (PQuot p L) := Subgroup.center (PQuot p L) with hZdef
  set Zt : Subgroup ↥L := Z.comap (QuotientGroup.mk' O') with hZt
  have hsurj : Function.Surjective (QuotientGroup.mk' O' : ↥L →* PQuot p L) :=
    QuotientGroup.mk'_surjective O'
  have hidx : Zt.index = Z.index := Subgroup.index_comap_of_surjective Z hsurj
  have hne : Zt.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcardZt : Nat.card Zt = Nat.card Z * Nat.card O' := by
    have h1 : Nat.card Zt * Z.index = Nat.card ↥L := by
      rw [← hidx]
      exact Subgroup.card_mul_index Zt
    have h2 : Nat.card Z * Z.index = Nat.card (PQuot p L) := Subgroup.card_mul_index Z
    have h3 : Nat.card ↥L = Nat.card (PQuot p L) * Nat.card O' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup O'
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (hidx ▸ hne))
    rw [h1, h3, ← h2]
    ring
  have hO'card : Nat.card O' = Nat.card (GLAPPrimeCoreOf p L) := by
    unfold GLAPPrimeCoreOf
    exact (Subgroup.card_map_of_injective L.subtype_injective).symm
  have hcopO' : Nat.Coprime p (Nat.card O') := by
    rw [hO'card]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp L)
  have hcopZ : Nat.Coprime p (Nat.card Z) := (Nat.Prime.coprime_iff_not_dvd hp).2 hZ
  have hcopZt : Nat.Coprime p (Nat.card Zt) := by
    rw [hcardZt]
    exact Nat.Coprime.mul_right hcopZ hcopO'
  have hZtle : Zt ≤ O' := le_sSup ⟨inferInstance, hcopZt⟩
  have hmem : (⟨g, hgL⟩ : ↥L) ∈ Zt :=
    mk_mem_center_of_mem_centModSubgroup hgL (mem_centModSubgroup.2 ⟨Subgroup.le_normalizer hgL, hg⟩)
  exact Subgroup.mem_map.2 ⟨⟨g, hgL⟩, hZtle hmem, rfl⟩

private theorem l93_inter_eq_bot {p : ℕ} (hp : p.Prime) {P O : Subgroup G} (hP : IsPGroup p P)
    (hO : Nat.Coprime p (Nat.card O)) : P ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgP, hgO⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have hk' : g ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hord1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hord2 : orderOf g ∣ Nat.card O := by
    have h := orderOf_dvd_natCard (⟨g, hgO⟩ : ↥O)
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime (orderOf g) p := Nat.Coprime.coprime_dvd_left hord2 hO.symm
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hord1
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h1)

private theorem l93_B_le_normalizer_C {p : ℕ} {B L : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    B ≤ Subgroup.normalizer ((centModSubgroup p L : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact S3.conj_mem_centModSubgroup (hBL hb) ha
  · intro ha
    have h1 := S3.conj_mem_centModSubgroup (Subgroup.inv_mem _ (hBL hb)) ha
    have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
    rw [e] at h1
    exact h1

private theorem l93_three_S2 {p : ℕ} {B L : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBO : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G))
    (hin : ∀ b ∈ B, InducesInnerMod p L b) :
    ∀ b ∈ B, ∃ c ∈ centModSubgroup p L, ∃ l ∈ L, b = c * l := by
  intro b hb
  obtain ⟨l₀, hl₀, hall⟩ := hin b hb
  refine ⟨b * l₀⁻¹, ?_, l₀, hl₀, by group⟩
  have hcN : b * l₀⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hBL hb) (Subgroup.inv_mem _ (Subgroup.le_normalizer hl₀))
  refine mem_centModSubgroup.2 ⟨hcN, fun y hy => ?_⟩
  have hO : (l₀⁻¹ * y * l₀)⁻¹ * (b⁻¹ * y * b) ∈ GLAPPrimeCoreOf p L := hall y hy
  have hbo : b * ((l₀⁻¹ * y * l₀)⁻¹ * (b⁻¹ * y * b))⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf p L :=
    (Subgroup.mem_normalizer_iff.1 (hBO hb) _).1 (Subgroup.inv_mem _ hO)
  have hcy : ⁅b * l₀⁻¹, y⁆ = y * (b * ((l₀⁻¹ * y * l₀)⁻¹ * (b⁻¹ * y * b))⁻¹ * b⁻¹) * y⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hmem : ⁅b * l₀⁻¹, y⁆ ∈ GLAPPrimeCoreOf p L := by
    rw [hcy]
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L hy) _).1 hbo
  have hyc : ⁅y, b * l₀⁻¹⁆ = (⁅b * l₀⁻¹, y⁆)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hyc]
  exact Subgroup.inv_mem _ hmem

open scoped Pointwise in
private theorem l93_mod {p : ℕ} {B L : Subgroup G}
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hBexp : ∀ b ∈ B, b ^ p = 1) :
    ∀ r ∈ B ⊔ centModSubgroup p L, ∀ r' ∈ B ⊔ centModSubgroup p L,
      ⁅r, r'⁆ ∈ centModSubgroup p L ∧ r ^ p ∈ centModSubgroup p L := by
  classical
  have hBC : B ≤ Subgroup.normalizer ((centModSubgroup p L : Subgroup G) : Set G) :=
    l93_B_le_normalizer_C hBL
  have hCK : centModSubgroup p L ≤ B ⊔ centModSubgroup p L := le_sup_right
  have hKN : B ⊔ centModSubgroup p L ≤
      Subgroup.normalizer ((centModSubgroup p L : Subgroup G) : Set G) :=
    sup_le hBC Subgroup.le_normalizer
  haveI hCnorm : ((centModSubgroup p L).subgroupOf (B ⊔ centModSubgroup p L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).2 hKN
  set K : Subgroup G := B ⊔ centModSubgroup p L with hK
  set q : K →* K ⧸ (centModSubgroup p L).subgroupOf K := QuotientGroup.mk' _ with hq
  have hqb : ∀ r (hr : r ∈ K), ∃ b, ∃ hb : b ∈ B, q ⟨r, hr⟩ = q ⟨b, Subgroup.mem_sup_left hb⟩ := by
    intro r hr
    have hr' : r ∈ (B : Set G) * (centModSubgroup p L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B (centModSubgroup p L) hBC]
      exact hr
    obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_mul.1 hr'
    refine ⟨b, hb, ?_⟩
    have hcq : q ⟨c, Subgroup.mem_sup_right hc⟩ = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hc
    have he : (⟨r, hr⟩ : K) = ⟨b, Subgroup.mem_sup_left hb⟩ * ⟨c, Subgroup.mem_sup_right hc⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; exact hbc.symm)
    rw [he, map_mul, hcq, mul_one]
  have hqcomm : ∀ r (hr : r ∈ K) r' (hr' : r' ∈ K), Commute (q ⟨r, hr⟩) (q ⟨r', hr'⟩) := by
    intro r hr r' hr'
    obtain ⟨b, hb, hqr⟩ := hqb r hr
    obtain ⟨b', hb', hqr'⟩ := hqb r' hr'
    rw [hqr, hqr']
    have h1 : Commute (⟨b, Subgroup.mem_sup_left hb⟩ : K) ⟨b', Subgroup.mem_sup_left hb'⟩ :=
      Subtype.ext (hBab b hb b' hb')
    exact h1.map q
  have hKc : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ K := by
    intro x hx y hy
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  intro r hr r' hr'
  constructor
  ·
    have hcK : ⁅r, r'⁆ ∈ K := hKc r hr r' hr'
    have h1 : q ⟨⁅r, r'⁆, hcK⟩ = 1 := by
      have e : q ⟨⁅r, r'⁆, hcK⟩ = ⁅q ⟨r, hr⟩, q ⟨r', hr'⟩⁆ := by
        have : (⟨⁅r, r'⁆, hcK⟩ : K) = ⁅(⟨r, hr⟩ : K), ⟨r', hr'⟩⁆ :=
          Subtype.ext (by simp [commutatorElement_def])
        rw [this]
        simp only [commutatorElement_def, map_mul, map_inv]
      rw [e]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hqcomm r hr r' hr').eq
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (Subgroup.mem_subgroupOf.1 h1)
  ·
    obtain ⟨b, hb, hqr⟩ := hqb r hr
    have h1 : q (⟨r, hr⟩ ^ p) = 1 := by
      rw [map_pow, hqr, ← map_pow]
      have : (⟨b, Subgroup.mem_sup_left hb⟩ : K) ^ p = 1 := Subtype.ext (hBexp b hb)
      rw [this, map_one]
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1

private theorem l93_closure {p : ℕ} {O Y : Subgroup G} {S : Set G}
    (hY : Subgroup.closure S = Y) (hOY : O ≤ Y) (hYN : Y ≤ Subgroup.normalizer (O : Set G))
    (hSc : ∀ g ∈ S, ∀ h ∈ S, ⁅g, h⁆ ∈ O) (hSp : ∀ g ∈ S, g ^ p ∈ O) :
    (∀ y ∈ Y, ∀ z ∈ Y, ⁅y, z⁆ ∈ O) ∧ (∀ y ∈ Y, y ^ p ∈ O) := by
  classical
  have st1 : ∀ g ∈ S, ∀ z ∈ Y, ⁅g, z⁆ ∈ O := by
    intro g hg z hz
    rw [← hY] at hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact hSc g hg z hz
    | one => rw [commutatorElement_one_right]; exact O.one_mem
    | mul x w hx hw ihx ihw =>
      have hxY : x ∈ Y := hY ▸ hx
      have e : ⁅g, x * w⁆ = ⁅g, x⁆ * (x * ⁅g, w⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact O.mul_mem ihx ((Subgroup.mem_normalizer_iff.1 (hYN hxY) _).1 ihw)
    | inv x hx ihx =>
      have hxY : x ∈ Y := hY ▸ hx
      have e : ⁅g, x⁻¹⁆ = x⁻¹ * (⁅g, x⁆)⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      have h1 := (Subgroup.mem_normalizer_iff.1 (hYN (Y.inv_mem hxY)) _).1 (O.inv_mem ihx)
      rw [inv_inv] at h1
      rw [e]
      exact h1
  have st2 : ∀ y ∈ Y, ∀ z ∈ Y, ⁅y, z⁆ ∈ O := by
    intro y hy z hz
    rw [← hY] at hy
    induction hy using Subgroup.closure_induction with
    | mem g hg => exact st1 g hg z hz
    | one => rw [commutatorElement_one_left]; exact O.one_mem
    | mul x w hx hw ihx ihw =>
      have hxY : x ∈ Y := hY ▸ hx
      have e : ⁅x * w, z⁆ = x * ⁅w, z⁆ * x⁻¹ * ⁅x, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact O.mul_mem ((Subgroup.mem_normalizer_iff.1 (hYN hxY) _).1 ihw) ihx
    | inv x hx ihx =>
      have hxY : x ∈ Y := hY ▸ hx
      have e : ⁅x⁻¹, z⁆ = x⁻¹ * (⁅x, z⁆)⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      have h1 := (Subgroup.mem_normalizer_iff.1 (hYN (Y.inv_mem hxY)) _).1 (O.inv_mem ihx)
      rw [inv_inv] at h1
      rw [e]
      exact h1
  haveI hNn : (O.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2 hYN
  have mulp : ∀ x (hx : x ∈ Y) w (hw : w ∈ Y), x ^ p ∈ O → w ^ p ∈ O → (x * w) ^ p ∈ O := by
    intro x hx w hw hxp hwp
    set qY : Y →* Y ⧸ O.subgroupOf Y := QuotientGroup.mk' _ with hqY
    have hc : Commute (qY ⟨x, hx⟩) (qY ⟨w, hw⟩) := by
      have h1 : qY ⁅(⟨x, hx⟩ : Y), ⟨w, hw⟩⁆ = 1 := by
        rw [hqY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.2 (st2 x hx w hw)
      have h2 : qY ⁅(⟨x, hx⟩ : Y), ⟨w, hw⟩⁆ = ⁅qY ⟨x, hx⟩, qY ⟨w, hw⟩⁆ := by
        simp only [commutatorElement_def, map_mul, map_inv]
      rw [h2] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have h3 : qY ((⟨x, hx⟩ : Y) ^ p) = 1 := by
      rw [hqY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hxp
    have h4 : qY ((⟨w, hw⟩ : Y) ^ p) = 1 := by
      rw [hqY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hwp
    have h5 : qY ((⟨x, hx⟩ * ⟨w, hw⟩ : Y) ^ p) = 1 := by
      rw [map_pow, map_mul, hc.mul_pow, ← map_pow, ← map_pow, h3, h4, mul_one]
    rw [hqY, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
    exact Subgroup.mem_subgroupOf.1 h5
  have st3 : ∀ y ∈ Y, y ^ p ∈ O := by
    intro y hy
    rw [← hY] at hy
    induction hy using Subgroup.closure_induction with
    | mem g hg => exact hSp g hg
    | one => rw [one_pow]; exact O.one_mem
    | mul x w hx hw ihx ihw => exact mulp x (hY ▸ hx) w (hY ▸ hw) ihx ihw
    | inv x hx ihx => rw [inv_pow]; exact O.inv_mem ihx
  exact ⟨fun y hy z hz => st2 y hy z hz, st3⟩

theorem l93_exists_two_group_of_le_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G}
    {L T : Subgroup G} (h : H92 p B x L) (hT : T ≤ Subgroup.centralizer ({x} : Set G))
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hTle : T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hTO : ¬ T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    ∃ T₀ : Subgroup G, T₀ ≤ L ∧ IsPGroup 2 T₀ ∧ B ≤ Subgroup.normalizer (T₀ : Set G) ∧
      ¬ T₀ ≤ GLAPPrimeCoreOf p L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer h.bmax.1 h.mem
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian h.bmax.1
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set O : Subgroup G := GLAPPrimeCoreOf p Cx with hOdef
  set OL : Subgroup G := GLAPPrimeCoreOf p L with hOLdef
  have hCxO : Cx ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p Cx
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := hBCx.trans hCxO
  have hTO' : T ≤ Subgroup.normalizer (O : Set G) := hT.trans hCxO
  have hLO : L ⊓ O = OL := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp h.comp.2.1
  have hOL_le : OL ≤ O := by
    rw [← hLO]
    exact inf_le_right
  have hBT' : B ≤ Subgroup.normalizer ((T ⊔ O : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup T O ⟨hBT hb, hBO hb⟩
  set Ts : Subgroup G := L ⊓ (T ⊔ O) with hTs
  have hTsN : B ≤ Subgroup.normalizer (Ts : Set G) := fun b hb =>
    (Subgroup.inf_normalizer_le_normalizer_inf (H := L) (K := T ⊔ O)) ⟨h.norm hb, hBT' hb⟩
  have hTsL : Ts ≤ L := inf_le_left
  have hTsCx : Ts ≤ Cx := hTsL.trans h.comp.1
  have hLN : L ≤ Subgroup.normalizer (O : Set G) := h.comp.1.trans hCxO
  have hsup : O ⊔ Ts = T ⊔ O := by
    apply le_antisymm
    · exact sup_le le_sup_right inf_le_right
    · refine sup_le ?_ le_sup_left
      intro t ht
      have hmem : t ∈ (L ⊔ O : Subgroup G) := hTle ht
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L O hLN] at hmem
      obtain ⟨l, hl, o, ho, hlo⟩ := Set.mem_mul.1 hmem
      have hlT : l ∈ T ⊔ O := by
        have : l = t * o⁻¹ := by rw [← hlo]; group
        rw [this]
        exact (T ⊔ O).mul_mem (Subgroup.mem_sup_left ht) ((T ⊔ O).inv_mem (Subgroup.mem_sup_right ho))
      have hlTs : l ∈ Ts := Subgroup.mem_inf.2 ⟨hl, hlT⟩
      have hconj : l * o * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hLN hl) o).1 ho
      have : t = (l * o * l⁻¹) * l := by rw [hlo]; group
      rw [this]
      exact Subgroup.mul_mem_sup hconj hlTs
  have hTsO : O ⊓ Ts = OL := by
    rw [hTs, inf_left_comm, inf_eq_left.2 (le_sup_right : O ≤ T ⊔ O), hLO]
  have hid1 := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := Ts) (hTsCx.trans hCxO)
  have hid2 := card_sup_mul_card_inf_of_le_normalizer (A := O) (B := T) hTO'
  rw [hsup, hTsO] at hid1
  rw [sup_comm O T] at hid2
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have key : Nat.card Ts * Nat.card (O ⊓ T : Subgroup G) = Nat.card OL * Nat.card T := by
    apply Nat.eq_of_mul_eq_mul_left hOpos
    calc Nat.card O * (Nat.card Ts * Nat.card (O ⊓ T : Subgroup G))
        = (Nat.card O * Nat.card Ts) * Nat.card (O ⊓ T : Subgroup G) := by ring
      _ = (Nat.card (T ⊔ O : Subgroup G) * Nat.card OL) * Nat.card (O ⊓ T : Subgroup G) := by
          rw [hid1]
      _ = Nat.card OL * (Nat.card (T ⊔ O : Subgroup G) * Nat.card (O ⊓ T : Subgroup G)) := by ring
      _ = Nat.card OL * (Nat.card O * Nat.card T) := by rw [hid2]
      _ = Nat.card O * (Nat.card OL * Nat.card T) := by ring
  have hT2' : IsPGroup 2 ↥T := hT2
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card).1 hT2'
  obtain ⟨s, hs⟩ := (IsPGroup.iff_card).1 (hT2.to_le (inf_le_right : O ⊓ T ≤ T))
  have hOTlt : O ⊓ T < T := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    apply hTO
    intro g hg
    have : g ∈ O ⊓ T := by rw [heq]; exact hg
    exact (inf_le_left : O ⊓ T ≤ O) this
  have hst : s < t := by
    have hlt : Nat.card (O ⊓ T : Subgroup G) < Nat.card T := Subgroup.card_lt_of_lt hOTlt
    rw [hs, ht] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  obtain ⟨j, rfl⟩ : ∃ j, t = s + j + 1 := ⟨t - s - 1, by omega⟩
  have hTs_card : Nat.card Ts = Nat.card OL * 2 ^ (j + 1) := by
    have hk := key
    rw [hs, ht] at hk
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ s from by positivity)
    rw [hk]
    ring
  have hcopOL : Nat.Coprime p (Nat.card OL) := (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp L)
  have hcopTs : Nat.Coprime p (Nat.card Ts) := by
    rw [hTs_card]
    exact Nat.Coprime.mul_right hcopOL (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hBp' : IsPGroup p ↥B := hBp
  obtain ⟨Q, hQTs, hQ2, hQprop, hBQ⟩ :=
    exists_sylow_normalized_of_not_dvd (p := p) (q := 2) Ts B hBp hTsN ((Nat.Prime.coprime_iff_not_dvd hp).1 hcopTs)
  refine ⟨Q, hQTs.trans hTsL, hQ2, hBQ, ?_⟩
  intro hQOL
  have hOLne : Nat.card OL ≠ 0 := (Nat.card_pos).ne'
  set n : ℕ := (Nat.card OL).factorization 2 with hn
  have hn_not : ¬ 2 ^ (n + 1) ∣ Nat.card OL :=
    Nat.pow_succ_factorization_not_dvd hOLne Nat.prime_two
  obtain ⟨k, hk⟩ := Nat.ordProj_dvd (Nat.card OL) 2
  have hk' : Nat.card OL = 2 ^ n * k := hk
  have hdvdTs : 2 ^ (n + 1) ∣ Nat.card Ts := by
    rw [hTs_card, hk']
    exact ⟨k * 2 ^ j, by ring⟩
  have hdvdQ := hQprop _ hdvdTs
  exact hn_not (dvd_trans hdvdQ (Subgroup.card_dvd_of_le hQOL))

theorem l93_nonInner_or_center {p : ℕ} (hc : S9Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : H92 p B x L) (hmax : IsMaxRankIn p B (Subgroup.centralizer ({x} : Set G)))
    (hA : ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({x} : Set G) ⊓ centModSubgroup p L ∧
      IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A) :
    (∃ b ∈ B, ¬ InducesInnerMod p L b) ∨ p ∣ Nat.card (Subgroup.center (PQuot p L)) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hinner, hZ⟩ := hcon
  obtain ⟨A, hAC, hAel, hA2⟩ := hA
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsElemAbelian p B := h.bmax.1
  have hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => isElemAbelian_commute hB hb hb'
  have hBexp : ∀ b ∈ B, b ^ p = 1 := fun b hb => hB.2 b hb
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  obtain ⟨mB, hmB⟩ := (IsPGroup.iff_card).1 hBp
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hAel
  have ha2 : 2 ≤ a := by
    have h1 : p ^ 2 ≤ p ^ a := ha ▸ hA2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hAel
  set O : Subgroup G := GLAPPrimeCoreOf p L with hOdef
  set C : Subgroup G := centModSubgroup p L with hCdef
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hcopO : Nat.Coprime p (Nat.card O) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp L)
  have hLN : L ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf p L
  have hNO : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := h.norm.trans hNO
  have hS1 : ∀ g ∈ L, (∀ l ∈ L, ⁅l, g⁆ ∈ O) → g ∈ O := l93_three_S1 hp hZ
  have hS2 := l93_three_S2 h.norm hBO hinner
  have hCO : O ≤ C := by
    intro o ho
    refine mem_centModSubgroup.2 ⟨Subgroup.le_normalizer (hOL ho), fun l hl => ?_⟩
    have h1 : l * o * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hLN hl) o).1 ho
    rw [commutatorElement_def]
    exact O.mul_mem h1 (O.inv_mem ho)
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := fun c hc' => (mem_centModSubgroup.1 hc').1
  have hLC : L ⊓ C ≤ O := fun g hg =>
    hS1 g (Subgroup.mem_inf.1 hg).1 (mem_centModSubgroup.1 (Subgroup.mem_inf.1 hg).2).2
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := l93_B_le_normalizer_C h.norm
  set R : Subgroup G := L ⊓ (B ⊔ C) with hRdef
  have hRL : R ≤ L := inf_le_left
  have hRBC : R ≤ B ⊔ C := inf_le_right
  have hOR : O ≤ R := le_inf hOL (hCO.trans le_sup_right)
  have hCRB : C ⊔ R = C ⊔ B := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      intro r hr
      have hr' := hRBC hr
      rw [sup_comm] at hr'
      exact hr'
    · refine sup_le le_sup_left ?_
      intro b hb
      obtain ⟨c, hc', l, hl, hbcl⟩ := hS2 b hb
      have hlR : l ∈ R := by
        refine Subgroup.mem_inf.2 ⟨hl, ?_⟩
        have hl' : l = c⁻¹ * b := by rw [hbcl]; group
        rw [hl']
        exact (B ⊔ C).mul_mem (Subgroup.mem_sup_right (C.inv_mem hc')) (Subgroup.mem_sup_left hb)
      rw [hbcl]
      exact Subgroup.mul_mem_sup hc' hlR
  have hCRinf : C ⊓ R = O := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgC, hgR⟩ := Subgroup.mem_inf.1 hg
      exact hLC (Subgroup.mem_inf.2 ⟨hRL hgR, hgC⟩)
    · exact le_inf hCO hOR
  have hBCN : B ⊔ C ≤ Subgroup.normalizer (C : Set G) := sup_le hBC Subgroup.le_normalizer
  have hRN : R ≤ Subgroup.normalizer (C : Set G) := hRBC.trans hBCN
  have hid1 := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := R) hRN
  rw [hCRB, hCRinf] at hid1
  have hid2 := card_sup_mul_card_inf_of_le_normalizer (A := C) (B := B) hBC
  have hCB : C ⊓ B = Subgroup.zpowers x := by
    rw [inf_comm]
    exact H92.inf_centMod_eq h
  have hxp : x ^ p = 1 := hBexp x h.mem
  have hxord : orderOf x = p := orderOf_eq_prime hxp h.ne_one
  have hcard_x : Nat.card (C ⊓ B : Subgroup G) = p := by
    rw [hCB, Nat.card_zpowers, hxord]
  rw [hcard_x] at hid2
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hRp : Nat.card R * p = Nat.card B * Nat.card O := by
    apply Nat.eq_of_mul_eq_mul_left hCpos
    calc Nat.card C * (Nat.card R * p) = (Nat.card C * Nat.card R) * p := by ring
      _ = (Nat.card ↥(C ⊔ B) * Nat.card O) * p := by rw [hid1]
      _ = (Nat.card ↥(C ⊔ B) * p) * Nat.card O := by ring
      _ = Nat.card C * Nat.card B * Nat.card O := by rw [hid2]
      _ = Nat.card C * (Nat.card B * Nat.card O) := by ring
  have hconjR : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hcC r hrR
    have hrc : ⁅r, c⁆ ∈ O := (mem_centModSubgroup.1 hcC).2 r (hRL hrR)
    have e : c * r * c⁻¹ = (⁅r, c⁆)⁻¹ * r := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact R.mul_mem (hOR (O.inv_mem hrc)) hrR
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    have haC : a ∈ C := (hAC ha).2
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    constructor
    · exact hconjR a haC h'
    · intro hh
      have h2 := hconjR a⁻¹ (C.inv_mem haC) _ hh
      have e : a⁻¹ * (a * h' * a⁻¹) * a⁻¹⁻¹ = h' := by group
      rw [e] at h2
      exact h2
  have hAR : R ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgR, hgA⟩ := Subgroup.mem_inf.1 hg
    have hgO : g ∈ O := hLC (Subgroup.mem_inf.2 ⟨hRL hgR, (hAC hgA).2⟩)
    have hAO : A ⊓ O = ⊥ := l93_inter_eq_bot hp hAp hcopO
    have h2 : g ∈ A ⊓ O := Subgroup.mem_inf.2 ⟨hgA, hgO⟩
    rw [hAO] at h2
    exact h2
  have hid3 := card_sup_mul_card_inf_of_le_normalizer (A := R) (B := A) hAN
  rw [hAR, Subgroup.card_bot, mul_one] at hid3
  set Y : Subgroup G := R ⊔ A with hYdef
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hRL.trans Subgroup.le_normalizer) (fun a ha => hCN (hAC ha).2)
  have hYN : Y ≤ Subgroup.normalizer (O : Set G) := hYL.trans hNO
  have hOY : O ≤ Y := hOR.trans le_sup_left
  have hYC : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (hRL.trans h.comp.1) (fun a ha => (hAC ha).1)
  set S : Set G := (R : Set G) ∪ (A : Set G) with hSdef
  have hY : Subgroup.closure S = Y := (Subgroup.sup_eq_closure R A).symm
  have hSc : ∀ g ∈ S, ∀ h' ∈ S, ⁅g, h'⁆ ∈ O := by
    intro g hg h' hh
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · have hcC := (l93_mod h.norm hBab hBexp g (hRBC hg) h' (hRBC hh)).1
      have hLcomm : ⁅g, h'⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem (hRL hg) (hRL hh)) (L.inv_mem (hRL hg)))
          (L.inv_mem (hRL hh))
      exact hS1 _ hLcomm (fun l hl => (mem_centModSubgroup.1 hcC).2 l hl)
    · exact (mem_centModSubgroup.1 (hAC hh).2).2 g (hRL hg)
    · have hcm : ⁅h', g⁆ ∈ O := (mem_centModSubgroup.1 (hAC hg).2).2 h' (hRL hh)
      have e : ⁅g, h'⁆ = (⁅h', g⁆)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact O.inv_mem hcm
    · have hcomm' : g * h' = h' * g := isElemAbelian_commute hAel hg hh
      have h1 : ⁅g, h'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm'
      rw [h1]
      exact O.one_mem
  have hSp : ∀ g ∈ S, g ^ p ∈ O := by
    intro g hg
    rcases hg with hg | hg
    · have hpC := (l93_mod h.norm hBab hBexp g (hRBC hg) g (hRBC hg)).2
      exact hS1 _ (L.pow_mem (hRL hg) p) (fun l hl => (mem_centModSubgroup.1 hpC).2 l hl)
    · rw [hAel.2 g hg]
      exact O.one_mem
  obtain ⟨hcomm, hpow⟩ := l93_closure hY hOY hYN hSc hSp
  have hYcard : Nat.card Y = Nat.card R * Nat.card A := hid3
  have hYp : Nat.card Y * p = p ^ (mB + a) * Nat.card O := by
    calc Nat.card Y * p = (Nat.card R * p) * Nat.card A := by rw [hYcard]; ring
      _ = (Nat.card B * Nat.card O) * Nat.card A := by rw [hRp]
      _ = p ^ (mB + a) * Nat.card O := by rw [hmB, ha, pow_add]; ring
  have hdvd : p ^ (mB + 1) ∣ Nat.card Y := by
    have h2 : p ^ (mB + 1) * p ∣ Nat.card Y * p := by
      rw [hYp, ← pow_succ]
      exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  set S₀ : Subgroup G := K.map Y.subtype with hS₀
  have hS₀card : Nat.card S₀ = p ^ (mB + 1) := by
    rw [hS₀, Subgroup.card_map_of_injective Y.subtype_injective, hK]
  have hS₀Y : S₀ ≤ Y := Subgroup.map_subtype_le K
  have hS₀p : IsPGroup p S₀ := IsPGroup.iff_card.2 ⟨mB + 1, hS₀card⟩
  have hS₀O : S₀ ⊓ O = ⊥ := l93_inter_eq_bot hp hS₀p hcopO
  have hS₀el : IsElemAbelian p S₀ := by
    refine ⟨⟨⟨fun s t => Subtype.ext ?_⟩⟩, fun s hs => ?_⟩
    · have hc1 : ⁅(s : G), (t : G)⁆ ∈ O := hcomm _ (hS₀Y s.2) _ (hS₀Y t.2)
      have hc2 : ⁅(s : G), (t : G)⁆ ∈ S₀ := by
        rw [commutatorElement_def]
        exact S₀.mul_mem (S₀.mul_mem (S₀.mul_mem s.2 t.2) (S₀.inv_mem s.2)) (S₀.inv_mem t.2)
      have h1 : ⁅(s : G), (t : G)⁆ = 1 := by
        have h3 : ⁅(s : G), (t : G)⁆ ∈ S₀ ⊓ O := Subgroup.mem_inf.2 ⟨hc2, hc1⟩
        rw [hS₀O] at h3
        exact (Subgroup.mem_bot.1 h3)
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    · have hp1 : s ^ p ∈ O := hpow s (hS₀Y hs)
      have hp2 : s ^ p ∈ S₀ := S₀.pow_mem hs p
      have h3 : s ^ p ∈ S₀ ⊓ O := Subgroup.mem_inf.2 ⟨hp2, hp1⟩
      rw [hS₀O] at h3
      exact Subgroup.mem_bot.1 h3
  have hS₀Cx : S₀ ≤ Subgroup.centralizer ({x} : Set G) := hS₀Y.trans hYC
  have hle := hmax S₀ hS₀Cx hS₀el
  rw [hS₀card, hmB] at hle
  have hlt : p ^ mB < p ^ (mB + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self mB)
  exact absurd hle (not_le.2 hlt)

theorem l93_exists_invariant_elemAbelian_of_noncyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B P : Subgroup G} {x : G} (hB : IsElemAbelian p B) (hP : IsPGroup p P)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hxP : x ∈ P) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxc : P ≤ Subgroup.centralizer ({x} : Set G))
    (hxB : B ≤ Subgroup.centralizer ({x} : Set G)) (hnc : ¬ IsCyclic P) :
    ∃ U : Subgroup G, U ≤ P ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧ x ∈ U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hTN : P ⊔ B ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hBP
  have hTp : IsPGroup p ↥(P ⊔ B : Subgroup G) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hB)
    have hd1 : Nat.card (P ⊓ B : Subgroup G) ∣ p ^ a := ha ▸ Subgroup.card_dvd_of_le (inf_le_left : P ⊓ B ≤ P)
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 hd1
    have hid := card_sup_mul_card_inf_of_le_normalizer hBP
    have h2 : Nat.card (P ⊔ B : Subgroup G) * p ^ c = p ^ (a + b) := by
      rw [← hc, hid, ha, hb, pow_add]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h2)
    exact IsPGroup.iff_card.2 ⟨i, hi⟩
  obtain ⟨V, hVP, hVT, hVcard, hVexp, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2 hTp le_sup_left hTN hnc
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hVT
  have hVel : IsElemAbelian p V :=
    ⟨⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩, fun a ha => hVexp a ha⟩
  by_cases hxV : x ∈ V
  · exact ⟨V, hVP, hVel, hVcard, hxV, hBV⟩
  letI : MulDistribMulAction ↥B ↥V := Subgroup.conjMulDistribMulActionOfLeNormalizer B V hBV
  have hsmul : ∀ (a : ↥B) (k : ↥V), ((a • k : ↥V) : G) = (a : G) * (k : G) * (a : G)⁻¹ :=
    fun a k => rfl
  have hBp : IsPGroup p ↥B := isPGroup_of_isElemAbelian hB
  have hmod := hBp.card_modEq_card_fixedPoints ↥V
  rw [hVcard] at hmod
  have h1mem : (1 : ↥V) ∈ MulAction.fixedPoints ↥B ↥V := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    rw [hsmul]
    simp
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints ↥B ↥V) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 (dvd_pow_self p two_ne_zero)))
  have hpos : 0 < Nat.card (MulAction.fixedPoints ↥B ↥V) := by
    haveI : Nonempty (MulAction.fixedPoints ↥B ↥V) := ⟨⟨1, h1mem⟩⟩
    exact Nat.card_pos
  have hge : p ≤ Nat.card (MulAction.fixedPoints ↥B ↥V) := Nat.le_of_dvd hpos hdvd
  have hnt : 1 < Nat.card (MulAction.fixedPoints ↥B ↥V) := lt_of_lt_of_le hp.one_lt hge
  haveI : Nontrivial (MulAction.fixedPoints ↥B ↥V) := (Finite.one_lt_card_iff_nontrivial).1 hnt
  obtain ⟨y, hy⟩ := exists_ne (⟨1, h1mem⟩ : MulAction.fixedPoints ↥B ↥V)
  have hu1 : ((y : ↥V) : G) ≠ 1 := by
    intro h
    apply hy
    apply Subtype.ext
    exact Subtype.ext h
  have hufix : ∀ b ∈ B, b * ((y : ↥V) : G) * b⁻¹ = ((y : ↥V) : G) := by
    intro b hb
    have h2 := congrArg Subtype.val (MulAction.mem_fixedPoints.1 y.2 ⟨b, hb⟩)
    rw [hsmul] at h2
    exact h2
  set u : G := ((y : ↥V) : G) with hu_def
  have huV : u ∈ V := (y : ↥V).2
  have hup : u ^ p = 1 := hVexp u huV
  have hu1' : u ≠ 1 := hu1
  have hxu : Commute x u := by
    have hc : u ∈ Subgroup.centralizer ({x} : Set G) := hxc (hVP huV)
    exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  have hord_x : orderOf x = p := orderOf_eq_prime hxp hx1
  have hord_u : orderOf u = p := orderOf_eq_prime hup hu1'
  have hcx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hord_x]
  have hcu : Nat.card (Subgroup.zpowers u) = p := by rw [Nat.card_zpowers, hord_u]
  have hzu_le : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    refine Subgroup.zpowers_le.2 ?_
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hxu.zpow_left k).eq
  have hzinf : Subgroup.zpowers x ⊓ Subgroup.zpowers u = ⊥ := by
    by_contra hne
    have hdvd' : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers u : Subgroup G) ∣ p :=
      hcx ▸ Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers x)
    rcases (Nat.dvd_prime hp).1 hdvd' with h1 | hpK
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers u = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcx, hpK])
      have hxinf : x ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers u := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      have hxzu : x ∈ Subgroup.zpowers u :=
        (inf_le_right : Subgroup.zpowers x ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers u) hxinf
      exact hxV ((Subgroup.zpowers_le.2 huV) hxzu)
  have hid := card_sup_mul_card_inf_of_le_normalizer hzu_le
  rw [hzinf, Subgroup.card_bot, hcx, hcu, mul_one] at hid
  have hUeq : Subgroup.closure ({x, u} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers u := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hpair : Set.Pairwise ({x, u} : Set G) Commute :=
    Set.pairwise_pair.2 (fun _ => ⟨hxu, hxu.symm⟩)
  haveI hUcomm : IsMulCommutative (Subgroup.closure ({x, u} : Set G)) :=
    Subgroup.isMulCommutative_closure hpair
  have hUcomm' : ∀ g ∈ Subgroup.closure ({x, u} : Set G), ∀ h ∈ Subgroup.closure ({x, u} : Set G),
      Commute g h := fun g hg h hh =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨g, hg⟩ : Subgroup.closure ({x, u} : Set G)) ⟨h, hh⟩)
  have hUexp : ∀ g ∈ Subgroup.closure ({x, u} : Set G), g ^ p = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hxp
      · exact hup
    | one => exact one_pow p
    | mul g h hg hh ihg ihh =>
      rw [(hUcomm' g hg h hh).mul_pow, ihg, ihh, one_mul]
    | inv g hg ih =>
      rw [inv_pow, ih, inv_one]
  have hBU : B ≤ Subgroup.normalizer (Subgroup.closure ({x, u} : Set G) : Set G) := by
    intro b hb
    have hbx : b * x = x * b := Subgroup.mem_centralizer_singleton_iff.1 (hxB hb)
    have hbu : b * u = u * b := by
      have h := hufix b hb
      calc b * u = b * u * b⁻¹ * b := by group
        _ = u * b := by rw [h]
    have hsub : Subgroup.closure ({x, u} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2 hbx.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 hbu.symm
    have hbc : b ∈ Subgroup.centralizer (Subgroup.closure ({x, u} : Set G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hsub hg))
    exact Subgroup.centralizer_le_normalizer _ hbc
  refine ⟨Subgroup.closure ({x, u} : Set G), ?_, ⟨hUcomm, fun g hg => hUexp g hg⟩, ?_, ?_, hBU⟩
  · refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hxP
    · exact hVP huV
  · rw [hUeq, hid, sq]
  · exact Subgroup.subset_closure (by simp)

end CFSG.LocalAnalysis.GLTheoremA.S9

end
