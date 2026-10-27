module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsLines
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveSylow

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.Asc75Lemma31

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G]

structure IsVprime (V V₀ P V' : Subgroup G) : Prop where
  le : V' ≤ P
  elem : IsElemAbelian 2 V'
  card : Nat.card V' = 16
  inf : V ⊓ V' = V₀
  sup : V ⊔ V' = P
  inv : ∀ x ∈ P, x * x = 1 → x ∉ V → x ∈ V'

structure OuterInvol (R T V₀ P : Subgroup G) (x z r₁ : G) : Prop where
  sq : x * x = 1
  not_mem : x ∉ P
  normV : x ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)
  normP : x ∈ normalizer (P : Set G)
  normR : x ∈ normalizer (R : Set G)
  z_mem : z ∈ V₀
  z_ne : z ≠ 1
  z_comm : x * z = z * x
  fix_V₀ : ∀ w ∈ V₀, x * w = w * x → w = 1 ∨ w = z
  r_mem : r₁ ∈ R
  r_ne : r₁ ≠ 1
  r_comm : x * r₁ = r₁ * x
  fix_R : ∀ r ∈ R, x * r = r * x → r = 1 ∨ r = r₁
  move : ∃ p ∈ P, p⁻¹ * (x * p * x⁻¹) ∉ R ⊔ T

namespace Setting310

variable [Finite G] {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

theorem exists_isVprime
    (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) :
    ∃ V' : Subgroup G, IsVprime (R ⊔ T) V₀ P V' := by
  obtain ⟨V', hV'P, hV'e, hV'16, hinf, hsup, hV'inv, -⟩ := h.exists_Vprime hP hPC hIIa hP64 hVP
  exact ⟨V', ⟨hV'P, hV'e, hV'16, hinf, hsup, hV'inv⟩⟩

omit hP hPC in
theorem card_inf_centralizer_V_le {u : G} (huR : u ∈ normalizer (R : Set G))
    (huV₀ : u ∈ normalizer (V₀ : Set G)) {r₁ z : G} (hr₁ : r₁ ∈ R) (hz : z ∈ V₀)
    (hfixR : ∀ r ∈ R, u * r = r * u → r = 1 ∨ r = r₁)
    (hfixV₀ : ∀ w ∈ V₀, u * w = w * u → w = 1 ∨ w = z) :
    Nat.card ((R ⊔ T) ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ 4 := by
  have hle : (R ⊔ T) ⊓ centralizer ({u} : Set G) ≤ zpowers r₁ ⊔ zpowers z := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := mem_inf.mp hv
    have hvu : u * v = v * u := (mem_centralizer_singleton_iff.mp hvC).symm
    obtain ⟨r, hr, w, hw, rfl⟩ := h.exists_mul hvV
    have hru : u * r * u⁻¹ ∈ R := (mem_normalizer_iff.mp huR r).mp hr
    have hwu : u * w * u⁻¹ ∈ V₀ := (mem_normalizer_iff.mp huV₀ w).mp hw
    have h1 : r⁻¹ * (u * r * u⁻¹) = w * (u * w * u⁻¹)⁻¹ := by
      have h2 : (u * r * u⁻¹) * (u * w * u⁻¹) = r * w := by
        calc (u * r * u⁻¹) * (u * w * u⁻¹) = u * (r * w) * u⁻¹ := by group
          _ = r * w := by rw [hvu]; group
      calc r⁻¹ * (u * r * u⁻¹) = r⁻¹ * ((u * r * u⁻¹) * (u * w * u⁻¹)) * (u * w * u⁻¹)⁻¹ := by
            group
        _ = r⁻¹ * (r * w) * (u * w * u⁻¹)⁻¹ := by rw [h2]
        _ = w * (u * w * u⁻¹)⁻¹ := by group
    have h3 : r⁻¹ * (u * r * u⁻¹) ∈ R ⊓ V₀ :=
      mem_inf.mpr ⟨mul_mem (inv_mem hr) hru, h1 ▸ mul_mem hw (inv_mem hwu)⟩
    rw [h.inf_R_V₀, mem_bot] at h3
    have hrfix : u * r = r * u := by
      have : u * r * u⁻¹ = r := by
        calc u * r * u⁻¹ = r * (r⁻¹ * (u * r * u⁻¹)) := by group
          _ = r := by rw [h3, mul_one]
      calc u * r = u * r * u⁻¹ * u := by group
        _ = r * u := by rw [this]
    have hwfix : u * w = w * u := by
      have h4 : w * (u * w * u⁻¹)⁻¹ = 1 := by rw [← h1, h3]
      have : u * w * u⁻¹ = w := by
        calc u * w * u⁻¹ = (w * (u * w * u⁻¹)⁻¹)⁻¹ * w := by group
          _ = w := by rw [h4, inv_one, one_mul]
      calc u * w = u * w * u⁻¹ * u := by group
        _ = w * u := by rw [this]
    refine mul_mem ?_ ?_
    · rcases hfixR r hr hrfix with rfl | rfl
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers _)
    · rcases hfixV₀ w hw hwfix with rfl | rfl
      · exact one_mem _
      · exact mem_sup_right (mem_zpowers _)
  have h1 := card_le_of_le hle
  have hz2 : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact h.mul_self (h.V₀_le hz))
  have hr2 : Nat.card (zpowers r₁) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact h.mul_self (mem_sup_left hr₁))
  have hc : r₁ * z = z * r₁ := h.comm (mem_sup_left hr₁) (h.V₀_le hz)
  have hrc : r₁ ∈ centralizer (zpowers z : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((show Commute r₁ z from hc).symm.zpow_left k).eq
  have hN : zpowers r₁ ≤ normalizer (zpowers z : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hrc)
  have h2 := card_sup_mul_card_inf_of_le hN
  have h3 : 0 < Nat.card (zpowers r₁ ⊓ zpowers z : Subgroup G) := Nat.card_pos
  have h4 : Nat.card (zpowers r₁ ⊔ zpowers z : Subgroup G) ≤ 4 := by
    have h5 : Nat.card (zpowers r₁ ⊔ zpowers z : Subgroup G) * 1 ≤ 2 * 2 := by
      calc Nat.card (zpowers r₁ ⊔ zpowers z : Subgroup G) * 1 ≤
          Nat.card (zpowers r₁ ⊔ zpowers z : Subgroup G) *
            Nat.card (zpowers r₁ ⊓ zpowers z : Subgroup G) := Nat.mul_le_mul_left _ h3
        _ = Nat.card (zpowers r₁) * Nat.card (zpowers z) := h2
        _ ≤ 2 * 2 := Nat.mul_le_mul hr2 hz2
    omega
  omega

theorem exists_outerInvol (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P)
    (hε : ¬ EpsOne (R ⊔ T) P) : ∃ x z r₁ : G, OuterInvol R T V₀ P x z r₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hV₀2 : ∀ x ∈ V₀, x * x = 1 := fun x hx => h.mul_self (h.V₀_le hx)
  have hPV : P ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun n hn => (hP.le hn).1
  obtain ⟨Q₀, hQ₀, hPQ₀⟩ := exists_isSylowOf_le hPV hP.isPGroup
  have hPQ₀' : P < Q₀ := lt_of_le_of_ne hPQ₀ fun he => hε (by
    change IsSylowOf 2 P _
    rw [he]
    exact hQ₀)
  have hQ₁ := lt_inf_normalizer hQ₀.isPGroup hPQ₀'
  obtain ⟨σ, hσ, hσP⟩ := IsConcreteLE.exists_of_lt hQ₁
  obtain ⟨hσQ, hσN⟩ := mem_inf.mp hσ
  obtain ⟨p, hp, hσp⟩ := h.exists_mul_mem_normalizer_R hP hPC hP64 (hQ₀.le hσQ)
  set σ' := σ * p with hσ'
  have hσ'Q : σ' ∈ Q₀ := mul_mem hσQ (hPQ₀ hp)
  have hσ'N : σ' ∈ normalizer (P : Set G) := mul_mem hσN (le_normalizer hp)
  have hσ'P : σ' ∉ P := fun he => hσP (by
    have := mul_mem he (inv_mem hp)
    simpa [hσ'] using this)
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQ₀.isPGroup ⟨σ', hσ'Q⟩
  rw [Subgroup.orderOf_mk] at ha
  have hex : ∃ k : ℕ, σ' ^ (2 ^ k) ∈ R ⊔ T :=
    ⟨a, by rw [← ha, pow_orderOf_eq_one]; exact one_mem _⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀V : σ' ^ (2 ^ k₀) ∈ R ⊔ T := Nat.find_spec hex
  have hk₀0 : k₀ ≠ 0 := by
    intro he
    rw [he, pow_zero, pow_one] at hk₀V
    exact hσ'P (hVP hk₀V)
  set σ₂ := σ' ^ (2 ^ (k₀ - 1)) with hσ₂
  have hσ₂V : σ₂ ∉ R ⊔ T := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk₀0) one_pos)
  have hσ₂sq : σ₂ * σ₂ ∈ R ⊔ T := by
    have e : σ₂ * σ₂ = σ' ^ (2 ^ k₀) := by
      rw [hσ₂, ← pow_add, ← two_mul, ← pow_succ']
      congr 2
      omega
    rw [e]
    exact hk₀V
  have hσ₂Q : σ₂ ∈ Q₀ := pow_mem hσ'Q _
  have hσ₂V' : σ₂ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := hQ₀.le hσ₂Q
  have hσ₂R : σ₂ ∈ normalizer (R : Set G) := pow_mem hσp _
  have hσ₂N : σ₂ ∈ normalizer (P : Set G) := pow_mem hσ'N _
  have hσ₂V₀ : σ₂ ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hσ₂V'
  have hσ₂P : σ₂ ∉ P := by
    intro he
    apply hσ₂V
    rw [← h.inf_normalizer_R_eq hP hPC]
    exact mem_inf.mpr ⟨he, hσ₂R⟩
  have hσ₂2 : IsPGroup 2 (zpowers σ₂) := hQ₀.isPGroup.to_le (zpowers_le.mpr hσ₂Q)
  have hVC : R ⊔ T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    le_centralizer_self_of_isElemAbelian h.loc.elem
  have hnotC : σ₂ ∉ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
    intro hC
    apply hσ₂V
    have hX : (R ⊔ T) ⊔ zpowers σ₂ = R ⊔ T :=
      h.eq_of_le_centralizer le_sup_left (sup_le hVC (zpowers_le.mpr hC))
        (hQ₀.isPGroup.to_le (sup_le (hVP.trans hPQ₀) (zpowers_le.mpr hσ₂Q)))
    rw [← hX]
    exact mem_sup_right (mem_zpowers _)
  have hnotV₀ : σ₂ ∉ centralizer (V₀ : Set G) := fun hC =>
    hnotC (h.mem_centralizer_of_mem_centralizer_V₀ hσ₂V' hσ₂R hσ₂2 hC)
  have hnotR : σ₂ ∉ centralizer (R : Set G) := fun hC =>
    hnotC (h.mem_centralizer_of_mem_centralizer_R hσ₂V' hσ₂2 hC)
  have hσ₂sqV₀ : σ₂ * σ₂ ∈ centralizer (V₀ : Set G) :=
    centralizer_le (fun v hv => h.V₀_le hv) (hVC hσ₂sq)
  have hσ₂sqR : σ₂ * σ₂ ∈ centralizer (R : Set G) :=
    centralizer_le (fun v hv => mem_sup_left hv) (hVC hσ₂sq)
  have hV₀e : IsElemAbelian 2 V₀ := isElemAbelian_of_le h.loc.elem h.V₀_le
  have hcV₀ := card_inf_centralizer_of_card_four hV₀e h.card_V₀ hσ₂V₀ hσ₂sqV₀ hnotV₀
  have hcR := card_inf_centralizer_of_card_four h.elemR h.cardR hσ₂R hσ₂sqR hnotR
  have hV₀C : (V₀ ⊓ centralizer ({σ₂} : Set G) : Subgroup G) ≠ ⊥ := fun he => by
    rw [he, card_bot] at hcV₀; omega
  have hRC : (R ⊓ centralizer ({σ₂} : Set G) : Subgroup G) ≠ ⊥ := fun he => by
    rw [he, card_bot] at hcR; omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀C
  obtain ⟨⟨r₁, hr₁⟩, hr₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRC
  have hz1' : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hr₁1' : (r₁ : G) ≠ 1 := fun he => hr₁1 (Subtype.ext he)
  have hfixV₀ : ∀ w ∈ V₀, σ₂ * w = w * σ₂ → w = 1 ∨ w = z := fun w hw hwc =>
    eq_one_or_eq_of_card_eq_two hcV₀ hz hz1'
      (mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr hwc.symm⟩)
  have hfixR : ∀ r ∈ R, σ₂ * r = r * σ₂ → r = 1 ∨ r = r₁ := fun r hr hrc =>
    eq_one_or_eq_of_card_eq_two hcR hr₁ hr₁1'
      (mem_inf.mpr ⟨hr, mem_centralizer_singleton_iff.mpr hrc.symm⟩)
  have hcV := h.card_inf_centralizer_V_le hσ₂R hσ₂V₀ (mem_inf.mp hr₁).1 (mem_inf.mp hz).1
    hfixR hfixV₀
  have hsq : Nat.card ((R ⊔ T) ⊓ centralizer ({σ₂} : Set G) : Subgroup G) ^ 2 ≤
      Nat.card (R ⊔ T : Subgroup G) := by
    rw [h.loc.card, sq]
    exact (Nat.mul_le_mul hcV hcV).trans (by norm_num)
  obtain ⟨e, he, hee⟩ := exists_conj_eq_mul_of_sq_le h.loc.elem hσ₂V' (hVC hσ₂sq) hsq
    (inv_mem hσ₂sq) (by group)
  have he2 : e * e = 1 := h.mul_self he
  set x := σ₂ * e with hx
  have hxsq : x * x = 1 := by
    have h1 : σ₂ * e = e * σ₂⁻¹ := by
      have h2 : e⁻¹ * σ₂ * e = σ₂⁻¹ := by rw [hee]; group
      calc σ₂ * e = e * (e⁻¹ * σ₂ * e) := by group
        _ = e * σ₂⁻¹ := by rw [h2]
    calc x * x = σ₂ * e * (σ₂ * e) := rfl
      _ = e * σ₂⁻¹ * (σ₂ * e) := by rw [h1]
      _ = e * e := by group
      _ = 1 := he2
  have heC : e ∈ centralizer ((R ⊔ T : Subgroup G) : Set G) := hVC he
  have hxact : ∀ v ∈ R ⊔ T, x * v * x⁻¹ = σ₂ * v * σ₂⁻¹ := fun v hv => by
    have : e * v * e⁻¹ = v := by rw [← mem_centralizer_iff.mp heC v hv]; group
    calc x * v * x⁻¹ = σ₂ * (e * v * e⁻¹) * σ₂⁻¹ := by rw [hx]; group
      _ = σ₂ * v * σ₂⁻¹ := by rw [this]
  have hxcomm : ∀ v ∈ R ⊔ T, (x * v = v * x ↔ σ₂ * v = v * σ₂) := fun v hv => by
    constructor
    · intro h1
      have h2 : σ₂ * v * σ₂⁻¹ = v := by rw [← hxact v hv, h1]; group
      calc σ₂ * v = σ₂ * v * σ₂⁻¹ * σ₂ := by group
        _ = v * σ₂ := by rw [h2]
    · intro h1
      have h2 : x * v * x⁻¹ = v := by rw [hxact v hv, h1]; group
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h2]
  refine ⟨x, z, r₁, ⟨hxsq, ?_, mul_mem hσ₂V' (le_normalizer he), mul_mem hσ₂N
    (le_normalizer (hVP he)), mul_mem hσ₂R (centralizer_le_normalizer _
      (centralizer_le (fun v hv => mem_sup_left hv) heC)), (mem_inf.mp hz).1, hz1', ?_, ?_,
    (mem_inf.mp hr₁).1, hr₁1', ?_, ?_, ?_⟩⟩
  · intro hxP
    apply hσ₂P
    have := mul_mem hxP (inv_mem (hVP he))
    simpa [hx] using this
  · exact (hxcomm z (h.V₀_le (mem_inf.mp hz).1)).mpr
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2).symm
  · intro w hw hwc
    exact hfixV₀ w hw ((hxcomm w (h.V₀_le hw)).mp hwc)
  · exact (hxcomm r₁ (mem_sup_left (mem_inf.mp hr₁).1)).mpr
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hr₁).2).symm
  · intro r hr hrc
    exact hfixR r hr ((hxcomm r (mem_sup_left hr)).mp hrc)
  ·
    by_contra hall
    push Not at hall
    obtain ⟨w, hw, hw1, hwz⟩ := exists_ne_one_ne h.card_V₀ hV₀2 (mem_inf.mp hz).1
    obtain ⟨q, hq, hqw⟩ := h.exists_mem_P_transvHom hP hPC hP64 (mem_inf.mp hr₁).1 hr₁1' hw
    have hxr : x * r₁ = r₁ * x := (hxcomm r₁ (mem_sup_left (mem_inf.mp hr₁).1)).mpr
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hr₁).2).symm
    obtain ⟨v, hv, hqv⟩ : ∃ v ∈ R ⊔ T, x * q * x⁻¹ = q * v :=
      ⟨q⁻¹ * (x * q * x⁻¹), hall q hq, by group⟩
    have hvr : v * (r₁ : G) = r₁ * v := h.comm hv (mem_sup_left (mem_inf.mp hr₁).1)
    have hxw : x * w * x⁻¹ = w := by
      rw [← hqw]
      calc x * ((r₁ : G)⁻¹ * (q * r₁ * q⁻¹)) * x⁻¹ =
          (x * (r₁ : G) * x⁻¹)⁻¹ * ((x * q * x⁻¹) * (x * r₁ * x⁻¹) * (x * q * x⁻¹)⁻¹) := by
            group
        _ = (r₁ : G)⁻¹ * ((q * v) * r₁ * (q * v)⁻¹) := by
            rw [hqv, show x * (r₁ : G) * x⁻¹ = r₁ by rw [hxr]; group]
        _ = (r₁ : G)⁻¹ * (q * (v * r₁ * v⁻¹) * q⁻¹) := by group
        _ = (r₁ : G)⁻¹ * (q * r₁ * q⁻¹) := by rw [hvr]; group
    have hwc : x * w = w * x := by
      calc x * w = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [hxw]
    have := hfixV₀ w hw ((hxcomm w (h.V₀_le hw)).mp hwc)
    rcases this with h1 | h1
    · exact hw1 h1
    · exact hwz h1

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

omit [Finite G] h hP hPC in
theorem outer_inv : x⁻¹ = x := by
  calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx.sq, mul_one]
    _ = x := by group

omit [Finite G] h hPC in
theorem outer_conj_V₀ {u : G} (hu : x * u ∈ P) {w : G} (hw : w ∈ V₀) :
    u * w * u⁻¹ = x * w * x⁻¹ := by
  have hu' : u = x * (x * u) := by
    rw [← mul_assoc, hx.sq, one_mul]
  have hpw : (x * u) * w * (x * u)⁻¹ = w := by
    rw [← mem_centralizer_iff.mp (hP.le hu).2.1 w hw]
    group
  calc u * w * u⁻¹ = x * ((x * u) * w * (x * u)⁻¹) * x⁻¹ := by
        conv_lhs => rw [hu']
        group
    _ = x * w * x⁻¹ := by rw [hpw]

omit hP hPC in
theorem outer_not_mem_centralizer_V₀ : x ∉ centralizer (V₀ : Set G) := by
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  obtain ⟨w, hw, hw1, hwz⟩ := exists_ne_one_ne h.card_V₀ hV₀2 hx.z_mem
  intro hC
  rcases hx.fix_V₀ w hw (mem_centralizer_iff.mp hC w hw).symm with h1 | h1
  · exact hw1 h1
  · exact hwz h1

omit hP hPC in
theorem outer_card_inf_centralizer_V₀ {u : G} (hu : ∀ w ∈ V₀, u * w * u⁻¹ = x * w * x⁻¹) :
    Nat.card (V₀ ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ 2 := by
  have hle : V₀ ⊓ centralizer ({u} : Set G) ≤ zpowers z := by
    intro w hw
    obtain ⟨hwV, hwC⟩ := mem_inf.mp hw
    have hwu : u * w = w * u := (mem_centralizer_singleton_iff.mp hwC).symm
    have hwx : x * w = w * x := by
      have h1 : x * w * x⁻¹ = w := by rw [← hu w hwV, hwu]; group
      calc x * w = x * w * x⁻¹ * x := by group
        _ = w * x := by rw [h1]
    rcases hx.fix_V₀ w hwV hwx with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  calc Nat.card (V₀ ⊓ centralizer ({u} : Set G) : Subgroup G) ≤ Nat.card (zpowers z) :=
        card_le_of_le hle
    _ ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact h.mul_self (h.V₀_le hx.z_mem))

theorem outer_card_le_four_V {u : G} (hu : x * u ∈ P) {X : Subgroup G} (hXV : X ≤ R ⊔ T)
    (hXC : X ≤ centralizer ({u} : Set G)) : Nat.card X ≤ 4 := by
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  by_contra hX4
  push Not at hX4
  have hdvd : Nat.card X ∣ 16 := h.loc.card ▸ card_dvd_of_le hXV
  have hXV₀ : Nat.card (X ⊓ V₀ : Subgroup G) ≤ 2 := by
    have hle : X ⊓ V₀ ≤ V₀ ⊓ centralizer ({u} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hXC)
    exact (card_le_of_le hle).trans
      (h.outer_card_inf_centralizer_V₀ hx fun w hw => outer_conj_V₀ hP hx hu hw)
  have hV₀N : V₀ ≤ normalizer (X : Set G) := le_normalizer_of_le h.loc.elem hXV h.V₀_le
  have hc := card_sup_mul_card_inf_of_le hV₀N
  rw [h.card_V₀, inf_comm] at hc
  have hsupV : V₀ ⊔ X ≤ R ⊔ T := sup_le h.V₀_le hXV
  have hsup16 := card_le_of_le hsupV
  rw [h.loc.card] at hsup16
  have hX8 : 8 ≤ Nat.card X := by
    have h1 : Nat.card X ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h2 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h2] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hpos : 0 < Nat.card (X ⊓ V₀ : Subgroup G) := Nat.card_pos
  have hsupeq : V₀ ⊔ X = R ⊔ T := by
    apply eq_of_le_of_card_ge hsupV
    rw [h.loc.card]
    nlinarith
  obtain ⟨r, hr, hr1, hrr₁⟩ := exists_ne_one_ne h.cardR hR2 hx.r_mem
  have hXN : X ≤ normalizer (V₀ : Set G) := le_normalizer_of_le h.loc.elem h.V₀_le hXV
  have hrV : r ∈ X ⊔ V₀ := by rw [sup_comm, hsupeq]; exact mem_sup_left hr
  obtain ⟨a, ha, w, hw, hraw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hrV
  have hua : u * a * u⁻¹ = a := by
    rw [← mem_centralizer_singleton_iff.mp (hXC ha)]; group
  have hp : x * u ∈ P := hu
  have hu' : u = x * (x * u) := by rw [← mul_assoc, hx.sq, one_mul]
  have hur : r⁻¹ * (u * r * u⁻¹) ∈ V₀ := by
    have hwu : u * w * u⁻¹ ∈ V₀ := by
      rw [outer_conj_V₀ hP hx hu hw]
      exact (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) w).mp hw
    rw [hraw]
    have : (a * w)⁻¹ * (u * (a * w) * u⁻¹) = w⁻¹ * (u * w * u⁻¹) := by
      calc (a * w)⁻¹ * (u * (a * w) * u⁻¹) = w⁻¹ * a⁻¹ * (u * a * u⁻¹) * (u * w * u⁻¹) := by
            group
        _ = w⁻¹ * (u * w * u⁻¹) := by rw [hua]; group
    rw [this]
    exact mul_mem (inv_mem hw) hwu
  have hxr : r⁻¹ * (x * r * x⁻¹) ∈ V₀ := by
    have hxV₀ : ∀ y ∈ V₀, x * y * x⁻¹ ∈ V₀ := fun y hy =>
      (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) y).mp hy
    set p := x * u with hpdef
    have h1 := P_mod hP hp (mem_sup_left hr)
    have hup : u = x * p := by rw [hpdef, ← mul_assoc, hx.sq, one_mul]
    have e : r⁻¹ * (x * r * x⁻¹) =
        (r⁻¹ * (u * r * u⁻¹)) * (x * (r⁻¹ * (p * r * p⁻¹)) * x⁻¹)⁻¹ := by
      rw [hup]
      group
    rw [e]
    exact mul_mem hur (inv_mem (hxV₀ _ h1))
  have hxrR : r⁻¹ * (x * r * x⁻¹) ∈ R ⊓ V₀ :=
    mem_inf.mpr ⟨mul_mem (inv_mem hr) ((mem_normalizer_iff.mp hx.normR r).mp hr), hxr⟩
  rw [h.inf_R_V₀, mem_bot] at hxrR
  have hxrc : x * r = r * x := by
    have : x * r * x⁻¹ = r := by
      calc x * r * x⁻¹ = r * (r⁻¹ * (x * r * x⁻¹)) := by group
        _ = r := by rw [hxrR, mul_one]
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [this]
  rcases hx.fix_R r hr hxrc with h1 | h1
  · exact hr1 h1
  · exact hrr₁ h1

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
include hIIa hV'

omit hP hPC hIIa in
theorem outer_mem_V' {v : G} (hv : v ∈ V') : x * v * x⁻¹ ∈ V' := by
  have hxP : x * v * x⁻¹ ∈ P := (mem_normalizer_iff.mp hx.normP v).mp (hV'.le hv)
  have hv2 : v * v = 1 := by rw [← sq]; exact hV'.elem.2 v hv
  have hxv2 : x * v * x⁻¹ * (x * v * x⁻¹) = 1 := by
    calc x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  by_cases hxV : x * v * x⁻¹ ∈ R ⊔ T
  · have hvV : v ∈ R ⊔ T := by
      have := (mem_normalizer_iff.mp (inv_mem hx.normV) (x * v * x⁻¹)).mp hxV
      simpa [mul_assoc] using this
    have hv0 : v ∈ V₀ := hV'.inf ▸ mem_inf.mpr ⟨hvV, hv⟩
    have hxv0 : x * v * x⁻¹ ∈ V₀ :=
      (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) v).mp hv0
    exact (hV'.inf ▸ inf_le_right : V₀ ≤ V') hxv0
  · exact hV'.inv _ hxP hxv2 hxV

omit hP hPC hIIa in
theorem outer_mem_normalizer_V' : x ∈ normalizer (V' : Set G) := by
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h.outer_mem_V' hx hV' hv, fun hv => ?_⟩
  have := h.outer_mem_V' hx hV' hv
  rwa [outer_inv hx, show x * (x * v * x) * x = (x * x) * v * (x * x) by group, hx.sq,
    one_mul, mul_one] at this

theorem outer_card_le_four_V' {u : G} (hu : x * u ∈ P) {X : Subgroup G} (hXV : X ≤ V')
    (hXC : X ≤ centralizer ({u} : Set G)) : Nat.card X ≤ 4 := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  by_contra hX4
  push Not at hX4
  have hdvd : Nat.card X ∣ 16 := hV'.card ▸ card_dvd_of_le hXV
  have hXV₀ : Nat.card (X ⊓ V₀ : Subgroup G) ≤ 2 := by
    have hle : X ⊓ V₀ ≤ V₀ ⊓ centralizer ({u} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hXC)
    exact (card_le_of_le hle).trans
      (h.outer_card_inf_centralizer_V₀ hx fun w hw => outer_conj_V₀ hP hx hu hw)
  have hV₀N : V₀ ≤ normalizer (X : Set G) := le_normalizer_of_le hV'.elem hXV hV₀V'
  have hc := card_sup_mul_card_inf_of_le hV₀N
  rw [h.card_V₀, inf_comm] at hc
  have hsupV : V₀ ⊔ X ≤ V' := sup_le hV₀V' hXV
  have hsup16 := card_le_of_le hsupV
  rw [hV'.card] at hsup16
  have hX8 : 8 ≤ Nat.card X := by
    have h1 : Nat.card X ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h2 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h2] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hpos : 0 < Nat.card (X ⊓ V₀ : Subgroup G) := Nat.card_pos
  have hsupeq : V₀ ⊔ X = V' := by
    apply eq_of_le_of_card_ge hsupV
    rw [hV'.card]
    nlinarith
  have hu' : u = x * (x * u) := by rw [← mul_assoc, hx.sq, one_mul]
  have hxV₀ : ∀ y ∈ V₀, x * y * x⁻¹ ∈ V₀ := fun y hy =>
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) y).mp hy
  have htriv : ∀ v ∈ V', v⁻¹ * (x * v * x⁻¹) ∈ V₀ := by
    intro v hv
    have hvX : v ∈ X ⊔ V₀ := by rw [sup_comm, hsupeq]; exact hv
    obtain ⟨a, ha, w, hw, hvaw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hvX
    have hua : u * a * u⁻¹ = a := by
      rw [← mem_centralizer_singleton_iff.mp (hXC ha)]; group
    have hwu : u * w * u⁻¹ ∈ V₀ := by
      rw [outer_conj_V₀ hP hx hu hw]
      exact hxV₀ w hw
    have hur : v⁻¹ * (u * v * u⁻¹) ∈ V₀ := by
      have : v⁻¹ * (u * v * u⁻¹) = w⁻¹ * (u * w * u⁻¹) := by
        rw [hvaw]
        calc (a * w)⁻¹ * (u * (a * w) * u⁻¹) = w⁻¹ * a⁻¹ * (u * a * u⁻¹) * (u * w * u⁻¹) := by
              group
          _ = w⁻¹ * (u * w * u⁻¹) := by rw [hua]; group
      rw [this]
      exact mul_mem (inv_mem hw) hwu
    set p := x * u with hpdef
    have hup : u = x * p := by rw [hpdef, ← mul_assoc, hx.sq, one_mul]
    have hpv : v⁻¹ * (p * v * p⁻¹) ∈ V₀ := by
      have h1 := h.P_comm_mem_V₀ hP hPC hIIa hu (hV'.le hv)
      have h2 : v * (p * v * p⁻¹ * v⁻¹) = (p * v * p⁻¹ * v⁻¹) * v := P_comm_V₀ hP h1 (hV'.le hv)
      have e : v⁻¹ * (p * v * p⁻¹) = v⁻¹ * ((p * v * p⁻¹ * v⁻¹) * v) := by group
      rw [e, ← h2]
      simpa using h1
    have e : v⁻¹ * (x * v * x⁻¹) =
        (v⁻¹ * (u * v * u⁻¹)) * (x * (v⁻¹ * (p * v * p⁻¹)) * x⁻¹)⁻¹ := by
      rw [hup]
      group
    rw [e]
    exact mul_mem hur (inv_mem (hxV₀ _ hpv))
  obtain ⟨p, hp, hpx⟩ := hx.move
  apply hpx
  have hV'N : V' ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun v hv => (hP.le (hV'.le hv)).1
  have hpV : p ∈ (R ⊔ T) ⊔ V' := hV'.sup ▸ hp
  obtain ⟨v, hv, v', hv', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hV'N hpV
  have hxv : x * v * x⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp hx.normV v).mp hv
  have h1 := htriv v' hv'
  have e : (v * v')⁻¹ * (x * (v * v') * x⁻¹) =
      v'⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * v' * (v'⁻¹ * (x * v' * x⁻¹)) := by group
  rw [e]
  refine mul_mem ?_ (h.V₀_le h1)
  have h2 : v'⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * v'⁻¹⁻¹ ∈ R ⊔ T :=
    (mem_normalizer_iff.mp (inv_mem (hV'N hv')) _).mp (mul_mem (inv_mem hv) hxv)
  simpa using h2

omit hIIa in
theorem outer_card_le_four_V'_of_isVprime {u : G} (hu : x * u ∈ P) {X : Subgroup G}
    (hXV : X ≤ V') (hXC : X ≤ centralizer ({u} : Set G)) : Nat.card X ≤ 4 := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  by_contra hX4
  push Not at hX4
  have hdvd : Nat.card X ∣ 16 := hV'.card ▸ card_dvd_of_le hXV
  have hXV₀ : Nat.card (X ⊓ V₀ : Subgroup G) ≤ 2 := by
    have hle : X ⊓ V₀ ≤ V₀ ⊓ centralizer ({u} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hXC)
    exact (card_le_of_le hle).trans
      (h.outer_card_inf_centralizer_V₀ hx fun w hw => outer_conj_V₀ hP hx hu hw)
  have hV₀N : V₀ ≤ normalizer (X : Set G) := le_normalizer_of_le hV'.elem hXV hV₀V'
  have hc := card_sup_mul_card_inf_of_le hV₀N
  rw [h.card_V₀, inf_comm] at hc
  have hsupV : V₀ ⊔ X ≤ V' := sup_le hV₀V' hXV
  have hsup16 := card_le_of_le hsupV
  rw [hV'.card] at hsup16
  have hX8 : 8 ≤ Nat.card X := by
    have h1 : Nat.card X ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have h2 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
    rw [h2] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hpos : 0 < Nat.card (X ⊓ V₀ : Subgroup G) := Nat.card_pos
  have hsupeq : V₀ ⊔ X = V' := by
    apply eq_of_le_of_card_ge hsupV
    rw [hV'.card]
    nlinarith
  have hu' : u = x * (x * u) := by rw [← mul_assoc, hx.sq, one_mul]
  have hxV₀ : ∀ y ∈ V₀, x * y * x⁻¹ ∈ V₀ := fun y hy =>
    (mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hx.normV) y).mp hy
  have htriv : ∀ v ∈ V', v⁻¹ * (x * v * x⁻¹) ∈ V₀ := by
    intro v hv
    have hvX : v ∈ X ⊔ V₀ := by rw [sup_comm, hsupeq]; exact hv
    obtain ⟨a, ha, w, hw, hvaw⟩ := exists_mul_of_mem_sup_of_le_normalizer hV₀N hvX
    have hua : u * a * u⁻¹ = a := by
      rw [← mem_centralizer_singleton_iff.mp (hXC ha)]; group
    have hwu : u * w * u⁻¹ ∈ V₀ := by
      rw [outer_conj_V₀ hP hx hu hw]
      exact hxV₀ w hw
    have hur : v⁻¹ * (u * v * u⁻¹) ∈ V₀ := by
      have : v⁻¹ * (u * v * u⁻¹) = w⁻¹ * (u * w * u⁻¹) := by
        rw [hvaw]
        calc (a * w)⁻¹ * (u * (a * w) * u⁻¹) = w⁻¹ * a⁻¹ * (u * a * u⁻¹) * (u * w * u⁻¹) := by
              group
          _ = w⁻¹ * (u * w * u⁻¹) := by rw [hua]; group
      rw [this]
      exact mul_mem (inv_mem hw) hwu
    set p := x * u with hpdef
    have hup : u = x * p := by rw [hpdef, ← mul_assoc, hx.sq, one_mul]
    have hpv : v⁻¹ * (p * v * p⁻¹) ∈ V₀ := by
      have h1 := h.P_comm_mem_V₀_of_sq hP hPC hu (hV'.le hv)
      have h2 : v * (p * v * p⁻¹ * v⁻¹) = (p * v * p⁻¹ * v⁻¹) * v := P_comm_V₀ hP h1 (hV'.le hv)
      have e : v⁻¹ * (p * v * p⁻¹) = v⁻¹ * ((p * v * p⁻¹ * v⁻¹) * v) := by group
      rw [e, ← h2]
      simpa using h1
    have e : v⁻¹ * (x * v * x⁻¹) =
        (v⁻¹ * (u * v * u⁻¹)) * (x * (v⁻¹ * (p * v * p⁻¹)) * x⁻¹)⁻¹ := by
      rw [hup]
      group
    rw [e]
    exact mul_mem hur (inv_mem (hxV₀ _ hpv))
  obtain ⟨p, hp, hpx⟩ := hx.move
  apply hpx
  have hV'N : V' ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun v hv => (hP.le (hV'.le hv)).1
  have hpV : p ∈ (R ⊔ T) ⊔ V' := hV'.sup ▸ hp
  obtain ⟨v, hv, v', hv', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hV'N hpV
  have hxv : x * v * x⁻¹ ∈ R ⊔ T := (mem_normalizer_iff.mp hx.normV v).mp hv
  have h1 := htriv v' hv'
  have e : (v * v')⁻¹ * (x * (v * v') * x⁻¹) =
      v'⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * v' * (v'⁻¹ * (x * v' * x⁻¹)) := by group
  rw [e]
  refine mul_mem ?_ (h.V₀_le h1)
  have h2 : v'⁻¹ * (v⁻¹ * (x * v * x⁻¹)) * v'⁻¹⁻¹ ∈ R ⊔ T :=
    (mem_normalizer_iff.mp (inv_mem (hV'N hv')) _).mp (mul_mem (inv_mem hv) hxv)
  simpa using h2

omit hP hPC hIIa in
theorem outer_exists_mem_V' : ∃ v ∈ V', v ∉ V₀ ∧ x * v = v * x := by
  have hcard := card_le_sq_card_inf_centralizer hV'.elem (h.outer_mem_normalizer_V' hx hV')
    (by rw [hx.sq]; exact one_mem _)
  rw [hV'.card] at hcard
  have h2 := h.outer_card_inf_centralizer_V₀ hx (u := x) fun w _ => rfl
  by_contra hno
  push Not at hno
  have hle : V' ⊓ centralizer ({x} : Set G) ≤ V₀ ⊓ centralizer ({x} : Set G) := by
    intro v hv
    obtain ⟨hvV', hvC⟩ := mem_inf.mp hv
    by_contra hv0
    have hv0' : v ∉ V₀ := fun h0 => hv0 (mem_inf.mpr ⟨h0, hvC⟩)
    exact hno v hvV' hv0' (mem_centralizer_singleton_iff.mp hvC).symm
  have h3 := (card_le_of_le hle).trans h2
  have h4 : Nat.card (V' ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 4 := by
    calc Nat.card (V' ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ 2 :=
          Nat.pow_le_pow_left h3 2
      _ = 4 := by norm_num
  omega

omit hIIa hV' in
theorem outer_exists_conj_eq (hP64 : Nat.card P = 64) {u : G} (hu : x * u ∈ P)
    (hu2 : u * u = 1) : ∃ q ∈ P, q⁻¹ * x * q = u := by
  have hV₀2 : ∀ y ∈ V₀, y * y = 1 := fun y hy => h.mul_self (h.V₀_le hy)
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hxinv := outer_inv hx
  set p := x * u with hpdef
  have hup : u = x * p := by rw [hpdef, ← mul_assoc, hx.sq, one_mul]
  have hPP₀ : P ≤ transvGroup (R ⊔ T) V₀ := hP.le
  set f := transvHom (T := T) (V₀ := V₀) hx.r_mem with hf
  have hfeq := h.transvHom_eq_iff hx.r_mem hx.r_ne
  have hxr : x * r₁ = r₁ * x := hx.r_comm
  have hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P := fun y hy => (mem_normalizer_iff.mp hx.normP y).mp hy
  have hxpx : x * p * x⁻¹ = p⁻¹ := by
    have h1 : x * p * (x * p) = 1 := by rw [← hup]; exact hu2
    calc x * p * x⁻¹ = x * p * x := by rw [hxinv]
      _ = (x * p * (x * p)) * p⁻¹ := by group
      _ = p⁻¹ := by rw [h1, one_mul]
  have hfp : x * ((f ⟨p, hPP₀ hu⟩ : ↥V₀) : G) * x⁻¹ = (f ⟨p, hPP₀ hu⟩ : ↥V₀) := by
    have h1 := transvHom_conj hx.r_mem hxr (hPP₀ hu) (hPP₀ (hxP p hu))
    rw [← h1]
    have hpsq : p * p * r₁ = r₁ * (p * p) := h.comm (h.P_sq_mem_V hP hPC hu) (mem_sup_left hx.r_mem)
    change r₁⁻¹ * (x * p * x⁻¹ * r₁ * (x * p * x⁻¹)⁻¹) = r₁⁻¹ * (p * r₁ * p⁻¹)
    rw [hxpx, inv_inv]
    congr 1
    calc p⁻¹ * r₁ * p = p⁻¹ * (r₁ * (p * p)) * p⁻¹ := by group
      _ = p⁻¹ * (p * p * r₁) * p⁻¹ := by rw [hpsq]
      _ = p * r₁ * p⁻¹ := by group
  set c := ((f ⟨p, hPP₀ hu⟩ : ↥V₀) : G) with hc
  have hcV₀ : c ∈ V₀ := (f ⟨p, hPP₀ hu⟩).2
  have hcx : x * c = c * x := by
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [hfp]
  have hV₀e : IsElemAbelian 2 V₀ := isElemAbelian_of_le h.loc.elem h.V₀_le
  have hxV₀ : x ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hx.normV
  have hcardV₀ : Nat.card (V₀ ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ Nat.card V₀ := by
    have h1 := h.outer_card_inf_centralizer_V₀ hx (u := x) fun w _ => rfl
    rw [h.card_V₀]
    calc Nat.card (V₀ ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ 2 :=
          Nat.pow_le_pow_left h1 2
      _ = 4 := by norm_num
  obtain ⟨e, he, hee⟩ := exists_conj_eq_mul_of_sq_le hV₀e hxV₀ (by rw [hx.sq]; exact one_mem _)
    hcardV₀ hcV₀ hcx
  have he2 : e * e = 1 := hV₀2 e he
  have heinv : e⁻¹ = e := by
    calc e⁻¹ = e⁻¹ * (e * e) := by rw [he2, mul_one]
      _ = e := by group
  have hce : c = x * e * x⁻¹ * e := by
    calc c = x⁻¹ * (x * c) := by group
      _ = x⁻¹ * (e⁻¹ * x * e) := by rw [hee]
      _ = x * e * x⁻¹ * e := by rw [heinv, hxinv]; group
  obtain ⟨q, hq, hqe⟩ := h.exists_mem_P_transvHom hP hPC hP64 hx.r_mem hx.r_ne he
  set m := x * q⁻¹ * x⁻¹ * p * q with hm
  have hmP : m ∈ P := mul_mem (mul_mem (hxP _ (inv_mem hq)) hu) hq
  have hfm : f ⟨m, hPP₀ hmP⟩ = 1 := by
    have e1 : (⟨m, hPP₀ hmP⟩ : ↥(transvGroup (R ⊔ T) V₀)) =
        ⟨x * q⁻¹ * x⁻¹, hPP₀ (hxP _ (inv_mem hq))⟩ * ⟨p, hPP₀ hu⟩ * ⟨q, hPP₀ hq⟩ :=
      Subtype.ext (by simp [hm, mul_assoc])
    have e2 := transvHom_conj hx.r_mem hxr (hPP₀ (inv_mem hq)) (hPP₀ (hxP _ (inv_mem hq)))
    have hfq : ((f ⟨q, hPP₀ hq⟩ : ↥V₀) : G) = e := hqe
    have hfqi : ((f ⟨q⁻¹, hPP₀ (inv_mem hq)⟩ : ↥V₀) : G) = e⁻¹ := by
      have : (⟨q⁻¹, hPP₀ (inv_mem hq)⟩ : ↥(transvGroup (R ⊔ T) V₀)) = ⟨q, hPP₀ hq⟩⁻¹ :=
        Subtype.ext rfl
      rw [this, map_inv]
      simp only [InvMemClass.coe_inv]
      rw [hfq]
    rw [e1, map_mul, map_mul]
    apply Subtype.ext
    simp only [coe_mul, OneMemClass.coe_one]
    change ((f ⟨x * q⁻¹ * x⁻¹, _⟩ : ↥V₀) : G) * c * ((f ⟨q, hPP₀ hq⟩ : ↥V₀) : G) = 1
    rw [hf, e2, ← hf, hfqi, hfq, hce, heinv]
    have hcomm : x * e * x⁻¹ * e = e * (x * e * x⁻¹) :=
      h.comm (h.V₀_le ((mem_normalizer_iff.mp hxV₀ e).mp he)) (h.V₀_le he)
    calc x * e * x⁻¹ * (x * e * x⁻¹ * e) * e = x * (e * e) * x⁻¹ * (e * e) := by group
      _ = 1 := by rw [he2]; group
  have hmV : m ∈ R ⊔ T := by
    have h1 := (hfeq ⟨m, hPP₀ hmP⟩ 1).mp (by rw [hfm, map_one])
    rw [← hPC]
    exact mem_inf.mpr ⟨hmP, by simpa using h1⟩
  have hqu : q⁻¹ * u * q = x * m := by
    calc q⁻¹ * u * q = q⁻¹ * (x * p) * q := by rw [← hup]
      _ = (x * x) * q⁻¹ * x * p * q := by rw [hx.sq]; group
      _ = x * m := by rw [hm, hxinv]; group
  have hm2 : x * m * (x * m) = 1 := by
    rw [← hqu]
    calc q⁻¹ * u * q * (q⁻¹ * u * q) = q⁻¹ * (u * u) * q := by group
      _ = 1 := by rw [hu2]; group
  have hmx : x * m = m * x := by
    have hmm : m * m = 1 := h.mul_self hmV
    have hminv : m⁻¹ = m := by
      calc m⁻¹ = m⁻¹ * (m * m) := by rw [hmm, mul_one]
        _ = m := by group
    calc x * m = (x * m * (x * m)) * m⁻¹ * x⁻¹ := by group
      _ = m⁻¹ * x⁻¹ := by rw [hm2, one_mul]
      _ = m * x := by rw [hminv, hxinv]
  have hcV := h.card_inf_centralizer_V_le hx.normR (h.normalizer_le_normalizer_V₀ hx.normV)
    hx.r_mem hx.z_mem hx.fix_R hx.fix_V₀
  have hsq : Nat.card ((R ⊔ T) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤
      Nat.card (R ⊔ T : Subgroup G) := by
    rw [h.loc.card, sq]
    exact (Nat.mul_le_mul hcV hcV).trans (by norm_num)
  obtain ⟨v, hv, hvx⟩ := exists_conj_eq_mul_of_sq_le h.loc.elem hx.normV
    (by rw [hx.sq]; exact one_mem _) hsq hmV hmx
  refine ⟨v * q⁻¹, mul_mem (hVP hv) (inv_mem hq), ?_⟩
  calc (v * q⁻¹)⁻¹ * x * (v * q⁻¹) = q * (v⁻¹ * x * v) * q⁻¹ := by group
    _ = q * (x * m) * q⁻¹ := by rw [hvx]
    _ = q * (q⁻¹ * u * q) * q⁻¹ := by rw [hqu]
    _ = u := by group

omit hIIa hV' hP hPC in
theorem outer_exists_conj_mul_r : ∃ r ∈ R, r⁻¹ * x * r = x * r₁ := by
  have hcard : Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ Nat.card R := by
    have hle : R ⊓ centralizer ({x} : Set G) ≤ zpowers r₁ := by
      intro r hr
      obtain ⟨hrR, hrC⟩ := mem_inf.mp hr
      rcases hx.fix_R r hrR (mem_centralizer_singleton_iff.mp hrC).symm with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    have h1 : Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 := by
      refine (card_le_of_le hle).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one two_pos (by rw [sq]; exact h.mul_self (mem_sup_left hx.r_mem))
    rw [h.cardR]
    calc Nat.card (R ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ 2 :=
          Nat.pow_le_pow_left h1 2
      _ = 4 := by norm_num
  exact exists_conj_eq_mul_of_sq_le h.elemR hx.normR (by rw [hx.sq]; exact one_mem _) hcard
    hx.r_mem hx.r_comm

omit hIIa hV' hPC in
theorem outer_exists_conj_mul_z {u : G} (hu : x * u ∈ P) (hu2 : u * u = 1) :
    ∃ w ∈ V₀, w⁻¹ * u * w = u * z := by
  have hV₀e : IsElemAbelian 2 V₀ := isElemAbelian_of_le h.loc.elem h.V₀_le
  have hact := fun w (hw : w ∈ V₀) => outer_conj_V₀ hP hx hu hw
  have hxV₀ : x ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hx.normV
  have hu' : u = x * (x * u) := by rw [← mul_assoc, hx.sq, one_mul]
  have huV₀ : u ∈ normalizer (V₀ : Set G) := by
    rw [hu']
    exact mul_mem hxV₀ (h.normalizer_le_normalizer_V₀ (hP.le hu).1)
  have hcard : Nat.card (V₀ ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 ≤ Nat.card V₀ := by
    have h1 := h.outer_card_inf_centralizer_V₀ hx hact
    rw [h.card_V₀]
    calc Nat.card (V₀ ⊓ centralizer ({u} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ 2 :=
          Nat.pow_le_pow_left h1 2
      _ = 4 := by norm_num
  have huz : u * z = z * u := by
    have h1 : u * z * u⁻¹ = z := by rw [hact z hx.z_mem, hx.z_comm]; group
    calc u * z = u * z * u⁻¹ * u := by group
      _ = z * u := by rw [h1]
  exact exists_conj_eq_mul_of_sq_le hV₀e huV₀ (by rw [hu2]; exact one_mem _) hcard hx.z_mem huz

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
