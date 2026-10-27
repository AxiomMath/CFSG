module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsExt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem gme_exists_conj_of_sq (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {y : G} (hy : y ∈ szT₁ L T)
    (hyw : (y * w) ^ 2 = 1) : ∃ c ∈ szT₁ L T, c * w * c⁻¹ = y * w := by
  obtain ⟨-, -, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨W, -, -, hWcard, -, -, -, hWiff⟩ := h.exists_W_of_card_sylow hS2 hwT hw2 hwS
  refine h.muOneCent_exists_conj_of_mem_W hS2 hwT hw2 hwS hWcard hWiff ((hWiff y hy).mp ?_)
  have hyw' : y * w * (y * w) = 1 := by rw [← sq, hyw]
  have hw' : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, ← sq, hw2, inv_one]
  have e : w * y * w⁻¹ = y⁻¹ := by
    calc w * y * w⁻¹ = y⁻¹ * (y * w * (y * w)) * (w⁻¹ * w⁻¹) := by group
      _ = y⁻¹ := by rw [hyw', hw', mul_one, mul_one]
  rw [e, show y⁻¹ * y⁻¹ = (y ^ 2)⁻¹ by rw [sq, mul_inv_rev]]
  exact inv_mem (hsqT y hy)

theorem gme_exists_conj_or (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {x : G} (hxT : x ∈ T) (hx2 : x ^ 2 = 1)
    (hxS : x ∉ szT₁ L T ⊔ zpowers t) :
    ∃ c ∈ szT₁ L T, c * w * c⁻¹ = x ∨ c * (t * w) * c⁻¹ = x := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hxw := h.mul_mem_of_outer_of_card_sylow hS2 hxT hwT hx2 hw2 hxS hwS
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hxw
  have hww : w * w = 1 := by rw [← sq, hw2]
  have hx : x = y * z * w := by
    calc x = x * w * w := by rw [mul_assoc, hww, mul_one]
      _ = y * z * w := by rw [hyz]
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with h1 | h1
  · rw [h1, mul_one] at hx
    obtain ⟨c, hc, hcw⟩ := h.gme_exists_conj_of_sq hS2 hwT hw2 hwS hy (by rw [← hx]; exact hx2)
    exact ⟨c, hc, Or.inl (hcw.trans hx.symm)⟩
  · rw [h1, mul_assoc] at hx
    have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (h.le hwT)
    have htwT : t * w ∈ T := mul_mem htT hwT
    have htw2 : (t * w) ^ 2 = 1 := by
      rw [Commute.mul_pow hwt.symm 2, h.sq_eq_one, hw2, one_mul]
    have htwS : t * w ∉ szT₁ L T ⊔ zpowers t := fun hm => hwS (by
      rw [show w = t⁻¹ * (t * w) by group]
      exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm)
    obtain ⟨c, hc, hcw⟩ :=
      h.gme_exists_conj_of_sq hS2 htwT htw2 htwS hy (by rw [← hx]; exact hx2)
    exact ⟨c, hc, Or.inr (hcw.trans hx.symm)⟩

theorem gme_conj_not_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w a : G} (hwT : w ∈ T)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) (ha : a ∈ centralizer ({t} : Set G)) :
    a⁻¹ * w * a ∉ szT₁ L T ⊔ zpowers t := by
  intro hm
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have haN : a ∈ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1 ha
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hm
  have hzT : z ∈ T := zpowers_le.mpr htT hz
  have haz : a * z = z * a :=
    commute_of_mem_zpowers hz (mem_centralizer_singleton_iff.mp ha)
  have hw : w = (a * y * a⁻¹) * z := by
    calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
      _ = a * (y * z) * a⁻¹ := by rw [hyz]
      _ = (a * y * a⁻¹) * (a * z) * a⁻¹ := by group
      _ = (a * y * a⁻¹) * z := by rw [haz]; group
  have hyL : a * y * a⁻¹ ∈ L :=
    (mem_normalizer_iff.mp haN y).mp (szT₁_le_right L T hy)
  have hyT : a * y * a⁻¹ ∈ T := by
    rw [show a * y * a⁻¹ = w * z⁻¹ by rw [hw]; group]
    exact mul_mem hwT (inv_mem hzT)
  have hyT₁ : a * y * a⁻¹ ∈ szT₁ L T := mem_inf.mpr ⟨hyT, hyL⟩
  exact hwS (by rw [hw]; exact mul_mem (mem_sup_left hyT₁) (mem_sup_right hz))

theorem gme_isSylowOf_inf_centralizer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {w : G} (hwT : w ∈ T)
    (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t) :
    IsSylowOf 2 (T ⊓ centralizer ({w} : Set G))
      (centralizer ({t} : Set G) ⊓ centralizer ({w} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀K : T ⊓ centralizer ({w} : Set G) ≤
      centralizer ({t} : Set G) ⊓ centralizer ({w} : Set G) := inf_le_inf_right _ h.le
  have hT₀2 : IsPGroup 2 (T ⊓ centralizer ({w} : Set G) : Subgroup G) :=
    h.isPGroup.to_le inf_le_left
  obtain ⟨Q, hQ, hT₀Q⟩ := exists_isSylowOf_le_of_isPGroup hT₀K hT₀2
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  obtain ⟨a, haC, ha⟩ :=
    exists_conj_mem_of_isSylowOf hTsyl (hQ.le.trans inf_le_left) hQ.isPGroup
  have hwQ : w ∈ Q := hT₀Q (mem_inf.mpr ⟨hwT, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hxT : a⁻¹ * w * a ∈ T := ha w hwQ
  have hx2 : (a⁻¹ * w * a) ^ 2 = 1 := by
    calc (a⁻¹ * w * a) ^ 2 = a⁻¹ * w ^ 2 * a := by rw [sq, sq]; group
      _ = 1 := by rw [hw2]; group
  obtain ⟨c, hc, hcx⟩ :=
    h.gme_exists_conj_or hS2 hwT hw2 hwS hxT hx2 (h.gme_conj_not_mem hS2 hwT hwS haC)
  have hcT : c ∈ T := szT₁_le_left L T hc
  have hconj : ∀ {y : G}, (a * c)⁻¹ * w * (a * c) = y → ∀ q : G, q * w = w * q →
      ((a * c)⁻¹ * q * (a * c)) * y = y * ((a * c)⁻¹ * q * (a * c)) := by
    intro y hy q hq
    rw [← hy]
    calc (a * c)⁻¹ * q * (a * c) * ((a * c)⁻¹ * w * (a * c)) = (a * c)⁻¹ * (q * w) * (a * c) := by
          group
      _ = (a * c)⁻¹ * (w * q) * (a * c) := by rw [hq]
      _ = (a * c)⁻¹ * w * (a * c) * ((a * c)⁻¹ * q * (a * c)) := by group
  have hmap : ∀ q ∈ Q, (a * c)⁻¹ * q * (a * c) ∈ T ⊓ centralizer ({w} : Set G) := by
    intro q hq
    have hqT : (a * c)⁻¹ * q * (a * c) ∈ T := by
      rw [show (a * c)⁻¹ * q * (a * c) = c⁻¹ * (a⁻¹ * q * a) * c by group]
      exact mul_mem (mul_mem (inv_mem hcT) (ha q hq)) hcT
    have hqw : q * w = w * q :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (hQ.le hq)).2
    refine mem_inf.mpr ⟨hqT, mem_centralizer_singleton_iff.mpr ?_⟩
    rcases hcx with hcx | hcx
    · have hgw : (a * c)⁻¹ * w * (a * c) = w := by
        rw [show (a * c)⁻¹ * w * (a * c) = c⁻¹ * (a⁻¹ * w * a) * c by group, ← hcx]
        group
      exact hconj hgw q hqw
    · have hgw : (a * c)⁻¹ * w * (a * c) = t * w := by
        rw [show (a * c)⁻¹ * w * (a * c) = c⁻¹ * (a⁻¹ * w * a) * c by group, ← hcx]
        group
      have h1 := hconj hgw q hqw
      have h2 : ((a * c)⁻¹ * q * (a * c)) * t⁻¹ = t⁻¹ * ((a * c)⁻¹ * q * (a * c)) :=
        (show Commute ((a * c)⁻¹ * q * (a * c)) t from
          mem_centralizer_singleton_iff.mp (h.le hqT)).inv_right.eq
      calc (a * c)⁻¹ * q * (a * c) * w =
          ((a * c)⁻¹ * q * (a * c)) * t⁻¹ * (t * w) := by group
        _ = t⁻¹ * ((a * c)⁻¹ * q * (a * c)) * (t * w) := by rw [h2]
        _ = t⁻¹ * (((a * c)⁻¹ * q * (a * c)) * (t * w)) := by group
        _ = t⁻¹ * ((t * w) * ((a * c)⁻¹ * q * (a * c))) := by rw [h1]
        _ = w * ((a * c)⁻¹ * q * (a * c)) := by group
  have hcard : Nat.card Q ≤ Nat.card (T ⊓ centralizer ({w} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun q : Q => (⟨(a * c)⁻¹ * q * (a * c), hmap q q.2⟩ :
        (T ⊓ centralizer ({w} : Set G) : Subgroup G))) ?_
    intro q q' hqq'
    have e : (a * c)⁻¹ * (q : G) * (a * c) = (a * c)⁻¹ * (q' : G) * (a * c) :=
      congrArg Subtype.val hqq'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel e))
  have heq : T ⊓ centralizer ({w} : Set G) = Q := eq_of_le_of_card_ge hT₀Q hcard
  rw [heq]
  exact hQ

end U3Start

namespace U3C1OuterSwapHigh

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G} {w s : G} {P : Subgroup G}
  (hW : U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P)
include hW

theorem gme_lang : IsSylowOf 2 (T ⊓ centralizer ({t * w} : Set G))
    (centralizer ({t} : Set G) ⊓ centralizer ({t * w} : Set G)) :=
  hW.step.start.gme_isSylowOf_inf_centralizer hW.step.card_sylow hW.tw_mem hW.tw_sq
    hW.tw_not_mem

end U3C1OuterSwapHigh

theorem u3C1GmsLangInput_holds : U3C1GmsLangInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW => hW.gme_lang

theorem u3C1GmsExtremalInput_holds : U3C1GmsExtremalInput :=
  u3C1GmsExtremalInput_of_lang u3C1GmsLangInput_holds

end CFSG.SeitzReduction.RankOne
