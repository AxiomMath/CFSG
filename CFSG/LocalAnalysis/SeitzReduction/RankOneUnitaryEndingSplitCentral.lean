module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplit
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSplitLift

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem exists_fpf_of_split
    (hD : U3EndingData G L f t T R₂ U₁ s) {J₁ J₂ : Subgroup G} (hJ : J₁ ⊔ J₂ = U₁)
    (hJinf : J₁ ⊓ J₂ = R₂) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hK : ∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
      k ∈ normalizer (J₁ : Set G)) :
    ∃ e : G, Odd (orderOf e) ∧ (∀ x ∈ J₁, e * x * e⁻¹ ∈ J₁) ∧ (∀ r ∈ R₂, e * r * e⁻¹ = r) ∧
      (∀ x ∈ J₁, e * x * e⁻¹ * x⁻¹ ∈ R₂ → x ∈ R₂) := by
  classical
  obtain ⟨E, _, _, d, μ, a, χ₁, χ₂, hKE, hμ0, hμ, -, -, hdodd, hdJ₁, hdR, ha_add, haR0, haR, -,
    hda, hχ₁, hχ₂, hχ, hdχ₁, hdχ₂⟩ := hD.exists_coords_of_split hJ hJinf ht₁ ht₂ hK
  have hU := hD.u1
  have hJ₁U : J₁ ≤ U₁ := hJ ▸ le_sup_left
  have hRJ₁ : R₂ ≤ J₁ := hJinf ▸ inf_le_left
  have hf : 2 ≤ f := hD.start.two_le
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : Nat.card E = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hKE, ← pow_mul, mul_comm]
  have : CharP E 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have hpowJ : ∀ j : ℕ, ∀ x ∈ J₁, d ^ j * x * (d ^ j)⁻¹ ∈ J₁ ∧
      a (d ^ j * x * (d ^ j)⁻¹) = μ ^ j * a x := by
    intro j
    induction j with
    | zero => intro x hx; simp [hx]
    | succ j ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      have e : d ^ (j + 1) * x * (d ^ (j + 1))⁻¹ = d * (d ^ j * x * (d ^ j)⁻¹) * d⁻¹ := by
        group
      rw [e]
      refine ⟨(mem_normalizer_iff.mp hdJ₁ _).mp h1, ?_⟩
      rw [hda _ (hJ₁U h1), h2, pow_succ]
      ring
  have hpowR : ∀ j : ℕ, ∀ r ∈ R₂, d ^ j * r * (d ^ j)⁻¹ ∈ R₂ ∧
      χ₁ (d ^ j * r * (d ^ j)⁻¹) = (μ ^ (2 ^ f + 1)) ^ j * χ₁ r ∧
      χ₂ (d ^ j * r * (d ^ j)⁻¹) = (μ ^ (2 ^ f + 1)) ^ j * χ₂ r := by
    intro j
    induction j with
    | zero => intro r hr; simp [hr]
    | succ j ih =>
      intro r hr
      obtain ⟨h1, h2, h3⟩ := ih r hr
      have e : d ^ (j + 1) * r * (d ^ (j + 1))⁻¹ = d * (d ^ j * r * (d ^ j)⁻¹) * d⁻¹ := by
        group
      rw [e]
      refine ⟨(mem_normalizer_iff.mp hdR _).mp h1, ?_, ?_⟩
      · rw [hdχ₁ _ h1, h2, pow_succ]
        ring
      · rw [hdχ₂ _ h1, h3, pow_succ]
        ring
  have hN1 : (μ ^ (2 ^ f + 1)) ^ (2 ^ f - 1) = 1 := by
    rw [← pow_mul]
    have e : (2 ^ f + 1) * (2 ^ f - 1) = (2 ^ f) ^ 2 - 1 := by
      have h1 : 1 ≤ 2 ^ f := by omega
      zify [h1, show 1 ≤ (2 ^ f) ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    rw [e]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hμ]
    refine Nat.div_dvd_of_dvd ?_
    refine (Nat.gcd_dvd_right 3 (2 ^ f + 1)).trans ⟨2 ^ f - 1, ?_⟩
    rw [← e]
  have hμ1 : μ ^ (2 ^ f - 1) ≠ 1 := by
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hμ] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hg0 : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hgdvd : Nat.gcd 3 (2 ^ f + 1) ∣ (2 ^ f) ^ 2 - 1 := by
      refine (Nat.gcd_dvd_right 3 (2 ^ f + 1)).trans ⟨2 ^ f - 1, ?_⟩
      have h1 : 1 ≤ 2 ^ f := by omega
      zify [h1, show 1 ≤ (2 ^ f) ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    have hmg := Nat.div_mul_cancel hgdvd
    set m := ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)
    set q := 2 ^ f
    have hqq : q ^ 2 = q * q := sq q
    have : m * Nat.gcd 3 (q + 1) ≤ (q - 1) * 3 := Nat.mul_le_mul hle hg
    have hq4' : 4 * q ≤ q * q := Nat.mul_le_mul_right q hq4
    omega
  refine ⟨d ^ (2 ^ f - 1), Odd.of_dvd_nat hdodd (orderOf_pow_dvd _),
    fun x hx => (hpowJ _ x hx).1, fun r hr => ?_, fun x hx h => ?_⟩
  ·
    obtain ⟨h1, h2, h3⟩ := hpowR (2 ^ f - 1) r hr
    rw [hN1, one_mul] at h2 h3
    have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU.sq_R₂ r hr)
    have hw : d ^ (2 ^ f - 1) * r * (d ^ (2 ^ f - 1))⁻¹ * r = 1 := hχ _ (mul_mem h1 hr)
      (by rw [hχ₁ _ h1 _ hr, h2, CharTwo.add_self_eq_zero])
      (by rw [hχ₂ _ h1 _ hr, h3, CharTwo.add_self_eq_zero])
    exact (eq_inv_of_mul_eq_one_left hw).trans hrinv
  ·
    obtain ⟨h1, h2⟩ := hpowJ (2 ^ f - 1) x hx
    refine haR x hx ?_
    have h3 := ha_add _ (hJ₁U h1) _ (hJ₁U (inv_mem hx))
    rw [haR0 _ h, h2] at h3
    have hinv : a x⁻¹ = -a x := by
      have := ha_add x (hJ₁U hx) x⁻¹ (hJ₁U (inv_mem hx))
      rw [mul_inv_cancel, haR0 1 (one_mem _)] at this
      linear_combination -this
    rw [hinv] at h3
    have h4 : (μ ^ (2 ^ f - 1) - 1) * a x = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (sub_eq_zero.mp h5) hμ1
    · exact h5

theorem exists_product_of_comm
    (hD : U3EndingData G L f t T R₂ U₁ s) {J₁ J₂ : Subgroup G} (hJ : J₁ ⊔ J₂ = U₁)
    (hJinf : J₁ ⊓ J₂ = R₂) (ht₁ : ∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) (ht₂ : ∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁)
    (hK : ∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
      k ∈ normalizer (J₁ : Set G)) (hc12 : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) :
    ∃ Y₁ Y₂ : Subgroup G, Y₁ ⊔ Y₂ = U₁ ∧ Y₁ ⊓ Y₂ = ⊥ ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧
      (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) ∧ (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) := by
  obtain ⟨e, heodd, heJ₁, heR, hefpf⟩ := hD.exists_fpf_of_split hJ hJinf ht₁ ht₂ hK
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨d, k, hdL, hT⟩ := h.exists_u3RTorus_of_card_sylow hS2
  have hdJ₁ : d ∈ normalizer (J₁ : Set G) := hK d hdL hT.mem_normalizer_T₁ hT.odd
  have hdt : d * t = t * d := hT.comm_t
  have hdJ₂ : d ∈ normalizer (J₂ : Set G) := by
    have key : ∀ c : G, c * t = t * c → c ∈ normalizer (J₁ : Set G) →
        ∀ x ∈ J₂, c * x * c⁻¹ ∈ J₂ := by
      intro c hct hc x hx
      have hx' : t⁻¹ * x * t ∈ J₁ := by
        have := ht₂ x hx
        rw [htinv] at this ⊢
        exact this
      have h1 := ht₁ _ ((mem_normalizer_iff.mp hc _).mp hx')
      have hctc : t * c * t⁻¹ = c := by rw [← hct, mul_inv_cancel_right]
      have e : t * (c * (t⁻¹ * x * t) * c⁻¹) * t⁻¹ = (t * c * t⁻¹) * x * (t * c * t⁻¹)⁻¹ := by
        group
      rw [e, hctc] at h1
      exact h1
    have hdt' : d⁻¹ * t = t * d⁻¹ := by
      calc d⁻¹ * t = d⁻¹ * (t * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * t) * d⁻¹ := by rw [hdt]
        _ = t * d⁻¹ := by group
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key d hdt hdJ₁ x hx, fun hx => ?_⟩
    have := key d⁻¹ hdt' (inv_mem hdJ₁) _ hx
    rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at this
  have hdR : d ∈ normalizer (R₂ : Set G) := by
    rw [← hJinf]
    refine mem_normalizer_iff.mpr fun x => ?_
    exact and_congr (mem_normalizer_iff.mp hdJ₁ x) (mem_normalizer_iff.mp hdJ₂ x)
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    mem_normalizer_szA₁_of_mem_normalizer hT.mem_normalizer_T₁
  have hUR : ∀ x ∈ U₁, ∀ r ∈ R₂, x * r = r * x := fun x hx r hr =>
    (mem_centralizer_iff.mp (hU.le_centralizer hx) r hr).symm
  have hRA : ¬ R₂ ≤ szA₁ (szT₁ L T) := by
    intro hle
    have hA1 : szA₁ (szT₁ L T) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨r, hr, hrb⟩ := hR.rho_onto b hb
      have hrt := hR.szA₁_comm_t (hle hr)
      rw [← hrb, mem_bot, hrt]
      group
      rw [← sq, hR.t_sq]
    have hbot : R₂ = ⊥ := le_bot_iff.mp (hA1 ▸ hle)
    have hcard := hR.card
    rw [hbot, card_bot] at hcard
    have h1 : 1 < (2 ^ f) ^ 2 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by have := h.two_le; omega))
    omega
  exact CFSG.SeitzReduction.RankOne.exists_product_of_comm hUR hU.commutator_eq
    hU.sq_R₂ hJ hJinf htt ht₁ ht₂ (fun r hr hrt => hR.rho_ker r hr hrt)
    (fun a ha => hR.szA₁_comm_t ha) hRA hdA hdJ₁
    (fun X hX hdX => hT.eq_bot_or_le_of_le hX hdX)
    (fun X hAX hXR hdX => hT.le_or_le_of_le hR hdR hAX hXR hdX) hc12 heJ₁ heR heodd
    (pow_orderOf_eq_one e) hefpf (hD.commutator_ne_of_split hJ hJinf ht₁ ht₂ hK)

end U3EndingData

@[expose] def U3EndingCommInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
      ∃ J₁ J₂ : Subgroup G, J₁ ⊔ J₂ = U₁ ∧ J₁ ⊓ J₂ = R₂ ∧
        (∀ x ∈ J₁, t * x * t⁻¹ ∈ J₂) ∧ (∀ x ∈ J₂, t * x * t⁻¹ ∈ J₁) ∧
        (∀ k ∈ L, k ∈ normalizer (szT₁ L T : Set G) → Odd (orderOf k) →
          k ∈ normalizer (J₁ : Set G)) ∧
        ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a

theorem u3EndingProductInput_of_comm
    (hcomm : U3EndingCommInput) : U3EndingProductInput := by
  intro G _ _ L f t T R₂ U₁ s v hD hvT hv2 hvS hsv _
  obtain ⟨J₁, J₂, hJ, hJinf, ht₁, ht₂, hK, hc12⟩ := hcomm G L f t T R₂ U₁ s v hD hvT hv2 hvS hsv
  exact hD.exists_product_of_comm hJ hJinf ht₁ ht₂ hK hc12

theorem u3EightLieInput_of_comm
    (hcomm : U3EndingCommInput) : U3EightLieInput := by
  intro G _ _ L t T R₂ U₁ s v hD hvT hv2 hvS hsv
  obtain ⟨J₁, J₂, hJ, hJinf, ht₁, ht₂, hK, hc12⟩ := hcomm G L 3 t T R₂ U₁ s v hD hvT hv2 hvS hsv
  exact hD.exists_product_of_comm hJ hJinf ht₁ ht₂ hK hc12

theorem u3EndingInput_of_comm (hcomm : U3EndingCommInput)
    (hsyl : U3EndingSylowInput) : U3EndingInput :=
  u3EndingInput_of_inputs (u3EndingProductInput_of_comm hcomm) (u3EightLieInput_of_comm hcomm)
    hsyl

end CFSG.SeitzReduction.RankOne
