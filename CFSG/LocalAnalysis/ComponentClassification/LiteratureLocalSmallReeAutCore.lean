module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.Ree.Model.Cells

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal.SmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [Finite K] in
theorem three_eq_zero_of_charP : (3 : K) = 0 := by
  have h := CharP.cast_eq_zero K ReeTag.G2.prime
  exact_mod_cast h

omit [Finite K] in
theorem two_ne_zero_of_charP : (2 : K) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K ReeTag.G2.prime] at h2
  exact absurd h2 (by decide)

section Coordinates

variable (hK : Nat.card K = 3 ^ (2 * a + 1))

@[expose] def uIn (t b c : K) : ReeTag.G2.reeGamma K a :=
  ⟨smallReeU a K t b c, ReeTag.reeFixedPosUnipotent_le_reeGamma (smallReeU_mem hK t b c)⟩

@[expose] def hIn (s : Kˣ) : ReeTag.G2.reeGamma K a :=
  ⟨smallReeH a K s, (Subgroup.mem_inf.1 (smallReeH_mem hK s)).2⟩

theorem uIn_val (t b c : K) :
    ((uIn hK t b c : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) = smallReeU a K t b c := by
  rw [uIn]

theorem hIn_val (s : Kˣ) :
    ((hIn hK s : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) = smallReeH a K s := by
  rw [hIn]

theorem uIn_inj {t b c t' b' c' : K} (h : uIn hK t b c = uIn hK t' b' c') :
    t = t' ∧ b = b' ∧ c = c' := by
  have h1 : smallReeU a K t b c = smallReeU a K t' b' c' := by
    rw [← uIn_val hK, ← uIn_val hK, h]
  exact smallReeU_inj h1

theorem uIn_mul (t b c s d e : K) :
    uIn hK t b c * uIn hK s d e =
      uIn hK (t + s) (b + d + smallReeSigma a t * s)
        (c + e - b * s + smallReeSigma a t * s ^ 2) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, uIn_val, uIn_val, uIn_val]
  exact smallReeCoord_mul hK t b c s d e

theorem uIn_zero : uIn hK (0 : K) 0 0 = 1 := by
  apply Subtype.ext
  rw [uIn_val, OneMemClass.coe_one]
  exact smallReeCoord_zero

theorem exists_uIn_eq {u : ReeTag.G2.reeGamma K a}
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a) :
    ∃ t b c : K, u = uIn hK t b c := by
  obtain ⟨t, b, c, h⟩ := exists_smallReeU_eq hK hu
  exact ⟨t, b, c, Subtype.ext (by rw [uIn_val, h])⟩

theorem uIn_mem (t b c : K) :
    ((uIn hK t b c : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
      ReeTag.G2.reeFixedPosUnipotent K a := by
  rw [uIn_val]
  exact smallReeU_mem hK t b c

theorem hIn_conj_uIn (s : Kˣ) (t b c : K) :
    hIn hK s * uIn hK t b c * (hIn hK s)⁻¹ =
      uIn hK (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t) (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b)
        ((s : K) ^ 3 ^ a * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hIn_val, uIn_val, uIn_val]
  exact ReeTag.smallReeTorusElt_conj_smallReeCoord hK s t b c

theorem hIn_neg_one_conj_uIn (t b c : K) :
    hIn hK (-1) * uIn hK t b c * (hIn hK (-1))⁻¹ = uIn hK (-t) b (-c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hIn_val, uIn_val, uIn_val]
  exact smallReeH_neg_one_conj hK t b c

theorem hIn_injective : Function.Injective (hIn (a := a) hK) := by
  intro s s' h
  apply smallReeH_injective (a := a)
  rw [← hIn_val hK, ← hIn_val hK, h]

theorem uIn_mul_eq_mul_mul (t b c s d e : K) :
    uIn hK t b c * uIn hK s d e = uIn hK s d e * uIn hK t b c *
      uIn hK 0 (smallReeSigma a t * s - smallReeSigma a s * t)
        (-(b * s) + smallReeSigma a t * s ^ 2 + d * t - smallReeSigma a s * t ^ 2) := by
  rw [uIn_mul, uIn_mul, uIn_mul]
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have hσ : ∀ x y : K, smallReeSigma a (x + y) = smallReeSigma a x + smallReeSigma a y := by
    obtain ⟨-, -, σ, -, hσ, -⟩ := small_Ree_field_power_identities a K hK
    intro x y
    rw [smallReeSigma, smallReeSigma, smallReeSigma, ← hσ, ← hσ, ← hσ, map_add]
  congr 1 <;> ring

theorem uIn_pow_three (t b c : K) :
    uIn hK t b c ^ 3 = uIn hK 0 0 (-(t ^ 2 * smallReeSigma a t)) := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, uIn_val, uIn_val]
  exact smallReeCoord_pow_three hK t b c

end Coordinates

section Core

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) (ha : 1 ≤ a)
  (β : MulAut (ReeTag.G2.reeGamma K a))
  (hT : ∀ t b c : K, ∃ b' c' : K, β (uIn hK t b c) = uIn hK t b' c')
  (hH : ∀ s : Kˣ, ∃ s' : Kˣ, β (hIn hK s) = hIn hK s')

include hT hH in
theorem core_fix_torus (s : Kˣ) : β (hIn hK s) = hIn hK s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  obtain ⟨s', hs'⟩ := hH s
  obtain ⟨b₁, c₁, h1⟩ := hT 1 0 0
  obtain ⟨b₂, c₂, h2⟩ := hT (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * 1)
    (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * 0) ((s : K) ^ 3 ^ a * 0)
  have h3 := congrArg β (hIn_conj_uIn hK s 1 0 0)
  rw [map_mul, map_mul, map_inv, hs', h1, hIn_conj_uIn, h2] at h3
  have h4 := (uIn_inj hK h3).1
  rw [mul_one, mul_one] at h4
  have h5 : s' = s := hbij.1 (Units.ext h4)
  rw [hs', h5]

include hT hH in
theorem core_mid (b : K) : ∃ b' : K, β (uIn hK 0 b 0) = uIn hK 0 b' 0 := by
  obtain ⟨b', c', h⟩ := hT 0 b 0
  refine ⟨b', ?_⟩
  have hcomm : uIn hK 0 b 0 * hIn hK (-1) = hIn hK (-1) * uIn hK 0 b 0 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, uIn_val, hIn_val]
    exact (smallReeU_commute_iff hK 0 b 0).2 ⟨rfl, rfl⟩
  have h1 := congrArg β hcomm
  rw [map_mul, map_mul, core_fix_torus hK β hT hH, h] at h1
  have h2 : smallReeU a K 0 b' c' * smallReeH a K (-1) =
      smallReeH a K (-1) * smallReeU a K 0 b' c' := by
    rw [← uIn_val hK, ← hIn_val hK, ← Subgroup.coe_mul, h1, Subgroup.coe_mul]
  obtain ⟨-, rfl⟩ := (smallReeU_commute_iff hK 0 b' c').1 h2
  exact h

include hT in
theorem core_center
    (hsurj : ∀ t b c : K, ∃ v : ReeTag.G2.reeGamma K a,
      (v : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ β v = uIn hK t b c)
    (c : K) : ∃ c' : K, β (uIn hK 0 0 c) = uIn hK 0 0 c' := by
  obtain ⟨b', c', h⟩ := hT 0 0 c
  refine ⟨c', ?_⟩
  obtain ⟨v, hvU, hv⟩ := hsurj 1 0 0
  obtain ⟨t₁, b₁, c₁, rfl⟩ := exists_uIn_eq hK hvU
  have hcomm : uIn hK 0 0 c * uIn hK t₁ b₁ c₁ = uIn hK t₁ b₁ c₁ * uIn hK 0 0 c := by
    rw [uIn_mul_eq_mul_mul hK]
    have e1 : smallReeSigma a (0 : K) * t₁ - smallReeSigma a t₁ * 0 = 0 := by
      rw [smallReeSigma_zero]; ring
    have e2 : -(0 * t₁) + smallReeSigma a (0 : K) * t₁ ^ 2 + b₁ * 0 -
        smallReeSigma a t₁ * 0 ^ 2 = 0 := by
      rw [smallReeSigma_zero]; ring
    rw [e1, e2, uIn_zero, mul_one]
  have h1 := congrArg β hcomm
  rw [map_mul, map_mul, h, hv, uIn_mul_eq_mul_mul hK, mul_eq_left, ← uIn_zero hK] at h1
  have h3 := (uIn_inj hK h1).2.2
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have h1' : smallReeSigma a (1 : K) = 1 := one_pow _
  rw [h0, h1'] at h3
  have hb : b' = 0 := by linear_combination (-1 : K) * h3
  rw [h, hb]

include hT hH in
theorem core_zeta (ζ : K → K) (hζ : ∀ c, β (uIn hK 0 0 c) = uIn hK 0 0 (ζ c)) (c : K) :
    ζ c = c * ζ 1 := by
  obtain ⟨-, ρ, -, hρ, -⟩ := small_Ree_field_power_identities a K hK
  have hequiv : ∀ (s : Kˣ) (c : K), ζ ((s : K) ^ 3 ^ a * c) = (s : K) ^ 3 ^ a * ζ c := by
    intro s c
    have h1 := congrArg β (hIn_conj_uIn hK s 0 0 c)
    rw [map_mul, map_mul, map_inv, core_fix_torus hK β hT hH, hζ, hIn_conj_uIn] at h1
    simp only [mul_zero] at h1
    rw [hζ] at h1
    exact (uIn_inj hK h1).2.2.symm
  by_cases hc : c = 0
  · subst hc
    have h1 := hζ 0
    rw [uIn_zero, map_one, ← uIn_zero hK] at h1
    rw [← (uIn_inj hK h1).2.2, zero_mul]
  · obtain ⟨x, rfl⟩ := ρ.surjective c
    have hx : x ≠ 0 := fun h => hc (by rw [h, map_zero])
    have h1 := hequiv (Units.mk0 x hx) 1
    rw [Units.val_mk0, mul_one, ← hρ] at h1
    exact h1

include hT in
theorem core_mid_eq_zeta (ζ β₁ : K → K) (hζ : ∀ c, β (uIn hK 0 0 c) = uIn hK 0 0 (ζ c))
    (hβ₁ : ∀ b, β (uIn hK 0 b 0) = uIn hK 0 (β₁ b) 0) (b : K) : ζ b = β₁ b := by
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have h1' : smallReeSigma a (1 : K) = 1 := one_pow _
  have hrel : uIn hK 1 0 0 * uIn hK 0 b 0 = uIn hK 0 b 0 * uIn hK 1 0 0 * uIn hK 0 0 b := by
    rw [uIn_mul_eq_mul_mul hK, h0, h1']
    congr 2 <;> ring
  obtain ⟨l, m, hlm⟩ := hT 1 0 0
  have h1 := congrArg β hrel
  rw [map_mul, map_mul, map_mul, hlm, hβ₁, hζ, uIn_mul_eq_mul_mul hK 1 l m 0 (β₁ b) 0, h0,
    h1'] at h1
  have h2 := mul_left_cancel h1
  have h3 := (uIn_inj hK h2).2.2
  rw [← h3]
  ring

include hT hH in
theorem core_zeta_one (ha : 1 ≤ a) (ζ β₁ : K → K)
    (hζ : ∀ c, β (uIn hK 0 0 c) = uIn hK 0 0 (ζ c))
    (hβ₁ : ∀ b, β (uIn hK 0 b 0) = uIn hK 0 (β₁ b) 0) : ζ 1 = 1 := by
  obtain ⟨-, -, σ, -, hσ, -, -, -, hσ1, -⟩ := small_Ree_field_power_identities a K hK
  obtain ⟨s, hs⟩ : ∃ s : K, smallReeSigma a s ≠ s := by
    by_contra h
    push Not at h
    exact hσ1 ha (RingEquiv.ext fun x => by rw [hσ]; exact h x)
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have h1' : smallReeSigma a (1 : K) = 1 := one_pow _
  have hU1 : ∀ B C : K, uIn hK 0 B 0 * uIn hK 0 0 C = uIn hK (0 : K) B C := by
    intro B C
    rw [uIn_mul, h0]
    congr 1 <;> ring
  have hD : ∀ B C : K, β (uIn hK 0 B C) = uIn hK 0 (β₁ B) (ζ C) := by
    intro B C
    rw [← hU1, map_mul, hβ₁, hζ, hU1]
  have hrel := uIn_mul_eq_mul_mul hK (1 : K) 0 0 s 0 0
  obtain ⟨l₁, m₁, hl₁⟩ := hT 1 0 0
  obtain ⟨l₂, m₂, hl₂⟩ := hT s 0 0
  have h1 := congrArg β hrel
  rw [map_mul, map_mul, map_mul, hl₁, hl₂, hD, uIn_mul_eq_mul_mul hK 1 l₁ m₁ s l₂ m₂] at h1
  have h2 := mul_left_cancel h1
  have h3 := (uIn_inj hK h2).2.1
  rw [← core_mid_eq_zeta hK β hT ζ β₁ hζ hβ₁, core_zeta hK β hT hH ζ hζ, h1'] at h3
  have hne : s - smallReeSigma a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have h4 : (1 * s - smallReeSigma a s * 1) * (ζ 1 - 1) = 0 := by linear_combination -h3
  rw [one_mul, mul_one] at h4
  exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left hne)

include hT hH in
theorem core_fix_U1 (ha : 1 ≤ a)
    (hsurj : ∀ t b c : K, ∃ v : ReeTag.G2.reeGamma K a,
      (v : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ β v = uIn hK t b c)
    (b c : K) : β (uIn hK 0 b c) = uIn hK 0 b c := by
  choose ζ hζ using core_center hK β hT hsurj
  choose β₁ hβ₁ using core_mid hK β hT hH
  have hz1 := core_zeta_one hK β hT hH ha ζ β₁ hζ hβ₁
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have hU1 : ∀ B C : K, uIn hK 0 B 0 * uIn hK 0 0 C = uIn hK (0 : K) B C := by
    intro B C
    rw [uIn_mul, h0]
    congr 1 <;> ring
  rw [← hU1, map_mul, hβ₁, hζ, ← core_mid_eq_zeta hK β hT ζ β₁ hζ hβ₁,
    core_zeta hK β hT hH ζ hζ b, core_zeta hK β hT hH ζ hζ c, hz1, mul_one, mul_one]

include hT hH in
theorem core_first (ha : 1 ≤ a)
    (hsurj : ∀ t b c : K, ∃ v : ReeTag.G2.reeGamma K a,
      (v : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ β v = uIn hK t b c)
    (x : K) : ∃ μ : K, β (uIn hK x 0 0) = uIn hK x 0 μ := by
  obtain ⟨l, m, hlm⟩ := hT x 0 0
  refine ⟨m, ?_⟩
  have h1 := congrArg β (hIn_neg_one_conj_uIn hK x 0 0)
  rw [map_mul, map_mul, map_inv, core_fix_torus hK β hT hH, hlm, hIn_neg_one_conj_uIn,
    neg_zero] at h1
  have h2 := uIn_mul hK x 0 0 (-x) 0 0
  rw [add_neg_cancel] at h2
  have h3 := congrArg β h2
  rw [map_mul, hlm, ← h1, uIn_mul, core_fix_U1 hK β hT hH ha hsurj] at h3
  have h4 := (uIn_inj hK h3).2.1
  have h5 : (2 : K) * l = 0 := by linear_combination h4
  rw [hlm, (mul_eq_zero.1 h5).resolve_left two_ne_zero_of_charP]

omit [CharP K ReeTag.G2.prime] in
include hK in
theorem pow_two_mul_sub_one_pow (ha : 1 ≤ a) (s : Kˣ) :
    ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) ^ (3 * 3 ^ a + 2) = (s : K) ^ 3 ^ a := by
  have hθ : 3 ≤ 3 ^ a := Nat.le_self_pow (by omega) 3
  have hq : ∀ x : K, x ^ 3 ^ (2 * a + 1) = x := fun x => by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hexp : (2 * 3 ^ a - 1) * (3 * 3 ^ a + 2) = 2 * 3 ^ (2 * a + 1) + (3 ^ a - 2) := by
    have h1 : 3 ^ (2 * a + 1) = 3 * 3 ^ a * 3 ^ a := by ring
    rw [h1]
    zify [show 1 ≤ 2 * 3 ^ a by omega, show 2 ≤ 3 ^ a by omega]
    ring
  rw [Units.val_pow_eq_pow_val, ← pow_mul, hexp, pow_add, pow_mul', hq, ← pow_add]
  congr 1
  omega

include hT hH in
theorem core_fix_U (ha : 1 ≤ a)
    (hsurj : ∀ t b c : K, ∃ v : ReeTag.G2.reeGamma K a,
      (v : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ β v = uIn hK t b c)
    (x b c : K) : β (uIn hK x b c) = uIn hK x b c := by
  obtain ⟨-, -, σ, -, hσ, -, -, -, hσ1, -, -, hbij, -⟩ :=
    small_Ree_field_power_identities a K hK
  choose μ hμ using core_first hK β hT hH ha hsurj
  have h0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have hσ' : ∀ y : K, smallReeSigma a y = σ y := fun y => (hσ y).symm
  have hadd : ∀ x y : K, μ (x + y) = μ x + μ y := by
    intro x y
    have e1 : uIn hK x 0 0 * uIn hK y 0 0 =
        uIn hK (x + y) 0 0 * uIn hK 0 (smallReeSigma a x * y) (smallReeSigma a x * y ^ 2) := by
      rw [uIn_mul, uIn_mul]
      congr 1 <;> ring
    have e2 := congrArg β e1
    rw [map_mul, map_mul, hμ, hμ, hμ, core_fix_U1 hK β hT hH ha hsurj, uIn_mul, uIn_mul] at e2
    have e3 := (uIn_inj hK e2).2.2
    linear_combination -e3
  have htorus : ∀ (s : Kˣ) (x : K),
      μ (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * x) = (s : K) ^ 3 ^ a * μ x := by
    intro s x
    have e1 := congrArg β (hIn_conj_uIn hK s x 0 0)
    rw [map_mul, map_mul, map_inv, core_fix_torus hK β hT hH, hμ, hIn_conj_uIn] at e1
    simp only [mul_zero] at e1
    rw [hμ] at e1
    exact (uIn_inj hK e1).2.2.symm
  have hform : ∀ y : K, μ y = y ^ (3 * 3 ^ a + 2) * μ 1 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have := hadd 0 0
      rw [add_zero] at this
      rw [zero_pow (by omega), zero_mul]
      linear_combination -this
    · obtain ⟨s, hs0⟩ := hbij.2 (Units.mk0 y hy)
      have hs : s ^ (2 * 3 ^ a - 1) = Units.mk0 y hy := hs0
      have hsy : ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) = y := by rw [hs, Units.val_mk0]
      have e1 := htorus s 1
      rw [mul_one, hsy] at e1
      rw [e1, ← hsy, pow_two_mul_sub_one_pow hK ha s]
  obtain ⟨y, hy⟩ : ∃ y : K, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ1 ha (RingEquiv.ext fun x => h x)
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hy (map_one σ)
  have h3 : (3 : K) = 0 := three_eq_zero_of_charP
  have f1 : (y + 1) ^ (3 * 3 ^ a + 2) = (σ y + 1) * (y + 1) ^ 2 := by
    rw [pow_add, ← hσ, map_add, map_one]
  have f2 : y ^ (3 * 3 ^ a + 2) = σ y * y ^ 2 := by rw [pow_add, ← hσ]
  have hkey : μ 1 * ((y - 1) * (2 * (σ y - y))) = 0 := by
    have e1 := hadd y 1
    rw [hform (y + 1), hform y, f1, f2] at e1
    linear_combination e1 + (-(μ 1) * (y ^ 2 + σ y)) * h3
  have h2' : (2 : K) ≠ 0 := two_ne_zero_of_charP
  have hμ1 : μ 1 = 0 := by
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exfalso
      rcases mul_eq_zero.1 h with h' | h'
      · exact hy1 (sub_eq_zero.1 h')
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact h2' h''
        · exact hy (sub_eq_zero.1 h'')
  have e1 : uIn hK x b c = uIn hK x 0 0 * uIn hK 0 b c := by
    rw [uIn_mul]
    congr 1 <;> ring
  rw [e1, map_mul, hμ, core_fix_U1 hK β hT hH ha hsurj, hform, hμ1, mul_zero]

end Core

end CFSG.ComponentClassification.LiteratureLocal.SmallRee
