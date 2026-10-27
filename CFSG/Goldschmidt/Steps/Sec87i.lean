module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.Sec85c
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec87g
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem card_le_four_pow {B : Subgroup G} (hB : Nat.card B ≤ 4) :
    ∀ n : ℕ, ∀ X : Subgroup G, (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      (∀ y ∈ X, y ^ (2 ^ n) = 1) → (∀ y ∈ X, y ^ 2 = 1 → y ∈ B) → Nat.card X ≤ 4 ^ n := by
  intro n
  induction n with
  | zero =>
    intro X _ hX _
    have : X = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (by simpa using hX y hy)
    rw [this, Subgroup.card_bot]
    norm_num
  | succ n ih =>
    intro X hXab hX hXB
    let φ : X →* G :=
      { toFun := fun y => (y : G) ^ 2
        map_one' := by simp
        map_mul' := fun y z => by
          simp only [Subgroup.coe_mul]
          exact (Commute.mul_pow (hXab _ y.2 _ z.2) 2) }
    have hR : φ.range ≤ X := by
      rintro _ ⟨y, rfl⟩
      exact X.pow_mem y.2 2
    have h1 : Nat.card φ.range ≤ 4 ^ n := by
      refine ih φ.range (fun x hx y hy => hXab x (hR hx) y (hR hy)) ?_
        fun y hy hy2 => hXB y (hR hy) hy2
      rintro _ ⟨y, rfl⟩
      show ((y : G) ^ 2) ^ (2 ^ n) = 1
      rw [← pow_mul, ← pow_succ']
      exact hX y y.2
    have h2 : Nat.card φ.ker ≤ 4 := by
      refine le_trans ?_ hB
      refine Nat.card_le_card_of_injective (fun y => ⟨(y : X), hXB _ (y : X).2 y.2⟩)
        fun y z hyz => Subtype.ext (Subtype.ext (congrArg (fun w : B => (w : G)) hyz))
    have h3 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h3
    calc Nat.card X = Nat.card φ.ker * Nat.card φ.range := h3.symm
      _ ≤ 4 * 4 ^ n := Nat.mul_le_mul h2 h1
      _ = 4 ^ (n + 1) := (pow_succ' 4 n).symm

omit [Finite G] in
theorem mem_zpowers_pow_of_sq_eq_one {g t : G} {n : ℕ} (hg : orderOf g = 2 ^ (n + 1))
    (ht : t ∈ Subgroup.zpowers g) (ht2 : t ^ 2 = 1) :
    t ∈ Subgroup.zpowers (g ^ (2 ^ n)) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h1 : g ^ (k * 2) = 1 := by
    rw [zpow_mul, ← ht2]
    norm_cast
  rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h1
  have h2 : ((2 : ℤ) ^ n) ∣ k := by
    have h3 : ((2 : ℤ) ^ n * 2) ∣ k * 2 := by
      have := h1
      push_cast [pow_succ] at this
      exact this
    exact (mul_dvd_mul_iff_right two_ne_zero).mp h3
  obtain ⟨l, rfl⟩ := h2
  refine Subgroup.mem_zpowers_iff.mpr ⟨l, ?_⟩
  rw [zpow_mul]
  norm_cast

theorem card_eq_exponent_sq (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hAD : A ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hC2 : ∀ u ∈ ⁅(S : Subgroup G), (S : Subgroup G)⁆, u ^ 2 = 1 → u ∈ A)
    (hab : IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G)) :
    Nat.card (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) =
      Monoid.exponent (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := ⁅(S : Subgroup G), (S : Subgroup G)⁆ with hD
  have hDS : D ≤ S := commutator_self_le _
  have hDp : IsPGroup 2 D := S.isPGroup'.to_le hDS
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hset
  obtain ⟨k, hk⟩ := hDp.exists_card_eq
  have hed : Monoid.exponent D ∣ 2 ^ k := hk ▸ Group.exponent_dvd_nat_card
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hed
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Monoid.pow_exponent_eq_one (⟨a, hAD ha⟩ : D)
    rw [hm, pow_zero, pow_one] at this
    exact ha1 (congrArg Subtype.val this)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hexpD : ∀ y ∈ D, y ^ (2 ^ (n + 1)) = 1 := fun y hy => by
    have := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : D)
    rw [hm] at this
    simpa using congrArg Subtype.val this
  have hup : Nat.card D ≤ 4 ^ (n + 1) :=
    card_le_four_pow (B := A) h4.le (n + 1) D hDab hexpD fun y hy hy2 => hC2 y hy hy2
  obtain ⟨g, hgD, hg⟩ : ∃ g ∈ D, g ^ (2 ^ n) ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hdvd : Monoid.exponent D ∣ 2 ^ n := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => Subtype.ext (by simpa using hall y y.2)
    rw [hm] at hdvd
    exact absurd ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd) (by omega)
  have hw2 : (g ^ (2 ^ n)) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact hexpD g hgD
  have hwA : g ^ (2 ^ n) ∈ A := hC2 _ (D.pow_mem hgD _) hw2
  obtain ⟨x, hxS, hxaA, hxa⟩ := exists_mem_normalizer_sylow hset h4 ha ha1
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_commutator hxS
  have hxxD : x * x ∈ Subgroup.normalizer (D : Set G) := Subgroup.mul_mem _ hxD hxD
  have hxA : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.inv_mem _ (normalizer_le_normalizer hset hxS)
  have hxC : x⁻¹ ∉ Subgroup.centralizer (A : Set G) := fun h => hxa (by
    have := conj_eq_of_mem_centralizer h ha
    simpa using this)
  have hσ := (conj_conj_eq_mul hset h4 hxA hxC ha ha1).2
  simp only [inv_inv] at hσ
  have hx2 : (x * x)⁻¹ * a * (x * x) = a * (x⁻¹ * a * x) := by
    rw [← hσ]
    group
  obtain ⟨g₁, hg₁D, hg₁⟩ : ∃ g₁ ∈ D, g₁ ^ (2 ^ n) = a := by
    rcases mem_four hset.elem h4 ha hxaA hwA ha1 (by simpa using conj_ne_one (n := x⁻¹) ha1)
      (Ne.symm hxa) with h | h | h | h
    · exact absurd h hg
    · exact ⟨g, hgD, h⟩
    · refine ⟨x * g * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxD g).mp hgD, ?_⟩
      rw [conj_pow, h]
      group
    · refine ⟨(x * x) * g * (x * x)⁻¹, (Subgroup.mem_normalizer_iff.mp hxxD g).mp hgD, ?_⟩
      rw [conj_pow, h, ← hx2]
      group
  set g₂ := x⁻¹ * g₁ * x with hg₂
  have hg₂D : g₂ ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxD) g₁).mp hg₁D
  have hg₂pow : g₂ ^ (2 ^ n) = x⁻¹ * a * x := by
    rw [hg₂, show x⁻¹ * g₁ * x = x⁻¹ * g₁ * x⁻¹⁻¹ by rw [inv_inv], conj_pow, hg₁, inv_inv]
  have hord₁ : orderOf g₁ = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hg₁]; exact ha1) (hexpD g₁ hg₁D)
  have hord₂ : orderOf g₂ = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hg₂pow]; simpa using conj_ne_one (n := x⁻¹) ha1)
      (hexpD g₂ hg₂D)
  have hz2 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 a ha) ha1]
  have hxa1 : x⁻¹ * a * x ≠ 1 := by simpa using conj_ne_one (n := x⁻¹) ha1
  have hz2' : Nat.card (Subgroup.zpowers (x⁻¹ * a * x)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hset.elem.2 _ hxaA) hxa1]
  have hbot : Subgroup.zpowers g₁ ⊓ Subgroup.zpowers g₂ = ⊥ := by
    refine inf_eq_bot_of_involutions (hDp.to_le (Subgroup.zpowers_le.mpr hg₁D))
      (fun t ht ht2 => ?_) (fun t ht ht2 => ?_) (Ne.symm hxa)
    · have := mem_zpowers_pow_of_sq_eq_one hord₁ ht ht2
      rw [hg₁] at this
      exact mem_two hz2 (Subgroup.mem_zpowers a) ha1 this
    · have := mem_zpowers_pow_of_sq_eq_one hord₂ ht ht2
      rw [hg₂pow] at this
      exact mem_two hz2' (Subgroup.mem_zpowers _) hxa1 this
  have hlow := card_mul_card_le (Subgroup.zpowers_le.mpr hg₁D) (Subgroup.zpowers_le.mpr hg₂D)
    hbot
  rw [Nat.card_zpowers, Nat.card_zpowers, hord₁, hord₂] at hlow
  rw [hm]
  have e : (2 ^ (n + 1)) ^ 2 = 4 ^ (n + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [e]
  refine le_antisymm hup ?_
  calc 4 ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) := by rw [← e, sq]
    _ ≤ Nat.card D := hlow

end CFSG.Goldschmidt.Sec8
