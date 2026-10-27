module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup

section Counting

variable {F : Type*} [Group F]

theorem e6fix_card_le_pow_of_exponent [Finite F] {b : ℕ}
    (hb : ∀ E : Subgroup F, (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      Nat.card E ≤ b) :
    ∀ (m : ℕ) (A : Subgroup F), (∀ a ∈ A, ∀ c ∈ A, a * c = c * a) →
      (∀ a ∈ A, a ^ (2 ^ m) = 1) → Nat.card A ≤ b ^ m := by
  intro m
  induction m with
  | zero =>
    intro A _ hA
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 fun a ha => by
      simpa using hA a ha
    rw [hbot, Subgroup.card_bot]
    simp
  | succ m ih =>
    intro A hcomm hA
    let φ : ↥A →* ↥A :=
      { toFun := fun x => x ^ 2
        map_one' := one_pow 2
        map_mul' := fun x y =>
          (show Commute x y from Subtype.ext (hcomm x x.2 y y.2)).mul_pow 2 }
    have hker : Nat.card φ.ker ≤ b := by
      have h1 : Nat.card (φ.ker.map A.subtype) ≤ b := by
        apply hb
        · rintro _ ⟨x, hx, rfl⟩
          have : (x : ↥A) ^ 2 = 1 := hx
          simpa [pow_two] using congrArg Subtype.val this
        · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          exact hcomm x x.2 y y.2
      rwa [Subgroup.card_map_of_injective A.subtype_injective] at h1
    have hrange : Nat.card φ.range ≤ b ^ m := by
      have h1 : Nat.card (φ.range.map A.subtype) ≤ b ^ m := by
        apply ih
        · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩
          exact hcomm _ (x ^ 2).2 _ (y ^ 2).2
        · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
          have h2 : ((x : F) ^ 2) ^ (2 ^ m) = 1 := by
            rw [← pow_mul, ← pow_succ']
            exact hA x x.2
          exact h2
      rwa [Subgroup.card_map_of_injective A.subtype_injective] at h1
    have h3 := Subgroup.card_ker_mul_card_range φ
    calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := h3.symm
      _ ≤ b * b ^ m := Nat.mul_le_mul hker hrange
      _ = b ^ (m + 1) := by ring

end Counting

section Extraspecial

variable {N : Type*} [Group N] [Finite N]

theorem e6fix_card_le_two_mul_card_centralizer {z : N} (hz : ∀ n : N, n * z = z * n)
    (hz2 : z * z = 1) (hsq : ∀ n : N, n * n = 1 ∨ n * n = z)
    (hcomm : ∀ n m : N, n * m * n⁻¹ * m⁻¹ = 1 ∨ n * m * n⁻¹ * m⁻¹ = z) (g : N) :
    Nat.card N ≤ 2 * Nat.card (centralizer ({g} : Set N)) := by
  have hZcen : zpowers z ≤ center N :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun n => hz n)
  have hZcard : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two, hz2]))
  have hbound : ∀ A : Subgroup N, A ≤ zpowers z → (∀ a ∈ A, a * a = 1) →
      Nat.card A ≤ 2 ^ 1 := fun A hA _ =>
    (Subgroup.card_le_of_le hA).trans (by simpa using hZcard)
  have hsqZ : ∀ e : N, e * e ∈ zpowers z := fun e => by
    rcases hsq e with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers z
  have hcommZ : ∀ e f : N, e * f * e⁻¹ * f⁻¹ ∈ zpowers z := fun e f => by
    rcases hcomm e f with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers z
  have hTop : CentralLift (zpowers z) ⊤ 1 :=
    { central := hZcen
      le := le_top
      sq_mem := fun e _ => hsqZ e
      comm_mem := fun e _ f _ => hcommZ e f
      bound := hbound }
  have hC := CentralLift.card_le_mul_card_inf_centralizer hTop (D := ⊤) le_rfl
    (x := g) (Subgroup.mem_top g)
  rw [top_inf_eq, Subgroup.card_top] at hC
  simpa using hC

end Extraspecial

section Centralizer

theorem e6fix_card_centralizer_conj_eq {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  refine Nat.card_congr
    { toFun := fun x => ⟨g * x * g⁻¹, ?_⟩
      invFun := fun y => ⟨g⁻¹ * y * g, ?_⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have h1 := mem_centralizer_singleton_iff.1 x.2
    refine mem_centralizer_singleton_iff.2 ?_
    calc g * (x : G) * g⁻¹ * (g * a * g⁻¹) = g * ((x : G) * a) * g⁻¹ := by group
      _ = g * (a * (x : G)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * (g * (x : G) * g⁻¹) := by group
  · have h1 := mem_centralizer_singleton_iff.1 y.2
    refine mem_centralizer_singleton_iff.2 ?_
    calc g⁻¹ * (y : G) * g * a = g⁻¹ * ((y : G) * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * (y : G)) * g := by rw [h1]
      _ = a * (g⁻¹ * (y : G) * g) := by group

theorem e6fix_card_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : G) :
    Nat.card (centralizer ({e a} : Set H)) = Nat.card (centralizer ({a} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨e.symm y, ?_⟩
      invFun := fun x => ⟨e x, ?_⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  · have h1 := mem_centralizer_singleton_iff.1 y.2
    refine mem_centralizer_singleton_iff.2 ?_
    apply e.injective
    simpa using h1
  · have h1 := mem_centralizer_singleton_iff.1 x.2
    refine mem_centralizer_singleton_iff.2 ?_
    rw [← map_mul, ← map_mul, h1]

end Centralizer

section Sylow

open scoped Pointwise

variable {O : Type*} [Group O]

theorem e6fix_exists_conj_of_two_bound [Finite O]
    (hO : ∀ T : Subgroup O, IsPGroup 2 T → Nat.card T ≤ 2) {x y : O} (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ g : O, g * x * g⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∀ z : O, z * z = 1 → z ≠ 1 → Nat.card (zpowers z) = 2 := fun z hz hz1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz) hz1
  have hsyl : ∀ z : O, z * z = 1 → z ≠ 1 → ∃ P : Sylow 2 O, (P : Subgroup O) = zpowers z :=
    fun z hz hz1 => by
      have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [hcard z hz hz1]; simp)
      refine ⟨⟨zpowers z, hp, fun {Q} hQ hle => ?_⟩, rfl⟩
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard z hz hz1]; exact hO Q hQ)).symm
  obtain ⟨P, hP⟩ := hsyl x hx hx1
  obtain ⟨Q, hQ⟩ := hsyl y hy hy1
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq O P Q
  refine ⟨g, ?_⟩
  have hmem : y ∈ ((g • P : Sylow 2 O) : Subgroup O) := by
    rw [hQ]
    exact mem_zpowers y
  rw [Sylow.coe_subgroup_smul, hP, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨s, hs, hsy⟩ := hmem
  have hsy' : g * s * g⁻¹ = y := hsy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · exfalso
    apply hy1
    rw [← hsy', zpow_mul, zpow_two, hx, one_zpow]
    group
  · rw [← hsy', zpow_add_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

end Sylow

section Unipotent

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem pow_two_pow_eq_one_of_finrank_le [CharP F 2] [FiniteDimensional F V] {k a : ℕ}
    (hk : Module.finrank F V ≤ 2 ^ k) (u : LinearMap.GeneralLinearGroup F V)
    (hu : u ^ (2 ^ a) = 1) : u ^ (2 ^ k) = 1 := by
  by_cases hV : Subsingleton V
  · have : Subsingleton (Module.End F V) :=
      ⟨fun f g => LinearMap.ext fun v => Subsingleton.elim _ _⟩
    exact Subsingleton.elim _ _
  · have : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
    have hchar : CharP (Module.End F V) 2 :=
      charP_of_injective_algebraMap (algebraMap F (Module.End F V)).injective 2
    set N : Module.End F V := (u : Module.End F V) - 1 with hN
    have hu' : (u : Module.End F V) = 1 + N := by rw [hN]; abel
    have hpow : ∀ j : ℕ, (u : Module.End F V) ^ (2 ^ j) = 1 + N ^ (2 ^ j) := fun j => by
      rw [hu', add_pow_char_pow_of_commute 2 j (Commute.one_left N), one_pow]
    have hNa : N ^ (2 ^ a) = 0 := by
      have h1 : (u : Module.End F V) ^ (2 ^ a) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hu]
        rfl
      rw [hpow a] at h1
      simpa using h1
    have hNf : N ^ Module.finrank F V = 0 := by
      have h := Module.End.ker_pow_le_ker_pow_finrank N (2 ^ a)
      rw [hNa, LinearMap.ker_zero] at h
      exact LinearMap.ker_eq_top.1 (top_le_iff.1 h)
    have hNk : N ^ (2 ^ k) = 0 := by
      have : N ^ (2 ^ k) = N ^ (2 ^ k - Module.finrank F V) * N ^ Module.finrank F V := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, hNf, mul_zero]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hpow k, hNk]
    simp

end Unipotent

end CFSG.EvenSporadicStandard.Induction.Hyp
