module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Fixed

variable {G : Type} [Group G]

theorem exists_fixed_of_odd_set [Finite G] {Ψ : Set G} (hΨ : Odd (Nat.card Ψ)) {a : G}
    (ha : a * a = 1) (hstab : ∀ y ∈ Ψ, a * y * a⁻¹ ∈ Ψ) : ∃ y ∈ Ψ, a * y * a⁻¹ = y := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let φ : ↥Ψ → ↥Ψ := fun y => ⟨a * (y : G) * a⁻¹, hstab y y.2⟩
  have hφφ : ∀ y, φ (φ y) = y := by
    intro y
    apply Subtype.ext
    show a * (a * (y : G) * a⁻¹) * a⁻¹ = (y : G)
    calc a * (a * (y : G) * a⁻¹) * a⁻¹ = (a * a) * (y : G) * (a⁻¹ * a⁻¹) := by group
      _ = (y : G) := by rw [ha, hainv, ha]; group
  let σ : Equiv.Perm ↥Ψ := ⟨φ, φ, hφφ, hφφ⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext y
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hφφ y)
  have : Fintype ↥Ψ := Fintype.ofFinite ↥Ψ
  have hodd : ¬ 2 ∣ Fintype.card ↥Ψ := by
    rw [← Nat.card_eq_fintype_card]
    exact hΨ.not_two_dvd_nat
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem mem_normalizer_closure_of_conj [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conjSub_le ?_
  rintro _ ⟨y, hy, rfl⟩
  change g * y * g⁻¹ ∈ Subgroup.closure s
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihx

end Fixed

section FuseEngine

variable {G : Type} [Group G] [Finite G] {K K' J : Subgroup G} {S : Sylow 2 G} {z t a : G}

theorem s_exists_x1_of
    (hex : ∃ t₀ ∈ J, t₀ * z * t₀⁻¹ = z * t ∧ t₀ * t * t₀⁻¹ = t) (hzJ : IsUniqueInvolution J t)
    (hA : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J)
    (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t = t * a) :
    ∃ x ∈ J, a * x = x * a ∧ x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t := by
  have ht2 : t * t = 1 := hzJ.sq
  obtain ⟨t₀, ht₀J, hx₀z, hx₀t⟩ := hex
  have haz' : a⁻¹ * z * a = z := by
    calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
      _ = a⁻¹ * (a * z) := by rw [haz]
      _ = z := by group
  have hazt : a * (z * t) * a⁻¹ = z * t := by
    refine mul_inv_eq_iff_eq_mul.mpr ?_
    calc a * (z * t) = (a * z) * t := by group
      _ = (z * a) * t := by rw [haz]
      _ = z * (a * t) := by group
      _ = z * (t * a) := by rw [hat]
      _ = (z * t) * a := by group
  have hinv : t₀⁻¹ * (z * t) * t₀ = z := by
    calc t₀⁻¹ * (z * t) * t₀ = t₀⁻¹ * (t₀ * z * t₀⁻¹) * t₀ := by rw [hx₀z]
      _ = z := by group
  have hn : t₀⁻¹ ∈ Subgroup.normalizer (oddCoreOf J : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (J.inv_mem ht₀J))
  have hcommO : t₀⁻¹ * ⁅a, t₀⁆ * t₀ ∈ oddCoreOf J := by
    have := (Subgroup.mem_normalizer_iff.mp hn _).mp (hA.2.2.2 t₀ ht₀J)
    simpa using this
  have hO'odd : Odd (Nat.card ↥(oddCoreOf J ⊓ Subgroup.centralizer ({z} : Set G))) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hΨodd : Odd (Nat.card ↥((fun o => t₀ * o) ''
      ((oddCoreOf J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G))) := by
    rw [Nat.card_image_of_injective (mul_right_injective t₀)]
    exact hO'odd
  have hstab : ∀ y ∈ (fun o => t₀ * o) ''
      ((oddCoreOf J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G),
      a * y * a⁻¹ ∈ (fun o => t₀ * o) ''
        ((oddCoreOf J ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨o, ho, rfl⟩
    have hoJ : o ∈ oddCoreOf J := ho.1
    have hoz : o * z * o⁻¹ = z := by
      have e := Subgroup.mem_centralizer_singleton_iff.mp ho.2
      calc o * z * o⁻¹ = (z * o) * o⁻¹ := by rw [e]
        _ = z := by group
    have h2 : a * o * a⁻¹ ∈ oddCoreOf J :=
      (Subgroup.mem_normalizer_iff.mp hA.2.2.1 o).mp hoJ
    obtain ⟨o', ho'def⟩ : ∃ o' : G, o' = t₀⁻¹ * (a * (t₀ * o) * a⁻¹) := ⟨_, rfl⟩
    have hot : t₀ * o' = a * (t₀ * o) * a⁻¹ := by rw [ho'def]; group
    have hoe : o' = (t₀⁻¹ * ⁅a, t₀⁆ * t₀) * (a * o * a⁻¹) := by
      rw [ho'def, commutatorElement_def]
      group
    have ho'J : o' ∈ oddCoreOf J := by
      rw [hoe]
      exact (oddCoreOf J).mul_mem hcommO h2
    have hxz : (a * (t₀ * o) * a⁻¹) * z * (a * (t₀ * o) * a⁻¹)⁻¹ = z * t := by
      have e1 : (t₀ * o) * z * (t₀ * o)⁻¹ = z * t := by
        calc (t₀ * o) * z * (t₀ * o)⁻¹ = t₀ * (o * z * o⁻¹) * t₀⁻¹ := by group
          _ = z * t := by rw [hoz, hx₀z]
      calc (a * (t₀ * o) * a⁻¹) * z * (a * (t₀ * o) * a⁻¹)⁻¹
          = a * ((t₀ * o) * (a⁻¹ * z * a) * (t₀ * o)⁻¹) * a⁻¹ := by group
        _ = a * ((t₀ * o) * z * (t₀ * o)⁻¹) * a⁻¹ := by rw [haz']
        _ = a * (z * t) * a⁻¹ := by rw [e1]
        _ = z * t := hazt
    have ho'z : o' * z * o'⁻¹ = z := by
      have e : t₀ * (o' * z * o'⁻¹) * t₀⁻¹ = z * t := by
        calc t₀ * (o' * z * o'⁻¹) * t₀⁻¹ = (t₀ * o') * z * (t₀ * o')⁻¹ := by group
          _ = (a * (t₀ * o) * a⁻¹) * z * (a * (t₀ * o) * a⁻¹)⁻¹ := by rw [hot]
          _ = z * t := hxz
      calc o' * z * o'⁻¹ = t₀⁻¹ * (t₀ * (o' * z * o'⁻¹) * t₀⁻¹) * t₀ := by group
        _ = t₀⁻¹ * (z * t) * t₀ := by rw [e]
        _ = z := hinv
    exact ⟨o', ⟨ho'J, Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp ho'z)⟩, hot⟩
  obtain ⟨y, ⟨o₁, ho₁, rfl⟩, hfix⟩ := exists_fixed_of_odd_set hΨodd ha2 hstab
  have ho₁J : o₁ ∈ J := oddCoreOf_le_self J ho₁.1
  have ho₁z : o₁ * z * o₁⁻¹ = z := by
    have e := Subgroup.mem_centralizer_singleton_iff.mp ho₁.2
    calc o₁ * z * o₁⁻¹ = (z * o₁) * o₁⁻¹ := by rw [e]
      _ = z := by group
  have ho₁t : o₁ * t * o₁⁻¹ = t := by
    have e := hzJ.commute_of_mem ho₁J
    calc o₁ * t * o₁⁻¹ = (t * o₁) * o₁⁻¹ := by rw [e]
      _ = t := by group
  refine ⟨t₀ * o₁, J.mul_mem ht₀J ho₁J, mul_inv_eq_iff_eq_mul.mp hfix, ?_, ?_⟩
  · calc (t₀ * o₁) * z * (t₀ * o₁)⁻¹ = t₀ * (o₁ * z * o₁⁻¹) * t₀⁻¹ := by group
      _ = z * t := by rw [ho₁z, hx₀z]
  · calc (t₀ * o₁) * t * (t₀ * o₁)⁻¹ = t₀ * (o₁ * t * o₁⁻¹) * t₀⁻¹ := by group
      _ = t := by rw [ho₁t, hx₀t]

theorem s_exists_rho_a_of
    (hx : ∃ x ∈ J, a * x = x * a ∧ x * z * x⁻¹ = z * t ∧ x * t * x⁻¹ = t)
    (htor : ∃ r ∈ K, r ∈ (S : Subgroup G) ∧ r * t * r⁻¹ = z * t)
    (hzK : IsUniqueInvolution K z) (ht2 : t * t = 1)
    (hA : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    ∃ ρ : G, a * ρ = ρ * a ∧ ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z ∧
      ρ ∈ Subgroup.normalizer ((Subgroup.closure ({z, t, a} : Set G) : Subgroup G) : Set G) := by
  obtain ⟨x, hxJ, hax, hxz, hxt⟩ := hx
  obtain ⟨r, hrK, hrS, hrt⟩ := htor
  have hrM : r ∈ K ⊔ K' := Subgroup.mem_sup_left hrK
  have har : a * r = r * a := commutes_of_mem_centModOddCore S.isPGroup'
    (mem_centModOddCore_of_mem_centralizerModOdd hA) hA.1 hrM hrS
  have hrz : r * z * r⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr (hzK.commute_of_mem hrK).symm
  have hρz : (x * r) * z * (x * r)⁻¹ = z * t := by
    calc (x * r) * z * (x * r)⁻¹ = x * (r * z * r⁻¹) * x⁻¹ := by group
      _ = z * t := by rw [hrz, hxz]
  have hρt : (x * r) * t * (x * r)⁻¹ = z := by
    calc (x * r) * t * (x * r)⁻¹ = x * (r * t * r⁻¹) * x⁻¹ := by group
      _ = (x * z * x⁻¹) * (x * t * x⁻¹) := by rw [hrt]; group
      _ = z := by rw [hxz, hxt, mul_assoc, ht2, mul_one]
  have hρa : (x * r) * a * (x * r)⁻¹ = a := by
    refine mul_inv_eq_iff_eq_mul.mpr ?_
    calc (x * r) * a = x * (r * a) := by group
      _ = x * (a * r) := by rw [har]
      _ = (x * a) * r := by group
      _ = (a * x) * r := by rw [hax]
      _ = a * (x * r) := by group
  refine ⟨x * r, ?_, hρz, hρt, ?_⟩
  · calc a * (x * r) = (a * x) * r := by group
      _ = (x * a) * r := by rw [hax]
      _ = x * (a * r) := by group
      _ = x * (r * a) := by rw [har]
      _ = (x * r) * a := by group
  · refine mem_normalizer_closure_of_conj ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    · rw [hρz]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [hρt]
      exact Subgroup.subset_closure (by simp)
    · rw [hρa]
      exact Subgroup.subset_closure (by simp)

end FuseEngine

end CFSG.ClassicalInvolution.Asc77.T3CII
