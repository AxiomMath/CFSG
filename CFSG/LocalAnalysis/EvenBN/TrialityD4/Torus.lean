module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

section Actions

variable {X : Type*} [Group X]

@[expose] def ConjRegularOn (A U : Subgroup X) : Prop :=
  A ≤ normalizer (U : Set X) ∧
    ∀ g ∈ U, g ≠ 1 → ∀ g' ∈ U, g' ≠ 1 → ∃! a, a ∈ A ∧ a * g * a⁻¹ = g'

@[expose] def ConjTransitiveOn (A U : Subgroup X) : Prop :=
  A ≤ normalizer (U : Set X) ∧ ∀ g ∈ U, g ≠ 1 → ∀ g' ∈ U, g' ≠ 1 → ∃ a ∈ A, a * g * a⁻¹ = g'

@[expose] def ConjSemiregularOn (A U : Subgroup X) : Prop :=
  A ≤ normalizer (U : Set X) ∧ ∀ g ∈ U, g ≠ 1 → ∀ a ∈ A, a * g * a⁻¹ = g → a = 1

variable {A K : Type*} [Group A] [Field K] {x : K → X} (hx : ∀ a b, x (a + b) = x a * x b)

include hx in
theorem ne_zero_of_map_ne_one {k : K} (hk : x k ≠ 1) : k ≠ 0 := by
  rintro rfl
  exact hk (map_zero_of_add hx)

variable (φ : A →* X) (c : A →* Kˣ) (hφ : ∀ a k, φ a * x k * (φ a)⁻¹ = x ((c a : K) * k))
include hφ

theorem range_le_normalizer_of_scalar : φ.range ≤ normalizer (rangeSubgroup hx : Set X) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(c a : K) * k, (hφ a k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨(c a⁻¹ : K) * k, ?_⟩
    rw [← hφ, hk, map_inv]
    group

theorem conjTransitiveOn_of_surjective (hc : Function.Surjective c) :
    ConjTransitiveOn φ.range (rangeSubgroup hx) := by
  refine ⟨range_le_normalizer_of_scalar hx φ c hφ, ?_⟩
  rintro _ ⟨k, rfl⟩ hk _ ⟨k', rfl⟩ hk'
  have k0 := ne_zero_of_map_ne_one hx hk
  have k0' := ne_zero_of_map_ne_one hx hk'
  obtain ⟨a, ha⟩ := hc (Units.mk0 (k' / k) (div_ne_zero k0' k0))
  refine ⟨φ a, ⟨a, rfl⟩, ?_⟩
  rw [hφ, ha, Units.val_mk0, div_mul_cancel₀ _ k0]

theorem conjRegularOn_of_bijective (hxi : Function.Injective x) (hc : Function.Bijective c) :
    ConjRegularOn φ.range (rangeSubgroup hx) := by
  refine ⟨range_le_normalizer_of_scalar hx φ c hφ, ?_⟩
  intro g hg g1 g' hg' g1'
  obtain ⟨t, ht, htg⟩ := (conjTransitiveOn_of_surjective hx φ c hφ hc.2).2 g hg g1 g' hg' g1'
  refine ⟨t, ⟨ht, htg⟩, ?_⟩
  rintro t' ⟨⟨a', rfl⟩, ht'⟩
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨k, rfl⟩ := hg
  have k0 := ne_zero_of_map_ne_one hx g1
  rw [hφ] at htg ht'
  have hca : c a' = c a := Units.ext (mul_right_cancel₀ k0 (hxi (ht'.trans htg.symm)))
  rw [hc.1 hca]

theorem conjSemiregularOn_of_injective (hxi : Function.Injective x)
    (hc : Function.Injective c) : ConjSemiregularOn φ.range (rangeSubgroup hx) := by
  refine ⟨range_le_normalizer_of_scalar hx φ c hφ, ?_⟩
  rintro _ ⟨k, rfl⟩ hk _ ⟨a, rfl⟩ ha
  have k0 := ne_zero_of_map_ne_one hx hk
  rw [hφ] at ha
  have h1 : c a = 1 := Units.ext (mul_right_cancel₀ k0 ((hxi ha).trans (one_mul k).symm))
  rw [← map_one c] at h1
  rw [hc h1, map_one]

end Actions

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem card_units_Γ : Nat.card d.Γˣ = q ^ 3 - 1 := by
  rw [Nat.card_units, d.card_Γ]

theorem card_units_Γ₀ : Nat.card (d.Γ₀)ˣ = q - 1 := by
  rw [Nat.card_units, d.card_Γ₀]

include d in
theorem pow_three_sub_one : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have hq := d.two_le_q
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  rw [add_tsub_cancel_right, Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
  ring

theorem sq_injective {a b : d.Γ} (h : a ^ 2 = b ^ 2) : a = b :=
  frobenius_inj d.Γ 2 h

theorem units_eq_one_of_sq {μ : d.Γˣ} (h : μ ^ 2 = 1) : μ = 1 :=
  Units.ext (d.sq_injective (by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h, one_pow]))

theorem units₀_eq_one_of_sq {l : (d.Γ₀)ˣ} (h : l ^ 2 = 1) : l = 1 := by
  refine Units.ext (Subtype.ext (d.sq_injective ?_))
  have h' := congrArg (fun m : (d.Γ₀)ˣ => ((m : d.Γ₀) : d.Γ)) h
  simpa using h'

@[expose] def unitsIncl : (d.Γ₀)ˣ →* d.Γˣ := Units.map d.Γ₀.subtype.toMonoidHom

theorem coe_unitsIncl (l : (d.Γ₀)ˣ) : ((d.unitsIncl l : d.Γˣ) : d.Γ) = ((l : d.Γ₀) : d.Γ) :=
  rfl

theorem unitsIncl_injective : Function.Injective d.unitsIncl := fun _ _ h =>
  Units.ext (Subtype.ext (congrArg Units.val h))

@[expose] def σUnits : d.Γˣ →* d.Γˣ := Units.map d.σ.toMonoidHom

theorem coe_σUnits (μ : d.Γˣ) : ((d.σUnits μ : d.Γˣ) : d.Γ) = d.σ μ :=
  rfl

@[expose] def nmHom : d.Γ →* d.Γ₀ where
  toFun := d.nm
  map_one' := Subtype.ext (by simp [coe_fixedNorm])
  map_mul' a b := Subtype.ext (by simp only [coe_fixedNorm, map_mul, MulMemClass.coe_mul]; ring)

theorem nm_one : d.nm 1 = 1 :=
  d.nmHom.map_one

theorem nm_mul (a b : d.Γ) : d.nm (a * b) = d.nm a * d.nm b :=
  d.nmHom.map_mul a b

@[expose] def nmUnits : d.Γˣ →* (d.Γ₀)ˣ := Units.map d.nmHom

theorem coe_nmUnits (μ : d.Γˣ) : ((d.nmUnits μ : d.Γ₀ˣ) : d.Γ₀) = d.nm μ :=
  rfl

theorem coe_nm_eq_pow (c : d.Γ) : (d.nm c : d.Γ) = c ^ (1 + q + q ^ 2) := by
  change c * d.σ c * d.σ (d.σ c) = _
  rw [d.σ_apply (d.σ c), d.σ_apply c, ← pow_mul, pow_add, pow_add, pow_one, sq]

theorem ker_nmUnits :
    d.nmUnits.ker = (powMonoidHom (1 + q + q ^ 2) : d.Γˣ →* d.Γˣ).ker := by
  ext μ
  simp only [MonoidHom.mem_ker, powMonoidHom_apply, Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]
  rw [← d.coe_nm_eq_pow, ← d.coe_nmUnits, ← OneMemClass.coe_one d.Γ₀, Subtype.ext_iff]

theorem card_ker_nmUnits : Nat.card d.nmUnits.ker = q ^ 2 + q + 1 := by
  rw [d.ker_nmUnits, IsCyclic.card_powMonoidHom_ker, d.card_units_Γ, d.pow_three_sub_one,
    show 1 + q + q ^ 2 = q ^ 2 + q + 1 by ring, Nat.gcd_eq_right (dvd_mul_left _ _)]

theorem nmUnits_surjective : Function.Surjective d.nmUnits := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [d.card_ker_nmUnits, d.card_units_Γ, d.card_units_Γ₀, d.pow_three_sub_one,
    Nat.mul_div_cancel_left _ (by have := d.two_le_q; omega)]

theorem mem_J {g : X} : g ∈ d.J ↔ ∃ h, d.torus h = g :=
  MonoidHom.mem_range

theorem torus_mem_J (h : (d.Γ₀)ˣ × d.Γˣ) : d.torus h ∈ d.J :=
  ⟨h, rfl⟩

theorem mem_centralizer_rangeSubgroup_iff {A : Type*} [AddGroup A] {x : A → X}
    (hx : ∀ a b, x (a + b) = x a * x b) {t : X} :
    t ∈ centralizer (rangeSubgroup hx : Set X) ↔ ∀ a, t * x a * t⁻¹ = x a := by
  rw [mem_centralizer_iff]
  constructor
  · intro h a
    rw [← h (x a) ⟨a, rfl⟩, mul_inv_cancel_right]
  · rintro h _ ⟨a, rfl⟩
    exact (mul_inv_eq_iff_eq_mul.1 (h a)).symm

omit [Group X] in
theorem forall_map_mul_eq_iff {K : Type*} [Field K] {x : K → X} (hxi : Function.Injective x)
    {c : K} : (∀ a, x (c * a) = x a) ↔ c = 1 := by
  constructor
  · intro h
    simpa using hxi (h 1)
  · rintro rfl a
    rw [one_mul]

theorem torus_mem_J₁_iff (h : (d.Γ₀)ˣ × d.Γˣ) : d.torus h ∈ d.J₁ ↔ h.2 = 1 := by
  rw [J₁, mem_inf, and_iff_right (d.torus_mem_J h), U₁, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₁]
  rw [forall_map_mul_eq_iff d.x₁_injective, Units.val_eq_one]

theorem torus_mem_J₂_iff (h : (d.Γ₀)ˣ × d.Γˣ) : d.torus h ∈ d.J₂ ↔ h.1 = 1 := by
  rw [J₂, mem_inf, and_iff_right (d.torus_mem_J h), U₂, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₂]
  rw [forall_map_mul_eq_iff d.x₂_injective, Units.val_eq_one]

theorem torus_mem_J₃_iff (h : (d.Γ₀)ˣ × d.Γˣ) :
    d.torus h ∈ d.J₃ ↔ ((h.1 : d.Γ₀) : d.Γ) * (h.2 : d.Γ) = 1 := by
  rw [J₃, mem_inf, and_iff_right (d.torus_mem_J h), U₃, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₃]
  rw [forall_map_mul_eq_iff d.x₃_injective]

theorem torus_mem_J₄_iff (h : (d.Γ₀)ˣ × d.Γˣ) :
    d.torus h ∈ d.J₄ ↔ ((h.1 : d.Γ₀) : d.Γ) * d.σ (h.2 : d.Γ) * d.σ (d.σ (h.2 : d.Γ)) = 1 := by
  rw [J₄, mem_inf, and_iff_right (d.torus_mem_J h), U₄, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₄]
  rw [forall_map_mul_eq_iff d.x₄_injective]

theorem torus_mem_J₅_iff (h : (d.Γ₀)ˣ × d.Γˣ) :
    d.torus h ∈ d.J₅ ↔ (h.1 : d.Γ₀) * d.nm (h.2 : d.Γ) = 1 := by
  rw [J₅, mem_inf, and_iff_right (d.torus_mem_J h), U₅, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₅]
  rw [forall_map_mul_eq_iff d.x₅_injective]

theorem torus_mem_J₆_iff (h : (d.Γ₀)ˣ × d.Γˣ) :
    d.torus h ∈ d.J₆ ↔ (h.1 : d.Γ₀) * (h.1 : d.Γ₀) * d.nm (h.2 : d.Γ) = 1 := by
  rw [J₆, mem_inf, and_iff_right (d.torus_mem_J h), U₆, mem_centralizer_rangeSubgroup_iff]
  simp_rw [d.torus_x₆]
  rw [forall_map_mul_eq_iff d.x₆_injective]

theorem mem_J_inf_iff {U : Subgroup X} {P : (d.Γ₀)ˣ × d.Γˣ → Prop}
    (hP : ∀ h, d.torus h ∈ d.J ⊓ centralizer (U : Set X) ↔ P h) {g : X} :
    g ∈ d.J ⊓ centralizer (U : Set X) ↔ ∃ h, d.torus h = g ∧ P h := by
  constructor
  · intro hg
    obtain ⟨h, rfl⟩ := d.mem_J.1 (mem_inf.1 hg).1
    exact ⟨h, rfl, (hP h).1 hg⟩
  · rintro ⟨h, rfl, hh⟩
    exact (hP h).2 hh

theorem mem_J₁ {g : X} : g ∈ d.J₁ ↔ ∃ h, d.torus h = g ∧ h.2 = 1 :=
  d.mem_J_inf_iff d.torus_mem_J₁_iff

theorem mem_J₂ {g : X} : g ∈ d.J₂ ↔ ∃ h, d.torus h = g ∧ h.1 = 1 :=
  d.mem_J_inf_iff d.torus_mem_J₂_iff

theorem J₁_eq_range : d.J₁ = (d.torus.comp (MonoidHom.inl _ _)).range := by
  ext g
  rw [mem_J₁, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl, h2⟩
    exact ⟨h.1, congrArg d.torus (Prod.ext rfl h2.symm)⟩
  · rintro ⟨l, rfl⟩
    exact ⟨(l, 1), rfl, rfl⟩

theorem J₂_eq_range : d.J₂ = (d.torus.comp (MonoidHom.inr _ _)).range := by
  ext g
  rw [mem_J₂, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl, h1⟩
    exact ⟨h.2, congrArg d.torus (Prod.ext h1.symm rfl)⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(1, m), rfl, rfl⟩

theorem yamada_three_five_one :
    (∀ g, g ∈ d.J₁ ↔ ∃ h, d.torus h = g ∧ h.2 = 1) ∧
      (∀ g, g ∈ d.J₂ ↔ ∃ h, d.torus h = g ∧ h.1 = 1) ∧
      IsCyclic d.J₁ ∧ Nat.card d.J₁ = q - 1 ∧ IsCyclic d.J₂ ∧ Nat.card d.J₂ = q ^ 3 - 1 := by
  have h₁ : Function.Injective (d.torus.comp (MonoidHom.inl (d.Γ₀)ˣ d.Γˣ)) :=
    d.torus_injective.comp fun a b h => congrArg Prod.fst h
  have h₂ : Function.Injective (d.torus.comp (MonoidHom.inr (d.Γ₀)ˣ d.Γˣ)) :=
    d.torus_injective.comp fun a b h => congrArg Prod.snd h
  refine ⟨fun g => d.mem_J₁, fun g => d.mem_J₂, ?_, ?_, ?_, ?_⟩
  · rw [J₁_eq_range]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · rw [J₁_eq_range, ← Nat.card_congr (MonoidHom.ofInjective h₁).toEquiv, d.card_units_Γ₀]
  · rw [J₂_eq_range]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · rw [J₂_eq_range, ← Nat.card_congr (MonoidHom.ofInjective h₂).toEquiv, d.card_units_Γ]

@[expose] def hA : (d.Γ₀)ˣ →* X :=
  d.torus.comp ((powMonoidHom 2).prod (d.unitsIncl.comp invMonoidHom))

@[expose] def hBCD : d.Γˣ →* X :=
  d.torus.comp ((invMonoidHom.comp d.nmUnits).prod (powMonoidHom 2))

theorem hA_apply (b : (d.Γ₀)ˣ) : d.hA b = d.torus (b ^ 2, d.unitsIncl b⁻¹) :=
  rfl

theorem hBCD_apply (b : d.Γˣ) : d.hBCD b = d.torus ((d.nmUnits b)⁻¹, b ^ 2) :=
  rfl

theorem mem_J₄ {g : X} : g ∈ d.J₄ ↔ ∃ h, d.torus h = g ∧
    ((h.1 : d.Γ₀) : d.Γ) * d.σ (h.2 : d.Γ) * d.σ (d.σ (h.2 : d.Γ)) = 1 :=
  d.mem_J_inf_iff d.torus_mem_J₄_iff

theorem mem_J₆ {g : X} : g ∈ d.J₆ ↔ ∃ h, d.torus h = g ∧
    (h.1 : d.Γ₀) * (h.1 : d.Γ₀) * d.nm (h.2 : d.Γ) = 1 :=
  d.mem_J_inf_iff d.torus_mem_J₆_iff

theorem J₄_eq_range_hA : d.J₄ = d.hA.range := by
  ext g
  rw [mem_J₄, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl, hh⟩
    set m : d.Γ := (h.2 : d.Γ) with hm
    set l : d.Γ := ((h.1 : d.Γ₀) : d.Γ) with hl
    have hl' : d.σ l = l := apply_coe_fixedSubfield _
    have m0 : m ≠ 0 := h.2.ne_zero
    have l0 : l ≠ 0 := ZeroMemClass.coe_eq_zero.not.2 h.1.ne_zero
    have hσσ0 : d.σ (d.σ m) ≠ 0 := by simpa using m0
    have hfix : d.σ m = m := by
      have h1 := congrArg d.σ hh
      rw [map_mul, map_mul, hl', d.σ_cube, map_one] at h1
      have h2 : l * d.σ (d.σ m) * m = l * d.σ (d.σ m) * d.σ m := by
        rw [h1, ← hh]
        ring
      exact (mul_left_cancel₀ (mul_ne_zero l0 hσσ0) h2).symm
    have hm0 : (⟨m, mem_fixedSubfield.2 hfix⟩ : d.Γ₀) ≠ 0 :=
      fun e => m0 (congrArg Subtype.val e)
    refine ⟨(Units.mk0 _ hm0)⁻¹, ?_⟩
    rw [hA_apply, inv_inv]
    refine congrArg d.torus (Prod.ext ?_ ?_)
    · refine Units.ext (Subtype.ext ?_)
      have hlm : l * (m * m) = 1 := by rw [← mul_assoc]; rwa [hfix, hfix] at hh
      have hl2 : l = (m * m)⁻¹ := eq_inv_of_mul_eq_one_left hlm
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0]
      push_cast
      rw [← hl, hl2]
      ring
    · exact Units.ext rfl
  · rintro ⟨b, rfl⟩
    refine ⟨(b ^ 2, d.unitsIncl b⁻¹), rfl, ?_⟩
    have hb : d.σ ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) = ((d.unitsIncl b⁻¹ : d.Γˣ) : d.Γ) :=
      apply_coe_fixedSubfield _
    simp only [hb]
    have b0 : ((b : d.Γ₀) : d.Γ) ≠ 0 := ZeroMemClass.coe_eq_zero.not.2 b.ne_zero
    simp only [coe_unitsIncl, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    push_cast
    field_simp

theorem sq_surjective_units (m : d.Γˣ) : ∃ b : d.Γˣ, b ^ 2 = m := by
  have hinj : Function.Injective (powMonoidHom 2 : d.Γˣ →* d.Γˣ) :=
    (injective_iff_map_eq_one _).2 fun _ hb => d.units_eq_one_of_sq hb
  exact Finite.injective_iff_surjective.1 hinj m

theorem J₆_eq_range_hBCD : d.J₆ = d.hBCD.range := by
  ext g
  rw [mem_J₆, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl, hh⟩
    obtain ⟨b, hb⟩ := d.sq_surjective_units h.2
    have hu : h.1 * h.1 * d.nmUnits h.2 = 1 := Units.ext hh
    rw [← hb, map_pow] at hu
    have h1 : h.1 * d.nmUnits b = 1 :=
      d.units₀_eq_one_of_sq (by rw [mul_pow, sq h.1]; exact hu)
    refine ⟨b, ?_⟩
    rw [hBCD_apply, hb, ← eq_inv_of_mul_eq_one_left h1]
  · rintro ⟨b, rfl⟩
    refine ⟨((d.nmUnits b)⁻¹, b ^ 2), rfl, ?_⟩
    have e : ((((d.nmUnits b)⁻¹ * (d.nmUnits b)⁻¹ * d.nmUnits (b ^ 2) : (d.Γ₀)ˣ)) : d.Γ₀) =
        1 := by
      rw [map_pow]
      group
      rfl
    simpa only [Units.val_mul, coe_nmUnits, Units.val_pow_eq_pow_val] using e

theorem pow_sub_one_Γ₀ (l : (d.Γ₀)ˣ) : l ^ (q - 1) = 1 := by
  rw [← d.card_units_Γ₀]
  exact pow_card_eq_one'

theorem range_pow_sub_one_eq_ker_nmUnits :
    (powMonoidHom (q - 1) : d.Γˣ →* d.Γˣ).range = d.nmUnits.ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨m, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, d.pow_sub_one_Γ₀]
  · rw [d.card_ker_nmUnits, IsCyclic.card_powMonoidHom_range, d.card_units_Γ,
      d.pow_three_sub_one, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (by have := d.two_le_q; omega)]

theorem J₀_eq_map : d.J₀ =
    (powMonoidHom (q - 1) : d.Γˣ →* d.Γˣ).range.map (d.torus.comp (MonoidHom.inr _ _)) := by
  ext g
  simp only [J₀, MonoidHom.mem_range, mem_map, MonoidHom.comp_apply, powMonoidHom_apply]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h.2 ^ (q - 1), ⟨h.2, rfl⟩, congrArg d.torus (Prod.ext ?_ rfl)⟩
    rw [MonoidHom.inr_apply, Prod.pow_fst, d.pow_sub_one_Γ₀]
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    refine ⟨(1, m), congrArg d.torus (Prod.ext ?_ rfl)⟩
    rw [Prod.pow_fst, one_pow, MonoidHom.inr_apply]

theorem J₂_inf_J₅_inf_J₆_eq_map :
    d.J₂ ⊓ d.J₅ ⊓ d.J₆ = d.nmUnits.ker.map (d.torus.comp (MonoidHom.inr _ _)) := by
  ext g
  rw [mem_inf, mem_inf, mem_map]
  constructor
  · rintro ⟨⟨h₂, h₅⟩, -⟩
    obtain ⟨h, rfl, h1⟩ := d.mem_J₂.1 h₂
    have hn := (d.torus_mem_J₅_iff h).1 h₅
    rw [h1, Units.val_one, one_mul] at hn
    exact ⟨h.2, Units.ext hn, congrArg d.torus (Prod.ext h1.symm rfl)⟩
  · rintro ⟨m, hm, rfl⟩
    have hn : d.nm (m : d.Γ) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hm)
    refine ⟨⟨(d.torus_mem_J₂_iff _).2 rfl, (d.torus_mem_J₅_iff _).2 ?_⟩,
      (d.torus_mem_J₆_iff _).2 ?_⟩
    · simp only [MonoidHom.inr_apply, Units.val_one, one_mul]
      exact hn
    · simp only [MonoidHom.inr_apply, Units.val_one, one_mul]
      exact hn

theorem yamada_three_five_four :
    d.J₀ = d.J₂ ⊓ d.J₅ ⊓ d.J₆ ∧ Nat.card d.J₀ = q ^ 2 + q + 1 := by
  have hinj : Function.Injective (d.torus.comp (MonoidHom.inr (d.Γ₀)ˣ d.Γˣ)) :=
    d.torus_injective.comp fun a b h => congrArg Prod.snd h
  refine ⟨?_, ?_⟩
  · rw [J₀_eq_map, J₂_inf_J₅_inf_J₆_eq_map, range_pow_sub_one_eq_ker_nmUnits]
  · rw [J₀_eq_map, range_pow_sub_one_eq_ker_nmUnits, Subgroup.card_map_of_injective hinj,
      d.card_ker_nmUnits]

theorem yamada_three_five_five :
    ConjRegularOn d.J₂ d.U₁ ∧ ConjRegularOn d.J₂ d.U₃ ∧ ConjRegularOn d.J₂ d.U₄ ∧
      ConjTransitiveOn d.J₂ d.U₅ ∧ ConjTransitiveOn d.J₂ d.U₆ ∧
      ConjRegularOn d.J₁ d.U₂ ∧ ConjRegularOn d.J₁ d.U₅ ∧ ConjRegularOn d.J₁ d.U₆ ∧
      ConjSemiregularOn d.J₁ d.U₃ ∧ ConjSemiregularOn d.J₁ d.U₄ := by
  have sq₀ : Function.Bijective (powMonoidHom 2 : (d.Γ₀)ˣ →* (d.Γ₀)ˣ) := by
    have hinj : Function.Injective (powMonoidHom 2 : (d.Γ₀)ˣ →* (d.Γ₀)ˣ) :=
      (injective_iff_map_eq_one _).2 fun _ hl => d.units₀_eq_one_of_sq hl
    exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have c₄ : Function.Bijective (d.σUnits * d.σUnits.comp d.σUnits) := by
    have hinj : Function.Injective (d.σUnits * d.σUnits.comp d.σUnits) := by
      refine (injective_iff_map_eq_one _).2 fun m hm => ?_
      have h0 : d.σ (m : d.Γ) * d.σ (d.σ (m : d.Γ)) = 1 := congrArg Units.val hm
      have h1 : (m : d.Γ) * d.σ (m : d.Γ) = 1 :=
        d.σ.injective (by rw [map_mul, map_one, h0])
      have h2 : d.σ (d.σ (m : d.Γ)) = (m : d.Γ) := by
        have e : d.σ (m : d.Γ) = (m : d.Γ)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [e, map_inv₀, e, inv_inv]
      have h3 : d.σ (m : d.Γ) = (m : d.Γ) := by
        conv_rhs => rw [← d.σ_cube (m : d.Γ), h2]
      refine d.units_eq_one_of_sq (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
      nth_rewrite 2 [← h3]
      exact h1
    exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have r₂ := d.J₂_eq_range
  have r₁ := d.J₁_eq_range
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₂]
    exact conjRegularOn_of_bijective d.x₁_add _ (MonoidHom.id _) (fun m k => d.torus_x₁ _ k)
      d.x₁_injective Function.bijective_id
  · rw [r₂]
    refine conjRegularOn_of_bijective d.x₃_add _ (MonoidHom.id _) (fun m k => ?_)
      d.x₃_injective Function.bijective_id
    rw [MonoidHom.comp_apply, d.torus_x₃]
    simp
  · rw [r₂]
    refine conjRegularOn_of_bijective d.x₄_add _ _ (fun m k => ?_) d.x₄_injective c₄
    rw [MonoidHom.comp_apply, d.torus_x₄]
    simp [coe_σUnits, mul_assoc]
  · rw [r₂]
    refine conjTransitiveOn_of_surjective d.x₅_add _ d.nmUnits (fun m k => ?_)
      d.nmUnits_surjective
    rw [MonoidHom.comp_apply, d.torus_x₅]
    simp [coe_nmUnits]
  · rw [r₂]
    refine conjTransitiveOn_of_surjective d.x₆_add _ d.nmUnits (fun m k => ?_)
      d.nmUnits_surjective
    rw [MonoidHom.comp_apply, d.torus_x₆]
    simp [coe_nmUnits]
  · rw [r₁]
    exact conjRegularOn_of_bijective d.x₂_add _ (MonoidHom.id _) (fun l k => d.torus_x₂ _ k)
      d.x₂_injective Function.bijective_id
  · rw [r₁]
    refine conjRegularOn_of_bijective d.x₅_add _ (MonoidHom.id _) (fun l k => ?_)
      d.x₅_injective Function.bijective_id
    rw [MonoidHom.comp_apply, d.torus_x₅]
    simp [d.nm_one]
  · rw [r₁]
    refine conjRegularOn_of_bijective d.x₆_add _ (powMonoidHom 2) (fun l k => ?_)
      d.x₆_injective sq₀
    rw [MonoidHom.comp_apply, d.torus_x₆]
    simp [d.nm_one, sq]
  · rw [r₁]
    refine conjSemiregularOn_of_injective d.x₃_add _ d.unitsIncl (fun l k => ?_)
      d.x₃_injective d.unitsIncl_injective
    rw [MonoidHom.comp_apply, d.torus_x₃]
    simp [coe_unitsIncl]
  · rw [r₁]
    refine conjSemiregularOn_of_injective d.x₄_add _ d.unitsIncl (fun l k => ?_)
      d.x₄_injective d.unitsIncl_injective
    rw [MonoidHom.comp_apply, d.torus_x₄]
    simp [coe_unitsIncl]

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
