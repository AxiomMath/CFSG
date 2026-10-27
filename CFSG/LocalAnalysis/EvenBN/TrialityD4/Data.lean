module

public import Mathlib.GroupTheory.Sylow
public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

section Field

variable {Γ : Type*} [Field Γ] (σ : Γ ≃+* Γ)

@[expose] def fixedSubfield : Subfield Γ :=
  RingHom.eqLocusField σ.toRingHom (RingHom.id Γ)

variable {σ}

theorem mem_fixedSubfield {c : Γ} : c ∈ fixedSubfield σ ↔ σ c = c :=
  Iff.rfl

theorem apply_coe_fixedSubfield (c : fixedSubfield σ) : σ (c : Γ) = c :=
  c.2

variable (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem trace_mem_fixedSubfield (c : Γ) : c + σ c + σ (σ c) ∈ fixedSubfield σ := by
  rw [mem_fixedSubfield, map_add, map_add, hσ]
  ring

theorem norm_mem_fixedSubfield (c : Γ) : c * σ c * σ (σ c) ∈ fixedSubfield σ := by
  rw [mem_fixedSubfield, map_mul, map_mul, hσ]
  ring

@[expose] def fixedTrace (c : Γ) : fixedSubfield σ :=
  ⟨c + σ c + σ (σ c), trace_mem_fixedSubfield hσ c⟩

@[expose] def fixedNorm (c : Γ) : fixedSubfield σ :=
  ⟨c * σ c * σ (σ c), norm_mem_fixedSubfield hσ c⟩

theorem coe_fixedTrace (c : Γ) : (fixedTrace hσ c : Γ) = c + σ c + σ (σ c) :=
  rfl

theorem coe_fixedNorm (c : Γ) : (fixedNorm hσ c : Γ) = c * σ c * σ (σ c) :=
  rfl

end Field

section Words

variable {X : Type*} [Group X] {Γ Γ₀ : Type*}

@[expose] def sixProd (x₁ : Γ → X) (x₂ : Γ₀ → X) (x₃ x₄ : Γ → X) (x₅ x₆ : Γ₀ → X)
    (a : Γ × Γ₀ × Γ × Γ × Γ₀ × Γ₀) : X :=
  x₁ a.1 * x₂ a.2.1 * x₃ a.2.2.1 * x₄ a.2.2.2.1 * x₅ a.2.2.2.2.1 * x₆ a.2.2.2.2.2

@[expose] def sixClosure (x₁ : Γ → X) (x₂ : Γ₀ → X) (x₃ x₄ : Γ → X) (x₅ x₆ : Γ₀ → X) :
    Subgroup X :=
  closure (Set.range x₁ ∪ Set.range x₂ ∪ Set.range x₃ ∪ Set.range x₄ ∪ Set.range x₅ ∪
    Set.range x₆)

theorem sixProd_mem_sixClosure (x₁ : Γ → X) (x₂ : Γ₀ → X) (x₃ x₄ : Γ → X) (x₅ x₆ : Γ₀ → X)
    (a : Γ × Γ₀ × Γ × Γ × Γ₀ × Γ₀) :
    sixProd x₁ x₂ x₃ x₄ x₅ x₆ a ∈ sixClosure x₁ x₂ x₃ x₄ x₅ x₆ := by
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact subset_closure (by simp)

variable {A : Type*} [AddGroup A] {x : A → X} (hx : ∀ a b, x (a + b) = x a * x b)
include hx

theorem map_zero_of_add : x 0 = 1 := by
  have h := hx 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_neg_of_add (a : A) : x (-a) = (x a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hx, neg_add_cancel, map_zero_of_add hx]

@[expose] def rangeSubgroup : Subgroup X where
  carrier := Set.range x
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, hx a b⟩
  one_mem' := ⟨0, map_zero_of_add hx⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, map_neg_of_add hx a⟩

theorem mem_rangeSubgroup {g : X} : g ∈ rangeSubgroup hx ↔ ∃ a, x a = g :=
  Iff.rfl

end Words

theorem odd_sub_one_of_even {n : ℕ} (hn : Even n) (h : 1 ≤ n) : Odd (n - 1) := by
  obtain ⟨k, rfl⟩ := hn
  exact ⟨k - 1, by omega⟩

structure TrialityD4Data (X : Type*) [Group X] (q : ℕ) where
  Γ : Type
  [instField : Field Γ]
  [instFinite : Finite Γ]
  [instCharP : CharP Γ 2]
  two_pow : ∃ f, 1 ≤ f ∧ q = 2 ^ f
  card_Γ : Nat.card Γ = q ^ 3
  σ : Γ ≃+* Γ
  σ_apply : ∀ c, σ c = c ^ q
  σ_cube : ∀ c, σ (σ (σ c)) = c
  card_Γ₀ : Nat.card (fixedSubfield σ) = q
  x₁ : Γ → X
  x₂ : fixedSubfield σ → X
  x₃ : Γ → X
  x₄ : Γ → X
  x₅ : fixedSubfield σ → X
  x₆ : fixedSubfield σ → X
  x₁_add : ∀ a b, x₁ (a + b) = x₁ a * x₁ b
  x₂_add : ∀ a b, x₂ (a + b) = x₂ a * x₂ b
  x₃_add : ∀ a b, x₃ (a + b) = x₃ a * x₃ b
  x₄_add : ∀ a b, x₄ (a + b) = x₄ a * x₄ b
  x₅_add : ∀ a b, x₅ (a + b) = x₅ a * x₅ b
  x₆_add : ∀ a b, x₆ (a + b) = x₆ a * x₆ b
  x₁_injective : Function.Injective x₁
  x₂_injective : Function.Injective x₂
  x₃_injective : Function.Injective x₃
  x₄_injective : Function.Injective x₄
  x₅_injective : Function.Injective x₅
  x₆_injective : Function.Injective x₆
  comm₁₂ : ∀ a b, ⁅x₁ a, x₂ b⁆ =
    x₃ (a * b) * x₄ (σ a * σ (σ a) * b) * x₅ (fixedNorm σ_cube a * b)
  comm₁₃ : ∀ a b, ⁅x₁ a, x₃ b⁆ =
    x₄ (σ a * σ (σ b) + σ (σ a) * σ b) * x₅ (fixedTrace σ_cube (a * σ a * σ (σ b))) *
      x₆ (fixedTrace σ_cube (a * σ b * σ (σ b)))
  comm₁₄ : ∀ a b, ⁅x₁ a, x₄ b⁆ = x₅ (fixedTrace σ_cube (a * b))
  comm₂₅ : ∀ a b, ⁅x₂ a, x₅ b⁆ = x₆ (a * b)
  comm₃₄ : ∀ a b, ⁅x₃ a, x₄ b⁆ = x₆ (fixedTrace σ_cube (a * b))
  commute₁₅ : ∀ a b, Commute (x₁ a) (x₅ b)
  commute₁₆ : ∀ a b, Commute (x₁ a) (x₆ b)
  commute₂₃ : ∀ a b, Commute (x₂ a) (x₃ b)
  commute₂₄ : ∀ a b, Commute (x₂ a) (x₄ b)
  commute₂₆ : ∀ a b, Commute (x₂ a) (x₆ b)
  commute₃₅ : ∀ a b, Commute (x₃ a) (x₅ b)
  commute₃₆ : ∀ a b, Commute (x₃ a) (x₆ b)
  commute₄₅ : ∀ a b, Commute (x₄ a) (x₅ b)
  commute₄₆ : ∀ a b, Commute (x₄ a) (x₆ b)
  commute₅₆ : ∀ a b, Commute (x₅ a) (x₆ b)
  normal_form : Set.BijOn (sixProd x₁ x₂ x₃ x₄ x₅ x₆) Set.univ
    (sixClosure x₁ x₂ x₃ x₄ x₅ x₆ : Set X)
  torus : (fixedSubfield σ)ˣ × Γˣ →* X
  torus_injective : Function.Injective torus
  torus_x₁ : ∀ h a, torus h * x₁ a * (torus h)⁻¹ = x₁ ((h.2 : Γ) * a)
  torus_x₂ : ∀ h a, torus h * x₂ a * (torus h)⁻¹ = x₂ ((h.1 : fixedSubfield σ) * a)
  torus_x₃ : ∀ h a, torus h * x₃ a * (torus h)⁻¹ =
    x₃ (((h.1 : fixedSubfield σ) : Γ) * (h.2 : Γ) * a)
  torus_x₄ : ∀ h a, torus h * x₄ a * (torus h)⁻¹ =
    x₄ (((h.1 : fixedSubfield σ) : Γ) * σ (h.2 : Γ) * σ (σ (h.2 : Γ)) * a)
  torus_x₅ : ∀ h a, torus h * x₅ a * (torus h)⁻¹ =
    x₅ ((h.1 : fixedSubfield σ) * fixedNorm σ_cube (h.2 : Γ) * a)
  torus_x₆ : ∀ h a, torus h * x₆ a * (torus h)⁻¹ =
    x₆ ((h.1 : fixedSubfield σ) * (h.1 : fixedSubfield σ) * fixedNorm σ_cube (h.2 : Γ) * a)
  normalizer_eq : normalizer (sixClosure x₁ x₂ x₃ x₄ x₅ x₆ : Set X) =
    sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ torus.range
  u : X
  v : X
  u_mul_self : u * u = 1
  v_mul_self : v * v = 1
  orderOf_u_mul_v : orderOf (u * v) = 6
  u_x₂ : ∀ a, u * x₂ a * u = x₅ a
  u_x₃ : ∀ a, u * x₃ a * u = x₄ a
  u_x₆ : ∀ a, u * x₆ a * u = x₆ a
  v_x₁ : ∀ a, v * x₁ a * v = x₃ a
  v_x₄ : ∀ a, v * x₄ a * v = x₄ a
  v_x₅ : ∀ a, v * x₅ a * v = x₆ a
  u_torus : ∀ h, ∃ h', u * torus h * u = torus h'
  v_torus : ∀ h, ∃ h', v * torus h * v = torus h'
  sup_closure_eq_top : sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ closure ({u, v} : Set X) = ⊤
  card_eq : Nat.card X = q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)
  bruhat : ∀ g : X, ∃ b₁ ∈ sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ torus.range,
    ∃ w ∈ closure ({u, v} : Set X), ∃ b₂ ∈ sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ torus.range,
      g = b₁ * w * b₂
  bruhat_disjoint : ∀ w ∈ closure ({u, v} : Set X), ∀ w' ∈ closure ({u, v} : Set X),
    ∀ b₁ ∈ sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ torus.range,
    ∀ b₂ ∈ sixClosure x₁ x₂ x₃ x₄ x₅ x₆ ⊔ torus.range, b₁ * w * b₂ = w' → w = w'
  φ : MulAut X
  φ_x₁ : ∀ a, φ (x₁ a) = x₁ (a ^ 2)
  φ_x₂ : ∀ a, φ (x₂ a) = x₂ (a ^ 2)
  φ_x₃ : ∀ a, φ (x₃ a) = x₃ (a ^ 2)
  φ_x₄ : ∀ a, φ (x₄ a) = x₄ (a ^ 2)
  φ_x₅ : ∀ a, φ (x₅ a) = x₅ (a ^ 2)
  φ_x₆ : ∀ a, φ (x₆ a) = x₆ (a ^ 2)
  φ_u : φ u = u
  φ_v : φ v = v
  φ_torus : ∀ h, φ (torus h) = torus (h ^ 2)
  aut_eq : ∀ α : MulAut X, ∃ (g : X) (k : ℕ), α = MulAut.conj g * φ ^ k
  φ_pow_eq_conj : ∀ (k : ℕ) (g : X), φ ^ k = MulAut.conj g → φ ^ k = 1
  two_pow_orderOf_φ : 2 ^ orderOf φ = q ^ 3
  involution_conj : ∀ y : X, orderOf y = 2 → ∃ g : X, g * y * g⁻¹ = x₆ 1 ∨ g * y * g⁻¹ = x₄ 1

namespace TrialityD4Data

attribute [instance] instField instFinite instCharP

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

abbrev Γ₀ : Subfield d.Γ := fixedSubfield d.σ

abbrev tr (c : d.Γ) : d.Γ₀ := fixedTrace d.σ_cube c

abbrev nm (c : d.Γ) : d.Γ₀ := fixedNorm d.σ_cube c

@[expose] def U₁ : Subgroup X := rangeSubgroup d.x₁_add

@[expose] def U₂ : Subgroup X := rangeSubgroup d.x₂_add

@[expose] def U₃ : Subgroup X := rangeSubgroup d.x₃_add

@[expose] def U₄ : Subgroup X := rangeSubgroup d.x₄_add

@[expose] def U₅ : Subgroup X := rangeSubgroup d.x₅_add

@[expose] def U₆ : Subgroup X := rangeSubgroup d.x₆_add

@[expose] def S : Subgroup X := sixClosure d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆

@[expose] def J : Subgroup X := d.torus.range

@[expose] def B : Subgroup X := d.S ⊔ d.J

@[expose] def weyl : Subgroup X := closure ({d.u, d.v} : Set X)

@[expose] def J₁ : Subgroup X := d.J ⊓ centralizer (d.U₁ : Set X)

@[expose] def J₂ : Subgroup X := d.J ⊓ centralizer (d.U₂ : Set X)

@[expose] def J₃ : Subgroup X := d.J ⊓ centralizer (d.U₃ : Set X)

@[expose] def J₄ : Subgroup X := d.J ⊓ centralizer (d.U₄ : Set X)

@[expose] def J₅ : Subgroup X := d.J ⊓ centralizer (d.U₅ : Set X)

@[expose] def J₆ : Subgroup X := d.J ⊓ centralizer (d.U₆ : Set X)

@[expose] def J₀ : Subgroup X := (d.torus.comp (powMonoidHom (q - 1))).range

@[expose] def V : Subgroup X := d.U₆

@[expose] def Y : Subgroup X := d.U₅ ⊔ d.V

@[expose] def W : Subgroup X := d.U₄ ⊔ d.Y

@[expose] def F : Subgroup X := d.U₃ ⊔ d.W

@[expose] def D : Subgroup X := d.U₂ ⊔ d.F

@[expose] def M : Subgroup X := d.U₁ ⊔ d.F

include d in
theorem even_q : Even q := by
  obtain ⟨f, hf, hq⟩ := d.two_pow
  rw [hq]
  exact (Nat.even_pow' (by omega)).2 even_two

include d in
theorem two_le_q : 2 ≤ q := by
  obtain ⟨f, hf, hq⟩ := d.two_pow
  rw [hq]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem u_inv : d.u⁻¹ = d.u :=
  inv_eq_of_mul_eq_one_right d.u_mul_self

theorem v_inv : d.v⁻¹ = d.v :=
  inv_eq_of_mul_eq_one_right d.v_mul_self

theorem x₁_zero : d.x₁ 0 = 1 := map_zero_of_add d.x₁_add

theorem x₂_zero : d.x₂ 0 = 1 := map_zero_of_add d.x₂_add

theorem x₃_zero : d.x₃ 0 = 1 := map_zero_of_add d.x₃_add

theorem x₄_zero : d.x₄ 0 = 1 := map_zero_of_add d.x₄_add

theorem x₅_zero : d.x₅ 0 = 1 := map_zero_of_add d.x₅_add

theorem x₆_zero : d.x₆ 0 = 1 := map_zero_of_add d.x₆_add

theorem add_self_Γ₀ (a : d.Γ₀) : a + a = 0 :=
  Subtype.ext (CharTwo.add_self_eq_zero (a : d.Γ))

theorem x₁_mul_self (a : d.Γ) : d.x₁ a * d.x₁ a = 1 := by
  rw [← d.x₁_add, CharTwo.add_self_eq_zero, d.x₁_zero]

theorem x₂_mul_self (a : d.Γ₀) : d.x₂ a * d.x₂ a = 1 := by
  rw [← d.x₂_add, d.add_self_Γ₀, d.x₂_zero]

theorem x₃_mul_self (a : d.Γ) : d.x₃ a * d.x₃ a = 1 := by
  rw [← d.x₃_add, CharTwo.add_self_eq_zero, d.x₃_zero]

theorem x₄_mul_self (a : d.Γ) : d.x₄ a * d.x₄ a = 1 := by
  rw [← d.x₄_add, CharTwo.add_self_eq_zero, d.x₄_zero]

theorem x₅_mul_self (a : d.Γ₀) : d.x₅ a * d.x₅ a = 1 := by
  rw [← d.x₅_add, d.add_self_Γ₀, d.x₅_zero]

theorem x₆_mul_self (a : d.Γ₀) : d.x₆ a * d.x₆ a = 1 := by
  rw [← d.x₆_add, d.add_self_Γ₀, d.x₆_zero]

theorem mem_S {g : X} : g ∈ d.S ↔ ∃ a, sixProd d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ a = g := by
  constructor
  · intro hg
    obtain ⟨a, -, ha⟩ := d.normal_form.surjOn hg
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact d.normal_form.mapsTo (Set.mem_univ a)

theorem card_S : Nat.card d.S = q ^ 12 := by
  have h := Nat.card_congr (d.normal_form.equiv _)
  rw [Nat.card_univ, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod, d.card_Γ, d.card_Γ₀] at h
  calc Nat.card d.S = Nat.card (sixClosure d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ : Set X) := rfl
    _ = q ^ 12 := by rw [← h]; ring

include d in
theorem finite : Finite X := by
  refine Nat.finite_of_card_ne_zero ?_
  have hq := d.two_le_q
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have h6 : 1 ≤ q ^ 6 - 1 := by
    have : 2 ≤ q ^ 6 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  rw [d.card_eq]
  positivity

theorem not_two_dvd_index_S : ¬ 2 ∣ d.S.index := by
  have hq := d.two_le_q
  have hpos : 0 < q ^ 12 := by positivity
  have h := d.S.card_mul_index
  rw [d.card_S, d.card_eq, mul_assoc, mul_assoc] at h
  rw [Nat.eq_of_mul_eq_mul_left hpos h]
  have he := d.even_q
  have h2 : Odd (q ^ 2 - 1) :=
    odd_sub_one_of_even (he.pow_of_ne_zero (by norm_num)) (Nat.one_le_pow _ _ (by omega))
  have h6 : Odd (q ^ 6 - 1) :=
    odd_sub_one_of_even (he.pow_of_ne_zero (by norm_num)) (Nat.one_le_pow _ _ (by omega))
  have h8 : Odd (q ^ 8 + q ^ 4 + 1) :=
    ((he.pow_of_ne_zero (by norm_num)).add (he.pow_of_ne_zero (by norm_num))).add_one
  exact (h2.mul (h6.mul h8)).not_two_dvd_nat

theorem exists_sylow_eq_S : ∃ P : Sylow 2 X, (P : Subgroup X) = d.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, -, hq⟩ := d.two_pow
  have hp : IsPGroup 2 d.S := IsPGroup.of_card (n := 12 * f) (by
    rw [d.card_S, hq, ← pow_mul, mul_comm])
  exact ⟨hp.toSylow d.not_two_dvd_index_S, IsPGroup.toSylow_coe hp d.not_two_dvd_index_S⟩

theorem normalizer_S : normalizer (d.S : Set X) = d.B :=
  d.normalizer_eq

section Transport

variable {X' : Type*} [Group X'] (e : X ≃* X')

theorem sixProd_map (a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) :
    sixProd (fun c => e (d.x₁ c)) (fun c => e (d.x₂ c)) (fun c => e (d.x₃ c))
      (fun c => e (d.x₄ c)) (fun c => e (d.x₅ c)) (fun c => e (d.x₆ c)) a =
      e (sixProd d.x₁ d.x₂ d.x₃ d.x₄ d.x₅ d.x₆ a) := by
  simp only [sixProd, map_mul]

theorem sixClosure_map :
    sixClosure (fun c => e (d.x₁ c)) (fun c => e (d.x₂ c)) (fun c => e (d.x₃ c))
      (fun c => e (d.x₄ c)) (fun c => e (d.x₅ c)) (fun c => e (d.x₆ c)) =
      d.S.map e.toMonoidHom := by
  rw [S, sixClosure, sixClosure, MonoidHom.map_closure]
  simp only [Set.image_union, ← Set.range_comp]
  rfl

theorem closure_pair_map :
    closure ({e d.u, e d.v} : Set X') = (closure ({d.u, d.v} : Set X)).map e.toMonoidHom := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

@[expose] def ofMulEquiv : TrialityD4Data X' q where
  Γ := d.Γ
  two_pow := d.two_pow
  card_Γ := d.card_Γ
  σ := d.σ
  σ_apply := d.σ_apply
  σ_cube := d.σ_cube
  card_Γ₀ := d.card_Γ₀
  x₁ c := e (d.x₁ c)
  x₂ c := e (d.x₂ c)
  x₃ c := e (d.x₃ c)
  x₄ c := e (d.x₄ c)
  x₅ c := e (d.x₅ c)
  x₆ c := e (d.x₆ c)
  x₁_add a b := by rw [d.x₁_add, map_mul]
  x₂_add a b := by rw [d.x₂_add, map_mul]
  x₃_add a b := by rw [d.x₃_add, map_mul]
  x₄_add a b := by rw [d.x₄_add, map_mul]
  x₅_add a b := by rw [d.x₅_add, map_mul]
  x₆_add a b := by rw [d.x₆_add, map_mul]
  x₁_injective := e.injective.comp d.x₁_injective
  x₂_injective := e.injective.comp d.x₂_injective
  x₃_injective := e.injective.comp d.x₃_injective
  x₄_injective := e.injective.comp d.x₄_injective
  x₅_injective := e.injective.comp d.x₅_injective
  x₆_injective := e.injective.comp d.x₆_injective
  comm₁₂ a b := by rw [← map_commutatorElement, d.comm₁₂, map_mul, map_mul]
  comm₁₃ a b := by rw [← map_commutatorElement, d.comm₁₃, map_mul, map_mul]
  comm₁₄ a b := by rw [← map_commutatorElement, d.comm₁₄]
  comm₂₅ a b := by rw [← map_commutatorElement, d.comm₂₅]
  comm₃₄ a b := by rw [← map_commutatorElement, d.comm₃₄]
  commute₁₅ a b := (d.commute₁₅ a b).map e
  commute₁₆ a b := (d.commute₁₆ a b).map e
  commute₂₃ a b := (d.commute₂₃ a b).map e
  commute₂₄ a b := (d.commute₂₄ a b).map e
  commute₂₆ a b := (d.commute₂₆ a b).map e
  commute₃₅ a b := (d.commute₃₅ a b).map e
  commute₃₆ a b := (d.commute₃₆ a b).map e
  commute₄₅ a b := (d.commute₄₅ a b).map e
  commute₄₆ a b := (d.commute₄₆ a b).map e
  commute₅₆ a b := (d.commute₅₆ a b).map e
  normal_form := by
    have h := (e.injective.injOn (s := (d.S : Set X))).bijOn_image.comp d.normal_form
    rw [sixClosure_map, Subgroup.coe_map]
    convert h using 1
    · funext a
      exact d.sixProd_map e a
    · rfl
  torus := e.toMonoidHom.comp d.torus
  torus_injective := e.injective.comp d.torus_injective
  torus_x₁ h a := by
    change e (d.torus h) * e (d.x₁ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₁]
  torus_x₂ h a := by
    change e (d.torus h) * e (d.x₂ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₂]
  torus_x₃ h a := by
    change e (d.torus h) * e (d.x₃ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₃]
  torus_x₄ h a := by
    change e (d.torus h) * e (d.x₄ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₄]
  torus_x₅ h a := by
    change e (d.torus h) * e (d.x₅ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₅]
  torus_x₆ h a := by
    change e (d.torus h) * e (d.x₆ a) * (e (d.torus h))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, d.torus_x₆]
  normalizer_eq := by
    rw [sixClosure_map, ← Subgroup.map_equiv_normalizer_eq, MonoidHom.range_comp,
      ← Subgroup.map_sup]
    exact congrArg (Subgroup.map e.toMonoidHom) d.normalizer_eq
  u := e d.u
  v := e d.v
  u_mul_self := by rw [← map_mul, d.u_mul_self, map_one]
  v_mul_self := by rw [← map_mul, d.v_mul_self, map_one]
  orderOf_u_mul_v := by rw [← map_mul, MulEquiv.orderOf_eq, d.orderOf_u_mul_v]
  u_x₂ a := by rw [← map_mul, ← map_mul, d.u_x₂]
  u_x₃ a := by rw [← map_mul, ← map_mul, d.u_x₃]
  u_x₆ a := by rw [← map_mul, ← map_mul, d.u_x₆]
  v_x₁ a := by rw [← map_mul, ← map_mul, d.v_x₁]
  v_x₄ a := by rw [← map_mul, ← map_mul, d.v_x₄]
  v_x₅ a := by rw [← map_mul, ← map_mul, d.v_x₅]
  u_torus h := by
    obtain ⟨h', hh'⟩ := d.u_torus h
    exact ⟨h', by simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      ← map_mul, hh']⟩
  v_torus h := by
    obtain ⟨h', hh'⟩ := d.v_torus h
    exact ⟨h', by simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      ← map_mul, hh']⟩
  sup_closure_eq_top := by
    rw [sixClosure_map, d.closure_pair_map e, ← Subgroup.map_sup,
      show d.S ⊔ closure ({d.u, d.v} : Set X) = ⊤ from d.sup_closure_eq_top]
    exact Subgroup.map_top_of_surjective _ e.surjective
  card_eq := (Nat.card_congr e.toEquiv).symm.trans d.card_eq
  bruhat g := by
    obtain ⟨b₁, hb₁, w, hw, b₂, hb₂, h⟩ := d.bruhat (e.symm g)
    refine ⟨e b₁, ?_, e w, ?_, e b₂, ?_, ?_⟩
    · rw [sixClosure_map, MonoidHom.range_comp, ← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem _ hb₁
    · rw [d.closure_pair_map e]
      exact Subgroup.mem_map_of_mem _ hw
    · rw [sixClosure_map, MonoidHom.range_comp, ← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem _ hb₂
    · rw [← map_mul, ← map_mul, ← h, MulEquiv.apply_symm_apply]
  bruhat_disjoint w hw w' hw' b₁ hb₁ b₂ hb₂ h := by
    rw [d.closure_pair_map e] at hw hw'
    rw [sixClosure_map, MonoidHom.range_comp, ← Subgroup.map_sup] at hb₁ hb₂
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    obtain ⟨w₀', hw₀', rfl⟩ := hw'
    obtain ⟨c₁, hc₁, rfl⟩ := hb₁
    obtain ⟨c₂, hc₂, rfl⟩ := hb₂
    simp only [MulEquiv.coe_toMonoidHom] at h ⊢
    rw [← map_mul, ← map_mul] at h
    exact congrArg e (d.bruhat_disjoint w₀ hw₀ w₀' hw₀' c₁ hc₁ c₂ hc₂ (e.injective h))
  φ := MulAut.congr e d.φ
  φ_x₁ a := by simp [d.φ_x₁]
  φ_x₂ a := by simp [d.φ_x₂]
  φ_x₃ a := by simp [d.φ_x₃]
  φ_x₄ a := by simp [d.φ_x₄]
  φ_x₅ a := by simp [d.φ_x₅]
  φ_x₆ a := by simp [d.φ_x₆]
  φ_u := by simp [d.φ_u]
  φ_v := by simp [d.φ_v]
  φ_torus h := by simp [d.φ_torus]
  aut_eq α := by
    obtain ⟨g, k, hα⟩ := d.aut_eq ((MulAut.congr e).symm α)
    refine ⟨e g, k, ?_⟩
    have h1 : α = MulAut.congr e (MulAut.conj g * d.φ ^ k) := by
      rw [← hα, MulEquiv.apply_symm_apply]
    rw [h1, map_mul, map_pow]
    congr 1
    ext x
    simp
  φ_pow_eq_conj k g h := by
    have h1 : d.φ ^ k = MulAut.conj (e.symm g) := by
      apply (MulAut.congr e).injective
      rw [map_pow, h]
      ext x
      simp
    rw [← map_pow, d.φ_pow_eq_conj k _ h1, map_one]
  two_pow_orderOf_φ := by rw [MulEquiv.orderOf_eq]; exact d.two_pow_orderOf_φ
  involution_conj y hy := by
    obtain ⟨g, hg⟩ := d.involution_conj (e.symm y) (by rw [MulEquiv.orderOf_eq]; exact hy)
    refine ⟨e g, ?_⟩
    rcases hg with hg | hg
    · left
      rw [← hg, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · right
      rw [← hg, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end Transport

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
