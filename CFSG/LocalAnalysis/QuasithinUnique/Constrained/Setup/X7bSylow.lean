module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped commutatorElement

variable {K : Type} [Field K]

section Basic

variable [CharP K 2]

theorem uElt_zero_eq_one : uElt (0 : K) 0 0 0 = 1 :=
  antiSp_ext uMat_zero

theorem uElt_inj {a b c d A B C D : K} (h : uElt a b c d = uElt A B C D) :
    a = A ∧ b = B ∧ c = C ∧ d = D :=
  uMat_inj (congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K)) h)

theorem uElt_mul_self (a b c d : K) :
    uElt a b c d * uElt a b c d = uElt 0 (a * d) (a ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  have e1 : a + a = 0 := CharTwo.add_self_eq_zero a
  have e2 : b + b + a * d = a * d := by linear_combination b * h2
  have e3 : c + c + a * b + a * a * d + b * a = a ^ 2 * d := by
    linear_combination (c + a * b) * h2
  have e4 : d + d = 0 := CharTwo.add_self_eq_zero d
  rw [e1, e2, e3, e4]

variable (K) in
@[expose] def radA1 : Subgroup (antiSp K) where
  carrier := {g | ∃ b c d : K, g = uElt 0 b c d}
  one_mem' := ⟨0, 0, 0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, c, d, rfl⟩ ⟨B, C, D, rfl⟩
    refine ⟨b + B, c + C, d + D, ?_⟩
    rw [uElt_mul]
    congr 1 <;> ring
  inv_mem' := by
    rintro _ ⟨b, c, d, rfl⟩
    refine ⟨b, c, d, ?_⟩
    rw [uElt_inv]
    congr 1
    ring

variable (K) in
@[expose] def radA2 : Subgroup (antiSp K) where
  carrier := {g | ∃ a b c : K, g = uElt a b c 0}
  one_mem' := ⟨0, 0, 0, uElt_zero_eq_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨A, B, C, rfl⟩
    refine ⟨a + A, b + B, c + C + a * B + b * A, ?_⟩
    rw [uElt_mul]
    congr 1 <;> ring
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    refine ⟨a, b, c, ?_⟩
    rw [uElt_inv]
    congr 1
    ring

end Basic

section Structure

variable [CharP K 2]

theorem radA1_le_antiUnipotent : radA1 K ≤ antiUnipotent K := by
  rintro _ ⟨b, c, d, rfl⟩
  exact ⟨0, b, c, d, rfl⟩

theorem radA2_le_antiUnipotent : radA2 K ≤ antiUnipotent K := by
  rintro _ ⟨a, b, c, rfl⟩
  exact ⟨a, b, c, 0, rfl⟩

theorem antiUnipotentCenter_le_radA1 : antiUnipotentCenter K ≤ radA1 K := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨b, c, 0, rfl⟩

theorem antiUnipotentCenter_le_radA2 : antiUnipotentCenter K ≤ radA2 K := by
  rintro _ ⟨b, c, rfl⟩
  exact ⟨0, b, c, rfl⟩

theorem radA1_inf_radA2 : radA1 K ⊓ radA2 K = antiUnipotentCenter K := by
  refine le_antisymm ?_ (le_inf antiUnipotentCenter_le_radA1 antiUnipotentCenter_le_radA2)
  rintro g ⟨⟨b, c, d, rfl⟩, ⟨a, b', c', h⟩⟩
  obtain ⟨ha, hb, hc, hd⟩ := uElt_inj h
  exact ⟨b, c, by rw [← hd]⟩

theorem antiUnipotent_eq_radA1_sup_radA2 : antiUnipotent K = radA1 K ⊔ radA2 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine le_antisymm ?_ (sup_le radA1_le_antiUnipotent radA2_le_antiUnipotent)
  rintro _ ⟨a, b, c, d, rfl⟩
  have e : uElt a b c d = uElt 0 b (c + a * b) d * uElt a 0 0 0 := by
    rw [uElt_mul]
    congr 1
    · simp
    · simp
    · linear_combination (-(a * b)) * h2
    · simp
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left ⟨b, c + a * b, d, rfl⟩)
    (Subgroup.mem_sup_right ⟨a, 0, 0, rfl⟩)

theorem mul_self_of_mem_radA1 {g : antiSp K} (hg : g ∈ radA1 K) : g * g = 1 := by
  obtain ⟨b, c, d, rfl⟩ := hg
  rw [uElt_mul_self, show (0 : K) * d = 0 by ring, show (0 : K) ^ 2 * d = 0 by ring, uElt_zero_eq_one]

theorem mul_self_of_mem_radA2 {g : antiSp K} (hg : g ∈ radA2 K) : g * g = 1 := by
  obtain ⟨a, b, c, rfl⟩ := hg
  rw [uElt_mul_self, show a * (0 : K) = 0 by ring, show a ^ 2 * (0 : K) = 0 by ring, uElt_zero_eq_one]

theorem radA1_comm {x y : antiSp K} (hx : x ∈ radA1 K) (hy : y ∈ radA1 K) : x * y = y * x := by
  obtain ⟨b, c, d, rfl⟩ := hx
  obtain ⟨B, C, D, rfl⟩ := hy
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

theorem radA2_comm {x y : antiSp K} (hx : x ∈ radA2 K) (hy : y ∈ radA2 K) : x * y = y * x := by
  obtain ⟨a, b, c, rfl⟩ := hx
  obtain ⟨A, B, C, rfl⟩ := hy
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

theorem mul_self_eq_one_iff {g : antiSp K} (hg : g ∈ antiUnipotent K) :
    g * g = 1 ↔ g ∈ radA1 K ∨ g ∈ radA2 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  rw [uElt_mul_self, ← uElt_zero_eq_one]
  constructor
  · intro h
    have := (uElt_inj h).2.1
    rcases mul_eq_zero.mp this with ha | hd
    · exact Or.inl ⟨b, c, d, by rw [ha]⟩
    · exact Or.inr ⟨a, b, c, by rw [hd]⟩
  · rintro (⟨b', c', d', h⟩ | ⟨a', b', c', h⟩)
    · obtain ⟨ha, -⟩ := uElt_inj h
      rw [ha]
      simp
    · obtain ⟨-, -, -, hd⟩ := uElt_inj h
      rw [hd]
      simp


theorem subgroup_le_of_subset_union {G : Type*} [Group G] {E P Q : Subgroup G}
    (h : ∀ x ∈ E, x ∈ P ∨ x ∈ Q) : E ≤ P ∨ E ≤ Q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxE, hxP⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨y, hyE, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have hxQ : x ∈ Q := (h x hxE).resolve_left hxP
  have hyP : y ∈ P := (h y hyE).resolve_right hyQ
  rcases h (x * y) (mul_mem hxE hyE) with hP | hQ
  · exact hxP (by simpa using mul_mem hP (inv_mem hyP))
  · exact hyQ (by simpa using mul_mem (inv_mem hxQ) hQ)

theorem elementary_le_radA1_or_radA2 {E : Subgroup (antiSp K)} (hEU : E ≤ antiUnipotent K)
    (hE : ∀ x ∈ E, x * x = 1) : E ≤ radA1 K ∨ E ≤ radA2 K :=
  subgroup_le_of_subset_union fun x hx => (mul_self_eq_one_iff (hEU hx)).mp (hE x hx)

theorem mem_radA1_of_commutes {g : antiSp K} (hg : g ∈ antiUnipotent K)
    (hc : ∀ h ∈ radA1 K, g * h = h * g) : g ∈ radA1 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  have h1 := hc (uElt 0 0 0 1) ⟨0, 0, 1, rfl⟩
  rw [uElt_mul, uElt_mul] at h1
  have hb := (uElt_inj h1).2.1
  have ha : a = 0 := by
    have : a * 1 = 0 := by linear_combination hb
    simpa using this
  exact ⟨b, c, d, by rw [ha]⟩

theorem mem_radA2_of_commutes {g : antiSp K} (hg : g ∈ antiUnipotent K)
    (hc : ∀ h ∈ radA2 K, g * h = h * g) : g ∈ radA2 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  have h1 := hc (uElt 1 0 0 0) ⟨1, 0, 0, rfl⟩
  rw [uElt_mul, uElt_mul] at h1
  have hb := (uElt_inj h1).2.1
  have hd : d = 0 := by
    have : 1 * d = 0 := by linear_combination -hb
    simpa using this
  exact ⟨a, b, c, by rw [hd]⟩

theorem mem_antiUnipotentCenter_iff_central (g : antiSp K) :
    g ∈ antiUnipotentCenter K ↔ g ∈ antiUnipotent K ∧ ∀ h ∈ antiUnipotent K, g * h = h * g := by
  constructor
  · rintro ⟨b, c, rfl⟩
    refine ⟨⟨0, b, c, 0, rfl⟩, ?_⟩
    rintro _ ⟨A, B, C, D, rfl⟩
    rw [uElt_mul, uElt_mul]
    congr 1 <;> ring
  · rintro ⟨hgU, hc⟩
    have h1 := mem_radA1_of_commutes hgU fun h hh => hc h (radA1_le_antiUnipotent hh)
    have h2 := mem_radA2_of_commutes hgU fun h hh => hc h (radA2_le_antiUnipotent hh)
    exact radA1_inf_radA2 (K := K) ▸ ⟨h1, h2⟩


theorem card_radicals [Finite K] :
    Nat.card (antiUnipotent K) = Nat.card K ^ 4 ∧ Nat.card (radA1 K) = Nat.card K ^ 3 ∧
      Nat.card (radA2 K) = Nat.card K ^ 3 ∧ Nat.card (antiUnipotentCenter K) = Nat.card K ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let e : K × K × K × K ≃ antiUnipotent K := Equiv.ofBijective
      (fun p => ⟨uElt p.1 p.2.1 p.2.2.1 p.2.2.2, p.1, p.2.1, p.2.2.1, p.2.2.2, rfl⟩)
      ⟨fun p q h => by
        obtain ⟨h1, h2, h3, h4⟩ := uElt_inj (congrArg Subtype.val h)
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)),
        fun ⟨g, a, b, c, d, hg⟩ => ⟨(a, b, c, d), Subtype.ext hg.symm⟩⟩
    rw [← Nat.card_congr e]
    simp [Nat.card_prod, pow_succ]
    ring
  · let e : K × K × K ≃ radA1 K := Equiv.ofBijective
      (fun p => ⟨uElt 0 p.1 p.2.1 p.2.2, p.1, p.2.1, p.2.2, rfl⟩)
      ⟨fun p q h => by
        obtain ⟨-, h2, h3, h4⟩ := uElt_inj (congrArg Subtype.val h)
        exact Prod.ext h2 (Prod.ext h3 h4),
        fun ⟨g, b, c, d, hg⟩ => ⟨(b, c, d), Subtype.ext hg.symm⟩⟩
    rw [← Nat.card_congr e]
    simp [Nat.card_prod, pow_succ]
    ring
  · let e : K × K × K ≃ radA2 K := Equiv.ofBijective
      (fun p => ⟨uElt p.1 p.2.1 p.2.2 0, p.1, p.2.1, p.2.2, rfl⟩)
      ⟨fun p q h => by
        obtain ⟨h1, h2, h3, -⟩ := uElt_inj (congrArg Subtype.val h)
        exact Prod.ext h1 (Prod.ext h2 h3),
        fun ⟨g, a, b, c, hg⟩ => ⟨(a, b, c), Subtype.ext hg.symm⟩⟩
    rw [← Nat.card_congr e]
    simp [Nat.card_prod, pow_succ]
    ring
  · let e : K × K ≃ antiUnipotentCenter K := Equiv.ofBijective
      (fun p => ⟨uElt 0 p.1 p.2 0, p.1, p.2, rfl⟩)
      ⟨fun p q h => by
        obtain ⟨-, h2, h3, -⟩ := uElt_inj (congrArg Subtype.val h)
        exact Prod.ext h2 h3,
        fun ⟨g, b, c, hg⟩ => ⟨(b, c), Subtype.ext hg.symm⟩⟩
    rw [← Nat.card_congr e]
    simp [Nat.card_prod, pow_succ]

theorem abelian_omega_card [Finite K] (A : Subgroup (antiSp K)) (hAU : A ≤ antiUnipotent K)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card {x : antiSp K // x ∈ A ∧ x * x = 1} ≤ Nat.card K ^ 3 ∧
      (Nat.card {x : antiSp K // x ∈ A ∧ x * x = 1} = Nat.card K ^ 3 →
        A = radA1 K ∨ A = radA2 K) := by
  classical
  let Ω : Subgroup (antiSp K) :=
    { carrier := {x | x ∈ A ∧ x * x = 1}
      one_mem' := ⟨one_mem A, one_mul 1⟩
      mul_mem' := by
        rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
        refine ⟨mul_mem hxA hyA, ?_⟩
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hab y hyA x hxA]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx, hy, one_mul]
      inv_mem' := by
        rintro x ⟨hxA, hx⟩
        refine ⟨inv_mem hxA, ?_⟩
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx, inv_one] }
  have hΩcard : Nat.card {x : antiSp K // x ∈ A ∧ x * x = 1} = Nat.card Ω := rfl
  have hΩ : Ω ≤ radA1 K ∨ Ω ≤ radA2 K :=
    elementary_le_radA1_or_radA2 (fun x hx => hAU hx.1) (fun x hx => hx.2)
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  rw [hΩcard]
  rcases hΩ with h | h
  · refine ⟨h1 ▸ Subgroup.card_le_of_le h, fun heq => Or.inl ?_⟩
    have hΩeq : Ω = radA1 K := Subgroup.eq_of_le_of_card_ge h (by rw [heq, h1])
    refine le_antisymm (fun x hx => ?_) ?_
    · exact mem_radA1_of_commutes (hAU hx) fun y hy => hab x hx y (by
        have : y ∈ Ω := hΩeq ▸ hy
        exact this.1)
    · intro x hx
      have : x ∈ Ω := hΩeq ▸ hx
      exact this.1
  · refine ⟨h2 ▸ Subgroup.card_le_of_le h, fun heq => Or.inr ?_⟩
    have hΩeq : Ω = radA2 K := Subgroup.eq_of_le_of_card_ge h (by rw [heq, h2])
    refine le_antisymm (fun x hx => ?_) ?_
    · exact mem_radA2_of_commutes (hAU hx) fun y hy => hab x hx y (by
        have : y ∈ Ω := hΩeq ▸ hy
        exact this.1)
    · intro x hx
      have : x ∈ Ω := hΩeq ▸ hx
      exact this.1


section Squares

theorem isSquare_iff (g : antiSp K) (hg1 : g ≠ 1) :
    (∃ h ∈ antiUnipotent K, h * h = g) ↔ ∃ b c : K, b ≠ 0 ∧ c ≠ 0 ∧ g = uElt 0 b c 0 := by
  constructor
  · rintro ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩
    rw [uElt_mul_self] at hg1 ⊢
    have had : a * d ≠ 0 := fun h0 => hg1 (by rw [h0, show a ^ 2 * d = a * (a * d) by ring, h0,
      mul_zero, uElt_zero_eq_one])
    have ha : a ≠ 0 := left_ne_zero_of_mul had
    have hd : d ≠ 0 := right_ne_zero_of_mul had
    exact ⟨a * d, a ^ 2 * d, had, mul_ne_zero (pow_ne_zero 2 ha) hd, rfl⟩
  · rintro ⟨b, c, hb, hc, rfl⟩
    refine ⟨uElt (c / b) 0 0 (b ^ 2 / c), ⟨_, _, _, _, rfl⟩, ?_⟩
    rw [uElt_mul_self]
    congr 1
    · field_simp
    · field_simp

theorem sq_mem_antiUnipotentCenter {h : antiSp K} (hh : h ∈ antiUnipotent K) : h * h ∈ antiUnipotentCenter K := by
  obtain ⟨a, b, c, d, rfl⟩ := hh
  rw [uElt_mul_self]
  exact ⟨a * d, a ^ 2 * d, rfl⟩

omit [CharP K 2] in
theorem exists_ne_zero_ne (hK : 2 < Nat.card K) (c : K) : ∃ c₁ : K, c₁ ≠ 0 ∧ c ≠ c₁ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, c} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon x hx |>.symm]
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
  have := Finset.card_le_two (a := (0 : K)) (b := c)
  omega

theorem closure_squares_eq (hK : 2 < Nat.card K) :
    Subgroup.closure {g : antiSp K | ∃ h ∈ antiUnipotent K, g = h * h} = antiUnipotentCenter K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact sq_mem_antiUnipotentCenter hh
  · have hsq : ∀ b c : K, b ≠ 0 → c ≠ 0 → uElt 0 b c 0 ∈
        Subgroup.closure {g : antiSp K | ∃ h ∈ antiUnipotent K, g = h * h} := fun b c hb hc =>
      Subgroup.subset_closure ⟨uElt (c / b) 0 0 (b ^ 2 / c), ⟨_, _, _, _, rfl⟩, by
        rw [uElt_mul_self]; congr 1 <;> field_simp⟩
    have hZ : ∀ c : K, uElt 0 0 c 0 ∈
        Subgroup.closure {g : antiSp K | ∃ h ∈ antiUnipotent K, g = h * h} := by
      intro c
      obtain ⟨c₁, h1, h2'⟩ := exists_ne_zero_ne hK c
      have e : uElt 0 0 c 0 = uElt 0 1 c₁ 0 * uElt 0 1 (c + c₁) 0 := by
        rw [uElt_mul]
        congr 1 <;> first | ring1 | (ring_nf; simp [h2])
      rw [e]
      exact mul_mem (hsq 1 c₁ one_ne_zero h1)
        (hsq 1 (c + c₁) one_ne_zero (fun h0 => h2' (CharTwo.add_eq_zero.mp h0)))
    rintro _ ⟨b, c, rfl⟩
    by_cases hb : b = 0
    · subst hb
      exact hZ c
    · obtain ⟨c₁, h1, -⟩ := exists_ne_zero_ne hK c
      have e : uElt 0 b c 0 = uElt 0 b c₁ 0 * uElt 0 0 (c + c₁) 0 := by
        rw [uElt_mul]
        congr 1 <;> first | ring1 | (ring_nf; simp [h2])
      rw [e]
      exact mul_mem (hsq b c₁ hb h1) (hZ _)

theorem commutator_uElt (a d : K) :
    ⁅uElt a 0 0 0, uElt 0 0 0 d⁆ = uElt 0 (a * d) (a ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) = 1 := by linear_combination h2
  rw [commutatorElement_def, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2, h3])

theorem commutator_antiUnipotent_eq (hK : 2 < Nat.card K) :
    ⁅antiUnipotent K, antiUnipotent K⁆ = antiUnipotentCenter K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · rintro _ ⟨a, b, c, d, rfl⟩ _ ⟨A, B, C, D, rfl⟩
    have h1 : a + A + a + A = 0 := by linear_combination (a + A) * h2
    have h4 : d + D + d + D = 0 := by linear_combination (d + D) * h2
    rw [commutatorElement_def, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul, h1, h4]
    exact ⟨_, _, rfl⟩
  · rw [← closure_squares_eq hK]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩
    rw [uElt_mul_self, ← commutator_uElt]
    have hx : uElt a 0 0 0 ∈ antiUnipotent K := ⟨a, 0, 0, 0, rfl⟩
    have hy : uElt 0 0 0 d ∈ antiUnipotent K := ⟨0, 0, 0, d, rfl⟩
    exact Subgroup.commutator_mem_commutator hx hy

end Squares

end Structure

section Sylow

variable [CharP K 2] [Finite K]

theorem exists_card_eq_two_pow : ∃ n : ℕ, 1 ≤ n ∧ Nat.card K = 2 ^ n := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem card_and_isSylowTwoOf_antiUnipotent :
    Nat.card (antiUnipotent K) = Nat.card K ^ 4 ∧ IsSylowTwoOf (antiUnipotent K) ⊤ := by
  obtain ⟨n, hn, hq⟩ := exists_card_eq_two_pow (K := K)
  have hU : Nat.card (antiUnipotent K) = Nat.card K ^ 4 := card_antiUnipotent rfl
  refine ⟨hU, le_top, IsPGroup.of_card (n := n * 4) (by rw [hU, hq, ← pow_mul]), ?_⟩
  rw [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
    Subgroup.relIndex_top_right _]
  intro hdvd
  have h1 := Subgroup.card_mul_index (antiUnipotent K)
  rw [hU, card_antiSp rfl] at h1
  have hpos : 0 < Nat.card K ^ 4 := Nat.pos_of_ne_zero (pow_ne_zero 4 Nat.card_pos.ne')
  have h2 : (antiUnipotent K).index = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) :=
    Nat.eq_of_mul_eq_mul_left hpos h1
  have hodd : Odd ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
    have he2 : Even (Nat.card K) := by
      rw [hq, Nat.even_pow]
      exact ⟨even_two, by omega⟩
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    refine Odd.mul ?_ ?_
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (Even.pow_of_ne_zero he2 (by norm_num))
        odd_one
    · exact Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) (Even.pow_of_ne_zero he2 (by norm_num))
        odd_one
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem card_omega_radA1 :
    Nat.card {x : antiSp K // x ∈ radA1 K ∧ x * x = 1} = Nat.card K ^ 3 := by
  rw [← (card_radicals (K := K)).2.1]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    ⟨fun h => h.1, fun h => ⟨h, mul_self_of_mem_radA1 h⟩⟩)

theorem card_omega_radA2 :
    Nat.card {x : antiSp K // x ∈ radA2 K ∧ x * x = 1} = Nat.card K ^ 3 := by
  rw [← (card_radicals (K := K)).2.2.1]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    ⟨fun h => h.1, fun h => ⟨h, mul_self_of_mem_radA2 h⟩⟩)

theorem even_symplectic_four_Sylow_involution_radicals {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    (Nat.card (antiUnipotent K) = Nat.card K ^ 4 ∧ IsSylowTwoOf (antiUnipotent K) ⊤) ∧
    ((∀ x ∈ radA1 K, ∀ y ∈ radA1 K, x * y = y * x) ∧ (∀ x ∈ radA1 K, x * x = 1) ∧
      Nat.card (radA1 K) = Nat.card K ^ 3) ∧
    ((∀ x ∈ radA2 K, ∀ y ∈ radA2 K, x * y = y * x) ∧ (∀ x ∈ radA2 K, x * x = 1) ∧
      Nat.card (radA2 K) = Nat.card K ^ 3) ∧
    antiUnipotent K = radA1 K ⊔ radA2 K ∧
    radA1 K ⊓ radA2 K = antiUnipotentCenter K ∧
    (∀ g : antiSp K, g ∈ antiUnipotentCenter K ↔
      g ∈ antiUnipotent K ∧ ∀ h ∈ antiUnipotent K, g * h = h * g) ∧
    (∀ g ∈ antiUnipotent K, g * g = 1 ↔ g ∈ radA1 K ∨ g ∈ radA2 K) ∧
    (∀ E : Subgroup (antiSp K), E ≤ antiUnipotent K → (∀ x ∈ E, x * x = 1) →
      E ≤ radA1 K ∨ E ≤ radA2 K) ∧
    (∀ A : Subgroup (antiSp K), A ≤ antiUnipotent K → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card {x : antiSp K // x ∈ A ∧ x * x = 1} ≤ 2 ^ (3 * n) ∧
        (Nat.card {x : antiSp K // x ∈ A ∧ x * x = 1} = 2 ^ (3 * n) →
          A = radA1 K ∨ A = radA2 K)) ∧
    Nat.card {x : antiSp K // x ∈ radA1 K ∧ x * x = 1} = 2 ^ (3 * n) ∧
    Nat.card {x : antiSp K // x ∈ radA2 K ∧ x * x = 1} = 2 ^ (3 * n) ∧
    (2 ≤ n → ⁅antiUnipotent K, antiUnipotent K⁆ = antiUnipotentCenter K ∧
      Subgroup.closure {g : antiSp K | ∃ h ∈ antiUnipotent K, g = h * h} =
        antiUnipotentCenter K ∧
      ∀ g : antiSp K, g ≠ 1 → ((∃ h ∈ antiUnipotent K, h * h = g) ↔
        ∃ b c : K, b ≠ 0 ∧ c ≠ 0 ∧ g = uElt 0 b c 0)) := by
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, h1, h2, -⟩ := card_radicals (K := K)
  refine ⟨card_and_isSylowTwoOf_antiUnipotent,
    ⟨fun x hx y hy => radA1_comm hx hy, fun x hx => mul_self_of_mem_radA1 hx, h1⟩,
    ⟨fun x hx y hy => radA2_comm hx hy, fun x hx => mul_self_of_mem_radA2 hx, h2⟩,
    antiUnipotent_eq_radA1_sup_radA2, radA1_inf_radA2,
    mem_antiUnipotentCenter_iff_central, fun g hg => mul_self_eq_one_iff hg,
    fun E hE hE2 => elementary_le_radA1_or_radA2 hE hE2, fun A hA hab => ?_,
    card_omega_radA1.trans hq3, card_omega_radA2.trans hq3, fun hn2 => ?_⟩
  · obtain ⟨hle, heq⟩ := abelian_omega_card A hA hab
    exact ⟨hq3 ▸ hle, fun h => heq (hq3 ▸ h)⟩
  · have hK2 : 2 < Nat.card K := by
      rw [hK]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact ⟨commutator_antiUnipotent_eq hK2, closure_squares_eq hK2, fun g hg => isSquare_iff g hg⟩

end Sylow

end CFSG.QuasithinUnique.Setup.X7b
