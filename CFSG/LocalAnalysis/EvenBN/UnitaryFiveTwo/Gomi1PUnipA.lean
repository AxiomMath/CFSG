module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem uElt_eq_coords {a b c d a' b' c' d' : K}
    (h : uElt a b c d = uElt a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  uMat_inj (congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K)) h)

theorem uElt_congr_coords {a b c d a' b' c' d' : K} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') : uElt a b c d = uElt a' b' c' d' := by
  subst h1 h2 h3 h4
  rfl

theorem uElt_zero_eq_one : uElt (0 : K) 0 0 0 = 1 :=
  antiSp_ext uMat_zero

theorem uElt_mul_self (a b c d : K) :
    uElt a b c d * uElt a b c d = uElt 0 (a * d) (a ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  refine uElt_congr_coords ?_ ?_ ?_ ?_
  · linear_combination a * h2
  · linear_combination b * h2
  · linear_combination (c + a * b) * h2
  · linear_combination d * h2

theorem card_antiUnipotent [Finite K] : Nat.card (antiUnipotent K) = Nat.card K ^ 4 := by
  have hbij : Function.Bijective (fun p : K × K × K × K =>
      (⟨uElt p.1 p.2.1 p.2.2.1 p.2.2.2, uElt_mem_antiUnipotent _ _ _ _⟩ : antiUnipotent K)) := by
    refine ⟨fun p q h => ?_, fun g => ?_⟩
    · obtain ⟨a, b, c, d⟩ := p
      obtain ⟨A, B, C, D⟩ := q
      have h' : uElt a b c d = uElt A B C D := congrArg Subtype.val h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := uElt_eq_coords h'
      rfl
    · obtain ⟨g, a, b, c, d, rfl⟩ := g
      exact ⟨(a, b, c, d), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp only [Nat.card_prod]
  ring

theorem natCard_eq_pow_three {R : Subgroup (antiSp K)} {f : K × K × K → antiSp K}
    (hf : ∀ p, f p ∈ R) (hinj : Function.Injective f) (hsurj : ∀ g ∈ R, ∃ p, f p = g) :
    Nat.card R = Nat.card K ^ 3 := by
  have hbij : Function.Bijective (fun p => (⟨f p, hf p⟩ : R)) := by
    refine ⟨fun p q h => hinj (congrArg Subtype.val h : f p = f q), fun g => ?_⟩
    obtain ⟨p, hp⟩ := hsurj g.1 g.2
    exact ⟨p, Subtype.ext hp⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp only [Nat.card_prod]
  ring

theorem frobHom_uElt (a b c d : K) :
    frobHom K (uElt a b c d) = uElt (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) := by
  apply antiSp_ext
  rw [glMat_frobHom, glMat_uElt, glMat_uElt]
  simpa only [pow_one] using uMat_map_pow 1 a b c d

theorem frobHom_mem_antiUnipotent {g : antiSp K} (hg : g ∈ antiUnipotent K) :
    frobHom K g ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  rw [frobHom_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

theorem antiUnipotent_class_two {x y z : antiSp K} (hx : x ∈ antiUnipotent K)
    (hy : y ∈ antiUnipotent K) (hz : z ∈ antiUnipotent K) :
    ⁅x, y⁆ * z = z * ⁅x, y⁆ := by
  set x' : antiUnipotent K := ⟨x, hx⟩ with hx'
  set y' : antiUnipotent K := ⟨y, hy⟩ with hy'
  have h1 : unipotentPair ⁅x', y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  have h2 : ⁅x', y'⁆ ∈ (antiUnipotentCenter K).subgroupOf (antiUnipotent K) := by
    rw [← ker_unipotentPair, MonoidHom.mem_ker]
    exact h1
  have h3 : ⁅x, y⁆ ∈ antiUnipotentCenter K := Subgroup.mem_subgroupOf.mp h2
  exact antiUnipotentCenter_comm h3 hz

theorem antiUnipotent_nonabelian :
    ∃ x ∈ antiUnipotent K, ∃ y ∈ antiUnipotent K, x * y ≠ y * x := by
  refine ⟨uElt 1 0 0 0, uElt_mem_antiUnipotent _ _ _ _, uElt 0 0 0 1,
    uElt_mem_antiUnipotent _ _ _ _, fun h => ?_⟩
  rw [uElt_mul, uElt_mul] at h
  obtain ⟨-, hb, -, -⟩ := uElt_eq_coords h
  norm_num at hb

variable (K) in
@[expose] def antiUnipotentR1 : Subgroup (antiSp K) where
  carrier := {g | ∃ b c d : K, g = uElt 0 b c d}
  mul_mem' := by
    rintro _ _ ⟨b, c, d, rfl⟩ ⟨B, C, D, rfl⟩
    exact ⟨b + B, c + C, d + D, by rw [uElt_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, 0, 0, uElt_zero_eq_one.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, d, rfl⟩
    exact ⟨b, c, d, by rw [uElt_inv]; congr 1; ring⟩

theorem antiUnipotentR1_le : antiUnipotentR1 K ≤ antiUnipotent K := by
  rintro _ ⟨b, c, d, rfl⟩
  exact uElt_mem_antiUnipotent _ _ _ _

theorem antiUnipotentR1_comm {x y : antiSp K} (hx : x ∈ antiUnipotentR1 K)
    (hy : y ∈ antiUnipotentR1 K) : x * y = y * x := by
  obtain ⟨b, c, d, rfl⟩ := hx
  obtain ⟨B, C, D, rfl⟩ := hy
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

theorem natCard_antiUnipotentR1 : Nat.card (antiUnipotentR1 K) = Nat.card K ^ 3 := by
  refine natCard_eq_pow_three (f := fun p : K × K × K => uElt 0 p.1 p.2.1 p.2.2) ?_ ?_ ?_
  · rintro ⟨b, c, d⟩
    exact ⟨b, c, d, rfl⟩
  · rintro ⟨b, c, d⟩ ⟨B, C, D⟩ h
    obtain ⟨-, rfl, rfl, rfl⟩ := uElt_eq_coords (h : uElt 0 b c d = uElt 0 B C D)
    rfl
  · rintro _ ⟨b, c, d, rfl⟩
    exact ⟨(b, c, d), rfl⟩

variable (K) in
@[expose] def antiUnipotentR2 : Subgroup (antiSp K) where
  carrier := {g | ∃ a b c : K, g = uElt a b c 0}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨A, B, C, rfl⟩
    exact ⟨a + A, b + B, c + C + a * B + b * A, by rw [uElt_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, 0, 0, uElt_zero_eq_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨a, b + a * 0, c, uElt_inv a b c 0⟩

theorem antiUnipotentR2_le : antiUnipotentR2 K ≤ antiUnipotent K := by
  rintro _ ⟨a, b, c, rfl⟩
  exact uElt_mem_antiUnipotent _ _ _ _

theorem antiUnipotentR2_comm {x y : antiSp K} (hx : x ∈ antiUnipotentR2 K)
    (hy : y ∈ antiUnipotentR2 K) : x * y = y * x := by
  obtain ⟨a, b, c, rfl⟩ := hx
  obtain ⟨A, B, C, rfl⟩ := hy
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

theorem natCard_antiUnipotentR2 : Nat.card (antiUnipotentR2 K) = Nat.card K ^ 3 := by
  refine natCard_eq_pow_three (f := fun p : K × K × K => uElt p.1 p.2.1 p.2.2 0) ?_ ?_ ?_
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c⟩ ⟨A, B, C⟩ h
    obtain ⟨rfl, rfl, rfl, -⟩ := uElt_eq_coords (h : uElt a b c 0 = uElt A B C 0)
    rfl
  · rintro _ ⟨a, b, c, rfl⟩
    exact ⟨(a, b, c), rfl⟩

theorem exists_elemAbelian [Finite K] :
    ∃ E : Subgroup (antiSp K), E ≤ antiUnipotent K ∧ Nat.card E = Nat.card K ^ 3 ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1 := by
  refine ⟨antiUnipotentR1 K, antiUnipotentR1_le, natCard_antiUnipotentR1,
    fun x hx y hy => antiUnipotentR1_comm hx hy, ?_⟩
  rintro _ ⟨b, c, d, rfl⟩
  rw [uElt_mul_self]
  refine (uElt_congr_coords ?_ ?_ ?_ ?_).trans uElt_zero_eq_one <;> ring

theorem exists_abelian_of_involution [Finite K] {x : antiSp K} (hx : x ∈ antiUnipotent K)
    (hx2 : x * x = 1) :
    ∃ R : Subgroup (antiSp K), R ≤ antiUnipotent K ∧ x ∈ R ∧
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ Nat.card R = Nat.card K ^ 3 := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  have hsq : uElt 0 (a * d) (a ^ 2 * d) 0 = uElt 0 0 0 0 :=
    (uElt_mul_self a b c d).symm.trans (hx2.trans uElt_zero_eq_one.symm)
  rcases mul_eq_zero.mp (uElt_eq_coords hsq).2.1 with ha | hd
  · subst ha
    exact ⟨antiUnipotentR1 K, antiUnipotentR1_le, ⟨b, c, d, rfl⟩,
      fun _ hg _ hh => antiUnipotentR1_comm hg hh, natCard_antiUnipotentR1⟩
  · subst hd
    exact ⟨antiUnipotentR2 K, antiUnipotentR2_le, ⟨a, b, c, rfl⟩,
      fun _ hg _ hh => antiUnipotentR2_comm hg hh, natCard_antiUnipotentR2⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
