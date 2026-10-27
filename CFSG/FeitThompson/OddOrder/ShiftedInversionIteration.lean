module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.Foundations.CounterorderedPrimeParity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section NormOne

variable (F : Type*) [Field F] (m : ℕ)

def normOneSubgroup : Subgroup Fˣ := (powMonoidHom m : Fˣ →* Fˣ).ker

def normOneShiftSet : Set F := {z | z ^ m = 1 ∧ (2 - z) ^ m = 1}

def normOneShiftSubset : Set (normOneSubgroup F m) := {u | (2 - ((u : Fˣ) : F)) ^ m = 1}

variable {F m}

@[simp] theorem mem_normOneSubgroup {u : Fˣ} : u ∈ normOneSubgroup F m ↔ u ^ m = 1 := by
  simp [normOneSubgroup, MonoidHom.mem_ker, powMonoidHom]

@[simp] theorem mem_normOneShiftSet {z : F} :
    z ∈ normOneShiftSet F m ↔ z ^ m = 1 ∧ (2 - z) ^ m = 1 := Iff.rfl

@[simp] theorem mem_normOneShiftSubset {u : normOneSubgroup F m} :
    u ∈ normOneShiftSubset F m ↔ (2 - ((u : Fˣ) : F)) ^ m = 1 := Iff.rfl

theorem pow_eq_one_of_mem_normOneSubgroup {u : Fˣ} (hu : u ∈ normOneSubgroup F m) :
    ((u : F)) ^ m = 1 := by
  simpa using congrArg Units.val ((mem_normOneSubgroup (u := u)).1 hu)

private theorem two_sub_one_pow_eq_one : ((2 : F) - 1) ^ m = 1 := by
  rw [← one_add_one_eq_two, add_sub_cancel_right, one_pow]

theorem one_mem_normOneShiftSet : (1 : F) ∈ normOneShiftSet F m :=
  ⟨one_pow m, two_sub_one_pow_eq_one⟩

theorem one_mem_normOneShiftSubset : (1 : normOneSubgroup F m) ∈ normOneShiftSubset F m := by
  change (2 - ((1 : Fˣ) : F)) ^ m = 1
  rw [Units.val_one, two_sub_one_pow_eq_one]

theorem ne_zero_of_mem_normOneShiftSet (hm : m ≠ 0) {z : F} (hz : z ∈ normOneShiftSet F m) :
    z ≠ 0 := by
  rintro rfl
  simpa [hm] using hz.1

theorem image_normOneShiftSubset (hm : m ≠ 0) :
    (fun u : normOneSubgroup F m => ((u : Fˣ) : F)) '' normOneShiftSubset F m
      = normOneShiftSet F m := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨pow_eq_one_of_mem_normOneSubgroup u.2, hu⟩
  · rintro z ⟨h1, h2⟩
    have hz : z ≠ 0 := ne_zero_of_mem_normOneShiftSet hm ⟨h1, h2⟩
    refine ⟨⟨Units.mk0 z hz, ?_⟩, ?_, rfl⟩
    · simpa [Units.ext_iff] using h1
    · simpa using h2

def normOneShiftImage {G : Type*} [Group G] (Ue : normOneSubgroup F m → G) : Set G :=
  Ue '' normOneShiftSubset F m

theorem mem_normOneShiftImage {G : Type*} [Group G] {Ue : normOneSubgroup F m → G} {g : G} :
    g ∈ normOneShiftImage Ue ↔ ∃ u ∈ normOneShiftSubset F m, Ue u = g := Iff.rfl

theorem one_mem_normOneShiftImage {G : Type*} [Group G] (Ue : normOneSubgroup F m →* G) :
    (1 : G) ∈ normOneShiftImage (Ue : normOneSubgroup F m → G) :=
  ⟨1, one_mem_normOneShiftSubset, map_one Ue⟩

end NormOne

section ShiftedInv

variable {G : Type*} [Group G]

def shiftedInv (t a : G) : G := (t ^ 3)⁻¹ * a⁻¹ * t ^ 3

theorem shiftedInv_apply (t a : G) : shiftedInv t a = (t ^ 3)⁻¹ * a⁻¹ * t ^ 3 := (rfl)

@[simp] theorem shiftedInv_one (t : G) : shiftedInv t 1 = 1 := by simp [shiftedInv_apply]

theorem shiftedInv_injective (t : G) : Function.Injective (shiftedInv t) := by
  intro a b hab
  simp only [shiftedInv_apply] at hab
  simpa using mul_left_cancel (mul_right_cancel hab)

theorem iterate_shiftedInv (t : G) (k : ℕ) (a : G) :
    (shiftedInv t)^[k] a = (t ^ (3 * k))⁻¹ * a ^ ((-1 : ℤ) ^ k) * t ^ (3 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : a ^ ((-1 : ℤ) ^ (k + 1)) = (a ^ ((-1 : ℤ) ^ k))⁻¹ := by
      rw [pow_succ, zpow_mul, zpow_neg_one]
    have h3 : t ^ (3 * (k + 1)) = t ^ (3 * k) * t ^ 3 := by rw [← pow_add, Nat.mul_succ]
    rw [Function.iterate_succ_apply', ih, shiftedInv_apply, hz, h3]
    group

theorem iterate_shiftedInv_eq_inv {t : G} {n : ℕ} (hn : Odd n) (ht : t ^ n = 1) (a : G) :
    (shiftedInv t)^[n] a = a⁻¹ := by
  have h1 : t ^ (3 * n) = 1 := by rw [mul_comm, pow_mul, ht, one_pow]
  rw [iterate_shiftedInv, h1, hn.neg_one_pow]
  simp

theorem inv_mem_of_mapsTo_shiftedInv {t : G} {n : ℕ} (hn : Odd n) (ht : t ^ n = 1) {E : Set G}
    (hE : Set.MapsTo (shiftedInv t) E E) {a : G} (ha : a ∈ E) : a⁻¹ ∈ E := by
  have h := hE.iterate n ha
  rwa [iterate_shiftedInv_eq_inv hn ht] at h

theorem conj_pow_eq_one {x y : G} {n : ℕ} (h : x ^ n = 1) : (y⁻¹ * x * y) ^ n = 1 := by
  have hc : (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y := by
    simpa using conj_pow (a := y⁻¹) (b := x) (i := n)
  rw [hc, h, mul_one, inv_mul_cancel]

end ShiftedInv

section AppendixC

variable {G : Type*} [Group G] {F : Type*} [Field F] [Fintype F] {p q m : ℕ}

theorem cast_eq_zero_of_card_eq (hq : q ≠ 0) (hcard : Fintype.card F = p ^ q) : (p : F) = 0 := by
  have h : ((p : F)) ^ q = 0 := by
    have h0 := Nat.cast_card_eq_zero F
    rw [hcard] at h0
    simpa using h0
  exact pow_eq_zero_iff hq |>.mp h

theorem pow_apply_ofAdd_one_eq_one (hq : q ≠ 0) (hcard : Fintype.card F = p ^ q)
    (Pe : Multiplicative F →* G) : Pe (Multiplicative.ofAdd (1 : F)) ^ p = 1 := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, cast_eq_zero_of_card_eq hq hcard]
  simp

theorem pow_conj_apply_ofAdd_one_eq_one (hq : q ≠ 0) (hcard : Fintype.card F = p ^ q)
    (Pe : Multiplicative F →* G) (y : G) :
    (y⁻¹ * Pe (Multiplicative.ofAdd (1 : F)) * y) ^ p = 1 :=
  conj_pow_eq_one (pow_apply_ofAdd_one_eq_one hq hcard Pe)

theorem inv_mem_normOneShiftImage_of_mapsTo_shiftedInv (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Fintype.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) {P U : Subgroup G} (Pe : Multiplicative F ≃* P)
    (Ue : normOneSubgroup F m ≃* U) (y : G)
    (hE : Set.MapsTo (shiftedInv (y⁻¹ * (Pe (Multiplicative.ofAdd (1 : F)) : G) * y))
      (normOneShiftImage fun u => (Ue u : G)) (normOneShiftImage fun u => (Ue u : G)))
    {a : G} (ha : a ∈ normOneShiftImage fun u => (Ue u : G)) :
    a⁻¹ ∈ normOneShiftImage fun u => (Ue u : G) :=
  inv_mem_of_mapsTo_shiftedInv
    (odd_of_coprime_pow_sub_one_div_sub_one hp hq hqp (hm ▸ hcop)).2.2.1
    (pow_conj_apply_ofAdd_one_eq_one hq.ne_zero hcard (P.subtype.comp Pe.toMonoidHom) y) hE ha

theorem inv_mem_normOneShiftImage_of_shiftedInv_mem (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Fintype.card F = p ^ q) (hm : m = (p ^ q - 1) / (p - 1))
    (hcop : Nat.Coprime m (p - 1)) {P U : Subgroup G} (Pe : Multiplicative F ≃* P)
    (Ue : normOneSubgroup F m ≃* U) (_hPU : P ⊓ U = ⊥)
    (_hact : ∀ (z : F) (u : normOneSubgroup F m),
      (Ue u : G)⁻¹ * (Pe (Multiplicative.ofAdd z) : G) * (Ue u : G)
        = (Pe (Multiplicative.ofAdd (z * ((u : Fˣ) : F))) : G))
    {P₀ Q : Subgroup G}
    (_hP₀ : P₀ = (Subgroup.zpowers (Multiplicative.ofAdd (1 : F))).map (P.subtype.comp Pe))
    (_hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (_hQp : Nat.Coprime (Nat.card Q) p)
    (_hQnorm : P₀ ≤ Subgroup.normalizer Q) {y : G} (_hy : y ∈ Q)
    (_hP₁ : P₀.map (MulAut.conj y⁻¹).toMonoidHom ≤ Subgroup.normalizer U)
    (_hycomm : y ∈ ⁅Q, P₀⁆) {s t : G} (hs : s = (Pe (Multiplicative.ofAdd (1 : F)) : G))
    (ht : t = y⁻¹ * s * y)
    (hE : ∀ a ∈ normOneShiftImage fun u => (Ue u : G),
      shiftedInv t a ∈ normOneShiftImage fun u => (Ue u : G))
    {a : G} (ha : a ∈ normOneShiftImage fun u => (Ue u : G)) :
    a⁻¹ ∈ normOneShiftImage fun u => (Ue u : G) := by
  subst hs ht
  exact inv_mem_normOneShiftImage_of_mapsTo_shiftedInv hp hq hqp hcard hm hcop Pe Ue y hE ha

end AppendixC

end CFSG.FeitThompson
