module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.RankOne.SzEight

abbrev V : Type := ZMod 2 × ZMod 2 × ZMod 2

@[expose] def mul (v w : V) : V :=
  (v.1 * w.1 + v.2.1 * w.2.2 + v.2.2 * w.2.1,
    v.1 * w.2.1 + v.2.1 * w.1 + v.2.1 * w.2.2 + v.2.2 * w.2.1 + v.2.2 * w.2.2,
    v.1 * w.2.2 + v.2.1 * w.2.1 + v.2.2 * w.1 + v.2.2 * w.2.2)

@[expose] def pow5 (v : V) : V :=
  (v.1 + v.2.1 + v.2.2 + v.2.1 * v.2.2, v.2.1 + v.2.2 + v.1 * v.2.2,
    v.2.1 + v.1 * v.2.1 + v.1 * v.2.2)

@[expose] def pow3 (v : V) : V :=
  (v.1 + v.2.1 + v.2.2 + v.2.1 * v.2.2, v.2.1 + v.1 * v.2.1 + v.1 * v.2.2, v.1 * v.2.1 + v.2.2)

theorem pow5_eq_mul (v : V) : pow5 v = mul v (mul v (mul v (mul v v))) := by
  revert v
  decide +kernel

theorem pow3_pow5 (v : V) : pow3 (pow5 v) = v := by
  revert v
  decide +kernel

theorem pow5_pow3 (v : V) : pow5 (pow3 v) = v := by
  revert v
  decide +kernel

theorem exists_mul_eq_one (v : V) (hv : v ≠ 0) : ∃ w, mul v w = (1, 0, 0) := by
  revert v
  decide +kernel

@[expose] def lin (t : V × V × V) (v : V) : V := v.1 • t.1 + v.2.1 • t.2.1 + v.2.2 • t.2.2

theorem lin_add (t : V × V × V) (v w : V) : lin t (v + w) = lin t v + lin t w := by
  simp only [lin, Prod.fst_add, Prod.snd_add, add_smul]
  abel

@[expose] def linHom (t : V × V × V) : V →+ V := AddMonoidHom.mk' (lin t) (lin_add t)

theorem linHom_apply (t : V × V × V) (v : V) : linHom t v = lin t v := rfl

theorem lin_basis (t : V × V × V) :
    lin t (1, 0, 0) = t.1 ∧ lin t (0, 1, 0) = t.2.1 ∧ lin t (0, 0, 1) = t.2.2 := by
  simp [lin]

theorem eq_lin (f : V →+ V) (v : V) : f v = lin (f (1, 0, 0), f (0, 1, 0), f (0, 0, 1)) v := by
  have hv : v = v.1 • ((1, 0, 0) : V) + v.2.1 • ((0, 1, 0) : V) + v.2.2 • ((0, 0, 1) : V) := by
    obtain ⟨a, b, c⟩ := v
    ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, ZMod.map_smul, lin]

@[expose] def twist (t : V × V × V) (v : V) : V := pow3 (lin t (pow5 v))

@[expose] def Admissible (t : V × V × V) : Prop :=
  (∀ v, twist t v = lin (twist t (1, 0, 0), twist t (0, 1, 0), twist t (0, 0, 1)) v) ∧
    ∀ v, lin t v = 0 → v = 0

@[expose] def toB (a : ZMod 2) : Bool := decide (a = 1)

theorem toB_add (a b : ZMod 2) : toB (a + b) = (toB a ^^ toB b) := by
  revert a b
  decide +kernel

theorem toB_mul (a b : ZMod 2) : toB (a * b) = (toB a && toB b) := by
  revert a b
  decide +kernel

theorem toB_injective : Function.Injective toB := by
  intro a b
  revert a b
  decide +kernel

theorem toB_surjective : Function.Surjective toB := by
  intro b
  revert b
  decide +kernel

abbrev B : Type := Bool × Bool × Bool

@[expose] def toW (v : V) : B := (toB v.1, toB v.2.1, toB v.2.2)

@[expose] def toW3 (t : V × V × V) : B × B × B := (toW t.1, toW t.2.1, toW t.2.2)

@[expose] def pow5B (v : B) : B :=
  ((v.1 ^^ v.2.1) ^^ v.2.2 ^^ (v.2.1 && v.2.2), (v.2.1 ^^ v.2.2) ^^ (v.1 && v.2.2),
    (v.2.1 ^^ (v.1 && v.2.1)) ^^ (v.1 && v.2.2))

@[expose] def pow3B (v : B) : B :=
  ((v.1 ^^ v.2.1) ^^ v.2.2 ^^ (v.2.1 && v.2.2), (v.2.1 ^^ (v.1 && v.2.1)) ^^ (v.1 && v.2.2),
    (v.1 && v.2.1) ^^ v.2.2)

@[expose] def linB (t : B × B × B) (v : B) : B :=
  (((v.1 && t.1.1) ^^ (v.2.1 && t.2.1.1)) ^^ (v.2.2 && t.2.2.1),
    ((v.1 && t.1.2.1) ^^ (v.2.1 && t.2.1.2.1)) ^^ (v.2.2 && t.2.2.2.1),
    ((v.1 && t.1.2.2) ^^ (v.2.1 && t.2.1.2.2)) ^^ (v.2.2 && t.2.2.2.2))

@[expose] def twistB (t : B × B × B) (v : B) : B := pow3B (linB t (pow5B v))

@[expose] def AdmissibleB (t : B × B × B) : Prop :=
  (∀ v, twistB t v = linB (twistB t (true, false, false), twistB t (false, true, false),
      twistB t (false, false, true)) v) ∧
    ∀ v, linB t v = (false, false, false) → v = (false, false, false)

instance : DecidablePred AdmissibleB := fun t => by
  unfold AdmissibleB
  infer_instance

theorem toW_injective : Function.Injective toW := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [toW, Prod.mk.injEq] at h
  rw [toB_injective h.1, toB_injective h.2.1, toB_injective h.2.2]

theorem toW_surjective : Function.Surjective toW := by
  rintro ⟨a, b, c⟩
  obtain ⟨a', rfl⟩ := toB_surjective a
  obtain ⟨b', rfl⟩ := toB_surjective b
  obtain ⟨c', rfl⟩ := toB_surjective c
  exact ⟨(a', b', c'), rfl⟩

theorem toW_pow5 (v : V) : toW (pow5 v) = pow5B (toW v) := by
  simp only [toW, pow5, pow5B, toB_add, toB_mul]

theorem toW_pow3 (v : V) : toW (pow3 v) = pow3B (toW v) := by
  simp only [toW, pow3, pow3B, toB_add, toB_mul]

theorem toW_lin (t : V × V × V) (v : V) : toW (lin t v) = linB (toW3 t) (toW v) := by
  simp only [toW, toW3, lin, linB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, toB_add, toB_mul]

theorem toW_twist (t : V × V × V) (v : V) : toW (twist t v) = twistB (toW3 t) (toW v) := by
  rw [twist, twistB, toW_pow3, toW_lin, toW_pow5]

theorem toW3_mk (a b c : V) : toW3 (a, b, c) = (toW a, toW b, toW c) := rfl

theorem admissible_iff (t : V × V × V) : Admissible t ↔ AdmissibleB (toW3 t) := by
  have hb₀ : toW ((1, 0, 0) : V) = (true, false, false) := by decide +kernel
  have hb₁ : toW ((0, 1, 0) : V) = (false, true, false) := by decide +kernel
  have hb₂ : toW ((0, 0, 1) : V) = (false, false, true) := by decide +kernel
  have h₀ : toW (0 : V) = (false, false, false) := by decide +kernel
  refine and_congr ?_ ?_
  · rw [toW_surjective.forall]
    refine forall_congr' fun v => ?_
    rw [← toW_injective.eq_iff]
    simp only [toW_twist, toW_lin, toW3_mk, hb₀, hb₁, hb₂]
  · rw [toW_surjective.forall]
    refine forall_congr' fun v => ?_
    rw [← toW_injective.eq_iff, ← toW_injective.eq_iff (b := 0), toW_lin, h₀]

instance : DecidablePred Admissible := fun t => decidable_of_iff _ (admissible_iff t).symm

theorem card_admissible : Fintype.card {t : V × V × V // Admissible t} = 21 := by
  decide +kernel

section Field

variable {K : Type*} [Field K]

theorem charP_two_of_card_eq_eight [Finite K] (hK : Nat.card K = 8) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := 3)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

theorem exists_pow_three_eq_add_one [Finite K] (hK : Nat.card K = 8) :
    ∃ α : K, α ^ 3 = α + 1 := by
  classical
  have : CharP K 2 := charP_two_of_card_eq_eight hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨g, hg0, hg1⟩ : ∃ g : K, g ≠ 0 ∧ g ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
    rw [Finset.card_univ, hcard] at h1
    omega
  have h7 : g ^ 7 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one g hg0
    rwa [hcard] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hprod : (g + 1) * ((g ^ 3 + g + 1) * (g ^ 3 + g ^ 2 + 1)) = 0 := by
    linear_combination h7 + (1 + g + g ^ 2 + 2 * g ^ 3 + 2 * g ^ 4 + g ^ 5 + g ^ 6) * h2
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (by linear_combination h - h2) hg1
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨g, by linear_combination h - (g + 1) * h2⟩
  · have hgα : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    refine ⟨g⁻¹, ?_⟩
    linear_combination (-g⁻¹ ^ 3) * h + g⁻¹ ^ 3 * h2 +
      (g⁻¹ * (g * g⁻¹ + 1) + (g * g⁻¹) ^ 2 + g * g⁻¹ + 1) * hgα

variable [CharP K 2]

@[expose] def coord (α : K) : V →+ K where
  toFun v := ZMod.castHom (dvd_refl 2) K v.1 + ZMod.castHom (dvd_refl 2) K v.2.1 * α +
    ZMod.castHom (dvd_refl 2) K v.2.2 * α ^ 2
  map_zero' := by simp
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem coord_apply (α : K) (v : V) : coord α v = ZMod.castHom (dvd_refl 2) K v.1 +
    ZMod.castHom (dvd_refl 2) K v.2.1 * α + ZMod.castHom (dvd_refl 2) K v.2.2 * α ^ 2 :=
  rfl

theorem coord_one (α : K) : coord α (1, 0, 0) = 1 := by
  simp [coord_apply]

theorem coord_mul {α : K} (hα : α ^ 3 = α + 1) (v w : V) :
    coord α (mul v w) = coord α v * coord α w := by
  simp only [coord_apply, mul, map_add, map_mul]
  linear_combination (-(ZMod.castHom (dvd_refl 2) K v.2.1 * ZMod.castHom (dvd_refl 2) K w.2.2 +
    ZMod.castHom (dvd_refl 2) K v.2.2 * ZMod.castHom (dvd_refl 2) K w.2.1 +
    ZMod.castHom (dvd_refl 2) K v.2.2 * ZMod.castHom (dvd_refl 2) K w.2.2 * α)) * hα

theorem coord_pow5 {α : K} (hα : α ^ 3 = α + 1) (v : V) : coord α (pow5 v) = coord α v ^ 5 := by
  rw [pow5_eq_mul, coord_mul hα, coord_mul hα, coord_mul hα, coord_mul hα]
  ring

theorem coord_injective {α : K} (hα : α ^ 3 = α + 1) : Function.Injective (coord α) := by
  refine (injective_iff_map_eq_zero (coord α)).2 fun v hv => ?_
  by_contra hne
  obtain ⟨w, hw⟩ := exists_mul_eq_one v hne
  have h1 := congrArg (coord α) hw
  rw [coord_mul hα, hv, zero_mul, coord_one] at h1
  exact zero_ne_one h1

theorem coord_bijective [Finite K] (hK : Nat.card K = 8) {α : K} (hα : α ^ 3 = α + 1) :
    Function.Bijective (coord α) :=
  (Nat.bijective_iff_injective_and_card _).2 ⟨coord_injective hα, by simp [hK]⟩

end Field

theorem exists_addEquiv_pow_five {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ∃ e : V ≃+ K, ∀ v, e (pow5 v) = e v ^ 5 := by
  have : CharP K 2 := charP_two_of_card_eq_eight hK
  obtain ⟨α, hα⟩ := exists_pow_three_eq_add_one hK
  exact ⟨AddEquiv.ofBijective (coord α) (coord_bijective hK hα), coord_pow5 hα⟩

end CFSG.SeitzReduction.RankOne.SzEight
