module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace QuaternionMatrices

open Matrix

section Lift

variable {G : Type*} [Group G] {x y : G}

theorem pow_val_add (hx4 : x ^ 4 = 1) (i j : ZMod 4) :
    x ^ (i + j).val = x ^ i.val * x ^ j.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx4]

theorem pow_mul_eq_mul_inv (hyx : y * x * y⁻¹ = x⁻¹) (m : ℕ) : x ^ m * y = y * (x ^ m)⁻¹ := by
  have h : y * x ^ m * y⁻¹ = (x ^ m)⁻¹ := by
    have := map_pow (MulAut.conj y) x m
    rw [MulAut.conj_apply, MulAut.conj_apply, hyx, inv_pow] at this
    exact this
  have h2 : y * (x ^ m)⁻¹ * y⁻¹ = x ^ m := by
    have := map_inv (MulAut.conj y) (x ^ m)
    rw [MulAut.conj_apply, MulAut.conj_apply, h, inv_inv] at this
    exact this
  calc x ^ m * y = y * (x ^ m)⁻¹ * y⁻¹ * y := by rw [h2]
    _ = y * (x ^ m)⁻¹ := by group

@[expose] def quaternionLift (hx4 : x ^ 4 = 1) (hyx : y * x * y⁻¹ = x⁻¹) (hy2 : y ^ 2 = x ^ 2) :
    QuaternionGroup 2 →* G where
  toFun g := match g with
    | .a k => x ^ k.val
    | .xa k => y * x ^ k.val
  map_one' := by
    change x ^ (0 : ZMod 4).val = 1
    simp
  map_mul' g h := by
    have hc : ∀ m n : ℕ, Commute (x ^ m) (x ^ n) := fun m n => Commute.pow_pow_self x m n
    rcases g with i | i <;> rcases h with j | j
    · change x ^ (i + j).val = x ^ i.val * x ^ j.val
      exact pow_val_add hx4 i j
    · rw [QuaternionGroup.a_mul_xa]
      change y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      have h1 : x ^ (j - i).val * x ^ i.val = x ^ j.val := by
        rw [← pow_val_add hx4, sub_add_cancel]
      rw [← mul_assoc, pow_mul_eq_mul_inv hyx, ← h1, mul_assoc, ← (hc _ _).eq]
      group
    · rw [QuaternionGroup.xa_mul_a]
      change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [pow_val_add hx4, mul_assoc]
    · rw [QuaternionGroup.xa_mul_xa]
      change x ^ ((2 : ℕ) + j - i : ZMod 4).val = y * x ^ i.val * (y * x ^ j.val)
      have h1 : x ^ ((2 : ℕ) + j - i : ZMod 4).val * x ^ i.val = x ^ 2 * x ^ j.val := by
        rw [← pow_val_add hx4, sub_add_cancel, pow_val_add hx4]
        rfl
      have h2 : x ^ ((2 : ℕ) + j - i : ZMod 4).val = x ^ 2 * x ^ j.val * (x ^ i.val)⁻¹ := by
        rw [← h1]
        group
      have hyy : y * y = x ^ 2 := by rw [← hy2, sq]
      rw [h2]
      calc x ^ 2 * x ^ j.val * (x ^ i.val)⁻¹ = x ^ 2 * ((x ^ i.val)⁻¹ * x ^ j.val) := by
            rw [mul_assoc, ((hc i.val j.val).inv_left.eq).symm]
        _ = y * y * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [hyy]
        _ = y * (y * (x ^ i.val)⁻¹) * x ^ j.val := by group
        _ = y * (x ^ i.val * y) * x ^ j.val := by rw [pow_mul_eq_mul_inv hyx]
        _ = y * x ^ i.val * (y * x ^ j.val) := by group

theorem quaternionLift_a (hx4 : x ^ 4 = 1) (hyx : y * x * y⁻¹ = x⁻¹) (hy2 : y ^ 2 = x ^ 2)
    (k : ZMod 4) : quaternionLift hx4 hyx hy2 (.a k) = x ^ k.val :=
  rfl

theorem quaternionLift_xa (hx4 : x ^ 4 = 1) (hyx : y * x * y⁻¹ = x⁻¹) (hy2 : y ^ 2 = x ^ 2)
    (k : ZMod 4) : quaternionLift hx4 hyx hy2 (.xa k) = y * x ^ k.val :=
  rfl

end Lift

variable {K : Type*} [Field K]

variable (K) in
@[expose] def quatI : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; -1, 0]

@[expose] def quatJ (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a, b; b, -a]

theorem neg_one_fin_two : (-1 : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_quatI : (quatI K).det = 1 := by
  simp [quatI, det_fin_two]

theorem det_quatJ {a b : K} (h : a ^ 2 + b ^ 2 = -1) : (quatJ a b).det = 1 := by
  simp only [quatJ, det_fin_two_of]
  linear_combination -h

theorem quatI_mul_self : quatI K * quatI K = -1 := by
  rw [quatI, Matrix.mul_fin_two, neg_one_fin_two]
  simp

theorem quatJ_mul_self {a b : K} (h : a ^ 2 + b ^ 2 = -1) : quatJ a b * quatJ a b = -1 := by
  rw [quatJ, Matrix.mul_fin_two, neg_one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination h

theorem quatI_mul_quatJ (a b : K) : quatI K * quatJ a b = !![b, -a; -a, -b] := by
  rw [quatI, quatJ, Matrix.mul_fin_two]
  simp

theorem quatJ_mul_quatI (a b : K) : quatJ a b * quatI K = !![-b, a; a, b] := by
  rw [quatI, quatJ, Matrix.mul_fin_two]
  simp

theorem quatI_mul_quatJ_eq_neg (a b : K) : quatI K * quatJ a b = -(quatJ a b * quatI K) := by
  rw [quatI_mul_quatJ, quatJ_mul_quatI]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable (K) in
@[expose] def slQuatI : SpecialLinearGroup (Fin 2) K :=
  ⟨quatI K, det_quatI⟩

@[expose] def slQuatJ {a b : K} (h : a ^ 2 + b ^ 2 = -1) : SpecialLinearGroup (Fin 2) K :=
  ⟨quatJ a b, det_quatJ h⟩

theorem coe_slQuatI_sq : ((slQuatI K ^ 2 : SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = -1 := by
  rw [SpecialLinearGroup.coe_pow, sq]
  exact quatI_mul_self

theorem slQuatI_pow_four : slQuatI K ^ 4 = 1 := by
  apply Subtype.ext
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, SpecialLinearGroup.coe_pow, coe_slQuatI_sq]
  simp

theorem slQuatJ_sq {a b : K} (h : a ^ 2 + b ^ 2 = -1) : slQuatJ h ^ 2 = slQuatI K ^ 2 := by
  apply Subtype.ext
  rw [coe_slQuatI_sq, SpecialLinearGroup.coe_pow, sq]
  exact quatJ_mul_self h

theorem coe_slQuatI_inv : ((slQuatI K)⁻¹ : SpecialLinearGroup (Fin 2) K) =
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
  rw [SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slQuatI, quatI]

theorem slQuatJ_conj {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    slQuatJ h * slQuatI K * (slQuatJ h)⁻¹ = (slQuatI K)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_slQuatI_inv]
  change quatJ a b * quatI K = !![0, -1; 1, 0] * quatJ a b
  rw [quatJ_mul_quatI, quatJ, Matrix.mul_fin_two]
  simp

@[expose] noncomputable def quatHom {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 →* SpecialLinearGroup (Fin 2) K :=
  quaternionLift slQuatI_pow_four (slQuatJ_conj h) (slQuatJ_sq h)

theorem coe_quatHom_a {a b : K} (h : a ^ 2 + b ^ 2 = -1) (k : ZMod 4) :
    (quatHom h (.a k) : Matrix (Fin 2) (Fin 2) K) = quatI K ^ k.val := by
  rw [quatHom, quaternionLift_a, SpecialLinearGroup.coe_pow]
  rfl

theorem coe_quatHom_xa {a b : K} (h : a ^ 2 + b ^ 2 = -1) (k : ZMod 4) :
    (quatHom h (.xa k) : Matrix (Fin 2) (Fin 2) K) = quatJ a b * quatI K ^ k.val := by
  rw [quatHom, quaternionLift_xa, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow]
  rfl

theorem quatI_pow_three : quatI K ^ 3 = -quatI K := by
  rw [pow_succ, sq, quatI_mul_self, neg_one_mul]

theorem neg_one_ne_one_matrix (hK : ringChar K ≠ 2) : (-1 : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
  intro h1
  have := congrFun (congrFun h1 0) 0
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact Ring.neg_one_ne_one_of_char_ne_two hK this

theorem quatHom_injective (hK : ringChar K ≠ 2) {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    Function.Injective (quatHom h) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hsq : ∀ g : QuaternionGroup 2, g ≠ 1 → g = .a 2 ∨ g ^ 2 = .a 2 := by decide
  have h2 : quatHom h (.a 2) ≠ 1 := by
    intro h1
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) h1
    simp only [coe_quatHom_a, SpecialLinearGroup.coe_one] at this
    rw [show (2 : ZMod 4).val = 2 from rfl, sq, quatI_mul_self] at this
    exact neg_one_ne_one_matrix hK this
  by_contra hne
  rcases hsq g hne with rfl | hg2
  · exact h2 hg
  · apply h2
    rw [← hg2, map_pow, hg, one_pow]

theorem quaternion_center (g : QuaternionGroup 2) (hg : ∀ x, g * x = x * g) :
    g = 1 ∨ g = .a 2 := by
  revert g
  decide

section Values

variable {a b : K} (h : a ^ 2 + b ^ 2 = -1)
include h

theorem quatHom_a_zero : (quatHom h (.a 0) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [coe_quatHom_a, show (0 : ZMod 4).val = 0 from rfl, pow_zero]

theorem quatHom_a_one : (quatHom h (.a 1) : Matrix (Fin 2) (Fin 2) K) = quatI K := by
  rw [coe_quatHom_a, show (1 : ZMod 4).val = 1 from rfl, pow_one]

theorem quatHom_a_two : (quatHom h (.a 2) : Matrix (Fin 2) (Fin 2) K) = -1 := by
  rw [coe_quatHom_a, show (2 : ZMod 4).val = 2 from rfl, sq, quatI_mul_self]

theorem quatHom_a_three : (quatHom h (.a 3) : Matrix (Fin 2) (Fin 2) K) = -quatI K := by
  rw [coe_quatHom_a, show (3 : ZMod 4).val = 3 from rfl, quatI_pow_three]

theorem quatHom_xa_zero : (quatHom h (.xa 0) : Matrix (Fin 2) (Fin 2) K) = quatJ a b := by
  rw [coe_quatHom_xa, show (0 : ZMod 4).val = 0 from rfl, pow_zero, Matrix.mul_one]

theorem quatHom_xa_one :
    (quatHom h (.xa 1) : Matrix (Fin 2) (Fin 2) K) = -(quatI K * quatJ a b) := by
  rw [coe_quatHom_xa, show (1 : ZMod 4).val = 1 from rfl, pow_one, quatI_mul_quatJ_eq_neg,
    neg_neg]

theorem quatHom_xa_two : (quatHom h (.xa 2) : Matrix (Fin 2) (Fin 2) K) = -quatJ a b := by
  rw [coe_quatHom_xa, show (2 : ZMod 4).val = 2 from rfl, sq, quatI_mul_self, Matrix.mul_neg,
    Matrix.mul_one]

theorem quatHom_xa_three :
    (quatHom h (.xa 3) : Matrix (Fin 2) (Fin 2) K) = quatI K * quatJ a b := by
  rw [coe_quatHom_xa, show (3 : ZMod 4).val = 3 from rfl, quatI_pow_three, Matrix.mul_neg,
    quatI_mul_quatJ_eq_neg]

end Values

theorem odd_field_two_dimensional_quaternion_matrices [Finite K] (hK : ringChar K ≠ 2) :
    (∃ a b : K, a ^ 2 + b ^ 2 = -1) ∧
    ∀ a b : K, a ^ 2 + b ^ 2 = -1 →
      (quatI K).det = 1 ∧ (quatJ a b).det = 1 ∧ quatI K * quatI K = -1 ∧
      quatJ a b * quatJ a b = -1 ∧ quatI K * quatJ a b = -(quatJ a b * quatI K) ∧
      ∃ Q : Subgroup (SpecialLinearGroup (Fin 2) K),
        (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) '' Q =
          {1, -1, quatI K, -quatI K, quatJ a b, -quatJ a b, quatI K * quatJ a b,
            -(quatI K * quatJ a b)} ∧
        Nat.card Q = 8 ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
        ∀ g ∈ Q, (∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) c) ↔
          ((g : Matrix (Fin 2) (Fin 2) K) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) K) = -1) := by
  have hex : ∃ a b : K, a ^ 2 + b ^ 2 = -1 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
    obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
    refine ⟨ZMod.castHom (dvd_refl p) K a, ZMod.castHom (dvd_refl p) K b, ?_⟩
    rw [← map_pow, ← map_pow, ← map_add, hab]
    simp
  refine ⟨hex, fun a b h => ⟨det_quatI, det_quatJ h, quatI_mul_self, quatJ_mul_self h,
    quatI_mul_quatJ_eq_neg a b, (quatHom h).range, ?_, ?_, ⟨?_⟩, ?_⟩⟩
  · ext M
    simp only [Set.mem_image, SetLike.mem_coe, MonoidHom.mem_range, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      rcases g with k | k <;> fin_cases k
      · exact Or.inl (quatHom_a_zero h)
      · exact Or.inr (Or.inr (Or.inl (quatHom_a_one h)))
      · exact Or.inr (Or.inl (quatHom_a_two h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (quatHom_a_three h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (quatHom_xa_zero h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (quatHom_xa_one h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (quatHom_xa_two h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (quatHom_xa_three h)))))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨_, ⟨.a 0, rfl⟩, quatHom_a_zero h⟩
      · exact ⟨_, ⟨.a 2, rfl⟩, quatHom_a_two h⟩
      · exact ⟨_, ⟨.a 1, rfl⟩, quatHom_a_one h⟩
      · exact ⟨_, ⟨.a 3, rfl⟩, quatHom_a_three h⟩
      · exact ⟨_, ⟨.xa 0, rfl⟩, quatHom_xa_zero h⟩
      · exact ⟨_, ⟨.xa 2, rfl⟩, quatHom_xa_two h⟩
      · exact ⟨_, ⟨.xa 3, rfl⟩, quatHom_xa_three h⟩
      · exact ⟨_, ⟨.xa 1, rfl⟩, quatHom_xa_one h⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective (quatHom_injective hK h)).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  · exact (MonoidHom.ofInjective (quatHom_injective hK h)).symm
  · rintro _ ⟨g, rfl⟩
    constructor
    · rintro ⟨c, hc⟩
      have hcomm : ∀ y, g * y = y * g := by
        intro y
        apply quatHom_injective hK h
        apply Subtype.ext
        rw [map_mul, map_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hc]
        exact (scalar_commute c (fun _ => Commute.all _ _) _).eq
      rcases quaternion_center g hcomm with rfl | rfl
      · exact Or.inl (by rw [map_one, SpecialLinearGroup.coe_one])
      · exact Or.inr (quatHom_a_two h)
    · rintro (h1 | h1)
      · exact ⟨1, by rw [h1, map_one]⟩
      · exact ⟨-1, by rw [h1, map_neg, map_one]⟩

end QuaternionMatrices

end CFSG.LocalAnalysis.ComponentInitial
