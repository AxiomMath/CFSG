module

public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuaternionGroup

section Quaternion

variable {G : Type*} [Group G]

theorem exists_quaternion_subgroup_of_anticommuting {x y z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hx : x ^ 2 = z) (hy : y ^ 2 = z) (hxy : x * y = z * (y * x)) :
    ∃ H : Subgroup G, x ∈ H ∧ y ∈ H ∧ Nonempty (QuaternionGroup 2 ≃* H) := by
  set H := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  refine ⟨H, hxH, hyH, ?_⟩
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hgen : Subgroup.closure ({⟨x, hxH⟩, ⟨y, hyH⟩} : Set H) = ⊤ := by
    convert Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set G)) using 2
    ext g
    simp [Subtype.ext_iff]
  have hxo : orderOf (⟨x, hxH⟩ : H) = 2 * 2 := by
    rw [Subgroup.orderOf_mk]
    refine orderOf_eq_prime_pow (n := 1) (by rwa [pow_one, hx]) ?_
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx, hz2]
  have hy' : (⟨y, hyH⟩ : H) ∉ Subgroup.zpowers ⟨x, hxH⟩ := by
    rintro ⟨n, hn⟩
    dsimp only at hn
    have hc : x * y = y * x := by
      have := ((Commute.refl (⟨x, hxH⟩ : H)).zpow_right n).eq
      rw [hn] at this
      exact congrArg Subtype.val this
    apply hz
    rw [hc] at hxy
    simpa using hxy.symm
  have hy2 : (⟨y, hyH⟩ : H) ^ 2 = ⟨x, hxH⟩ ^ 2 := Subtype.ext (by simp [hx, hy])
  have hyx : (⟨y, hyH⟩ : H) * ⟨x, hxH⟩ * (⟨y, hyH⟩ : H)⁻¹ = (⟨x, hxH⟩ : H)⁻¹ := by
    refine Subtype.ext ?_
    have hxinv : x⁻¹ = z * x := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [mul_assoc, ← sq, hx, hzz]
    have hyx' : y * x = z * (x * y) := by rw [hxy, ← mul_assoc, hzz, one_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyx', hxinv]
    group
  obtain ⟨⟨e, -, -⟩, -⟩ :=
    CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2) (by norm_num) hgen hxo
      hy' hy2 hyx
  exact ⟨e⟩

end Quaternion

section SLTwo

variable {k : Type*} [Field k]

theorem fin_two_eq_one_or_neg_one_of_mul_self {M : Matrix (Fin 2) (Fin 2) k} (h2 : (2 : k) ≠ 0)
    (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  rw [Matrix.mul_fin_two, Matrix.one_fin_two] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have hs : a + d ≠ 0 := fun hs => h2 (by linear_combination -e00 - hdet + a * hs)
  have hb : b = 0 :=
    (mul_eq_zero.1 (show b * (a + d) = 0 by linear_combination e01)).resolve_right hs
  have hc : c = 0 :=
    (mul_eq_zero.1 (show c * (a + d) = 0 by linear_combination e10)).resolve_right hs
  subst hb hc
  have ha0 : a ≠ 0 := fun ha => by rw [ha] at e00; simp at e00
  have hd : d = a := sub_eq_zero.1 ((mul_eq_zero.1 (show a * (d - a) = 0 by
    linear_combination hdet - e00)).resolve_left ha0)
  subst hd
  rcases mul_eq_zero.1 (show (d - 1) * (d + 1) = 0 by linear_combination e00) with ha | ha
  · left
    rw [sub_eq_zero.1 ha, Matrix.one_fin_two]
  · right
    rw [eq_neg_of_add_eq_zero_left ha, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sl2_sq_eq_one_iff (hk : ringChar k ≠ 2) (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    A ^ 2 = 1 ↔ A = 1 ∨ A = -1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hM : (A : Matrix (Fin 2) (Fin 2) k) * A = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, h, Matrix.SpecialLinearGroup.coe_one]
    rcases fin_two_eq_one_or_neg_one_of_mul_self (Ring.two_ne_zero hk) hM A.prop with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  · rintro (rfl | rfl)
    · simp
    · rw [sq, neg_mul_neg, mul_one]

theorem sl2_neg_one_ne_one (hk : ringChar k ≠ 2) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) k) ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
    (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact hk (neg_one_eq_one_iff.1 this)

theorem sl2_orderOf_eq_two_iff (hk : ringChar k ≠ 2) (A : Matrix.SpecialLinearGroup (Fin 2) k) :
    orderOf A = 2 ↔ A = -1 := by
  constructor
  · intro h
    have hA : A ^ orderOf A = 1 := pow_orderOf_eq_one A
    rw [h] at hA
    rcases (sl2_sq_eq_one_iff hk A).1 hA with rfl | rfl
    · simp at h
    · rfl
  · rintro rfl
    exact orderOf_eq_prime ((sl2_sq_eq_one_iff hk _).2 (Or.inr rfl)) (sl2_neg_one_ne_one hk)

theorem sl2_exists_anticommuting_pair {a b : k} (hab : a ^ 2 + b ^ 2 = -1) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) k,
      (x : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] ∧
      (y : Matrix (Fin 2) (Fin 2) k) = !![a, b; b, -a] ∧
      x ^ 2 = -1 ∧ y ^ 2 = -1 ∧ x * y = -1 * (y * x) := by
  let x : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
  let y : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination -hab⟩
  have hxm : (x : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have hym : (y : Matrix (Fin 2) (Fin 2) k) = !![a, b; b, -a] := rfl
  refine ⟨x, y, hxm, hym, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hxm, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [sq]
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hym, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [sq] <;> first | linear_combination hab | ring1
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, hxm, hym]
    fin_cases i <;> fin_cases j <;> simp

theorem sl2_exists_quaternion_subgroup [Finite k] (hk : ringChar k ≠ 2) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) k, x * y ≠ y * x ∧
      ∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k), x ∈ H ∧ y ∈ H ∧
        Nonempty (QuaternionGroup 2 ≃* H) := by
  obtain ⟨a, b, hab⟩ := finite_odd_field_two_squares hk (-1)
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ := sl2_exists_anticommuting_pair hab
  have hz := sl2_neg_one_ne_one hk (k := k)
  refine ⟨x, y, fun h => hz ?_,
    exists_quaternion_subgroup_of_anticommuting hz ((sl2_sq_eq_one_iff hk _).2 (Or.inr rfl))
      hx hy hxy⟩
  rw [h] at hxy
  exact mul_eq_right.1 hxy.symm

theorem sl2_odd_field_involution_structure [Finite k] (hk : ringChar k ≠ 2) :
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) k, orderOf A = 2 ↔ A = -1) ∧
      (∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k),
        Nonempty (QuaternionGroup 2 ≃* H)) ∧
      ∀ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) k),
        ¬ IsMulCommutative (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) := by
  obtain ⟨x, y, hxy, H, hxH, hyH, ⟨e⟩⟩ := sl2_exists_quaternion_subgroup hk
  refine ⟨sl2_orderOf_eq_two_iff hk, ⟨H, ⟨e⟩⟩, fun P hP => ?_⟩
  have hH : IsPGroup 2 H := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  let f := P.equiv Q
  have hcomm : ∀ u v : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)), u * v = v * u :=
    fun u v => f.symm.injective (by rw [map_mul, map_mul, mul_comm'])
  exact hxy (congrArg Subtype.val (hcomm ⟨x, hHQ hxH⟩ ⟨y, hHQ hyH⟩))

theorem sl2_zmod_three_involution_structure :
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), orderOf A = 2 ↔ A = -1) ∧
      (∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)),
        Nonempty (QuaternionGroup 2 ≃* H)) ∧
      ∀ P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)),
        ¬ IsMulCommutative (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :=
  sl2_odd_field_involution_structure (by rw [ZMod.ringChar_zmod_n]; decide)

end SLTwo

end CFSG.LocalAnalysis.ComponentInitial
