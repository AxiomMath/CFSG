module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.Asc77

open scoped MatrixGroups commutatorElement

namespace T7Z

section SL2

variable {F : Type*} [Field F]



theorem sl2_comm_entries (A X : SL(2, F)) (h : X * A = A * X) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (X : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (X : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
    ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - (A : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
        ((X : Matrix (Fin 2) (Fin 2) F) 0 0 - (X : Matrix (Fin 2) (Fin 2) F) 1 1) ∧
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((X : Matrix (Fin 2) (Fin 2) F) 0 0 - (X : Matrix (Fin 2) (Fin 2) F) 1 1) =
      ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - (A : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (X : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  have hm : (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-1 : F) * h00
  · linear_combination (-1 : F) * h01
  · linear_combination (-1 : F) * h10



theorem sl2_sq_neg_one_entries (A : SL(2, F)) (hA : A * A = -1) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (A : Matrix (Fin 2) (Fin 2) F) 1 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = -1 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have hm : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (-1 : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) hA
    simpa using this
  have h00 := congrFun (congrFun hm 0) 0
  have h11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  refine ⟨?_, ?_, hdet⟩
  · simpa using h00
  · simpa using h11



theorem sl2_commute_of_sq (h2 : (2 : F) ≠ 0) {A X Y : SL(2, F)} (hA : A * A = -1)
    (hX : X * A = A * X) (hY : Y * A = A * Y) : X * Y = Y * X := by
  obtain ⟨hA1, hA2, hA3⟩ := sl2_sq_neg_one_entries A hA
  obtain ⟨hX1, hX2, hX3⟩ := sl2_comm_entries A X hX
  obtain ⟨hY1, hY2, hY3⟩ := sl2_comm_entries A Y hY
  generalize (A : Matrix (Fin 2) (Fin 2) F) 0 0 = p at *
  generalize (A : Matrix (Fin 2) (Fin 2) F) 0 1 = q at *
  generalize (A : Matrix (Fin 2) (Fin 2) F) 1 0 = r at *
  generalize (A : Matrix (Fin 2) (Fin 2) F) 1 1 = s at *
  have key : (X : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 =
        (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (X : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      ((X : Matrix (Fin 2) (Fin 2) F) 0 0 - (X : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (Y : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((Y : Matrix (Fin 2) (Fin 2) F) 0 0 - (Y : Matrix (Fin 2) (Fin 2) F) 1 1) *
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((Y : Matrix (Fin 2) (Fin 2) F) 0 0 - (Y : Matrix (Fin 2) (Fin 2) F) 1 1) =
      (Y : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((X : Matrix (Fin 2) (Fin 2) F) 0 0 - (X : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    generalize (X : Matrix (Fin 2) (Fin 2) F) 0 1 = x2 at *
    generalize (X : Matrix (Fin 2) (Fin 2) F) 1 0 = x3 at *
    generalize (X : Matrix (Fin 2) (Fin 2) F) 0 0 - (X : Matrix (Fin 2) (Fin 2) F) 1 1 = dx at *
    generalize (Y : Matrix (Fin 2) (Fin 2) F) 0 1 = y2 at *
    generalize (Y : Matrix (Fin 2) (Fin 2) F) 1 0 = y3 at *
    generalize (Y : Matrix (Fin 2) (Fin 2) F) 0 0 - (Y : Matrix (Fin 2) (Fin 2) F) 1 1 = dy at *
    by_cases hq : q = 0
    · by_cases hr : r = 0
      · have hps : p - s ≠ 0 := by
          intro hps
          have hs : s = p := by linear_combination -hps
          subst hs hq hr
          apply h2
          linear_combination hA1 - hA3
        subst hq hr
        have hx2 : x2 = 0 := by
          have : (p - s) * x2 = 0 := by linear_combination hX2
          exact (mul_eq_zero.mp this).resolve_left hps
        have hy2 : y2 = 0 := by
          have : (p - s) * y2 = 0 := by linear_combination hY2
          exact (mul_eq_zero.mp this).resolve_left hps
        have hx3 : x3 = 0 := by
          have : (p - s) * x3 = 0 := by linear_combination -hX3
          exact (mul_eq_zero.mp this).resolve_left hps
        have hy3 : y3 = 0 := by
          have : (p - s) * y3 = 0 := by linear_combination -hY3
          exact (mul_eq_zero.mp this).resolve_left hps
        subst hx2 hy2 hx3 hy3
        simp
      · subst hq
        have hx2 : x2 = 0 := by
          have : r * x2 = 0 := by linear_combination -hX1
          exact (mul_eq_zero.mp this).resolve_left hr
        have hy2 : y2 = 0 := by
          have : r * y2 = 0 := by linear_combination -hY1
          exact (mul_eq_zero.mp this).resolve_left hr
        subst hx2 hy2
        refine ⟨by simp, by simp, ?_⟩
        apply mul_left_cancel₀ hr
        linear_combination x3 * hY3 - y3 * hX3
    · have g1 : x2 * y3 = y2 * x3 := by
        apply mul_left_cancel₀ hq
        linear_combination x2 * hY1 - y2 * hX1
      have g2 : dx * y2 = dy * x2 := by
        apply mul_left_cancel₀ hq
        linear_combination y2 * (-hX2) + x2 * hY2
      refine ⟨g1, g2, ?_⟩
      apply mul_left_cancel₀ hq
      linear_combination dy * hX1 - dx * hY1 - r * g2
  obtain ⟨g1, g2, g3⟩ := key
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination g1
  · linear_combination g2
  · linear_combination g3
  · linear_combination -g1

end SL2

section Group

variable {K : Type*} [Group K] {F : Type*} [Field F] [Finite F]

theorem commute_of_centralizes_sq (hodd : Odd (Nat.card F)) (e : K ≃* SL(2, F)) {a z : K}
    (hz : orderOf z = 2) (haa : a * a = z) {x y : K} (hx : x * a = a * x) (hy : y * a = a * y) :
    x * y = y * x := by
  have hz' : e z = -1 := by
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e z).mp hz
    rw [this, MulEquiv.apply_symm_apply]
  have hA : e a * e a = -1 := by rw [← map_mul, haa, hz']
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have := sl2_commute_of_sq (X := e x) (Y := e y) h2 hA (by rw [← map_mul, ← map_mul, hx])
    (by rw [← map_mul, ← map_mul, hy])
  apply e.injective
  rw [map_mul, map_mul]
  exact this

theorem eq_one_or_eq_of_mem_center (hodd : Odd (Nat.card F)) (e : K ≃* SL(2, F)) {z : K}
    (hz : orderOf z = 2) {c : K} (hc : c ∈ Subgroup.center K) : c = 1 ∨ c = z := by
  have hz' : z = e.symm (-1) := (orderOf_eq_two_iff_of_equiv_sl2 hodd e z).mp hz
  have h := (mem_center_iff_of_equiv_sl2 e c).mp hc
  rcases (mem_center_sl2_iff _).mp h with h | h
  · left
    exact e.injective (by rw [h, map_one])
  · right
    rw [hz']
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])

end Group


theorem fix_of_perfect_two {G Y : Type*} [Group G] (act : G → Y → Y)
    (hmul : ∀ x y s, act (x * y) s = act x (act y s)) (hone : ∀ s, act 1 s = s)
    {L : Subgroup G} (hL : L ≤ ⁅L, L⁆) {s₀ s₁ : Y}
    (hmap : ∀ w ∈ L, (act w s₀ = s₀ ∧ act w s₁ = s₁) ∨ (act w s₀ = s₁ ∧ act w s₁ = s₀)) :
    ∀ w ∈ L, act w s₀ = s₀ ∧ act w s₁ = s₁ := by
  have hinv : ∀ w s, act w⁻¹ (act w s) = s := by
    intro w s
    rw [← hmul, inv_mul_cancel, hone]
  have hiT : ∀ w, act w s₀ = s₀ → act w s₁ = s₁ → act w⁻¹ s₀ = s₀ ∧ act w⁻¹ s₁ = s₁ := by
    intro w h0 h1
    exact ⟨by calc act w⁻¹ s₀ = act w⁻¹ (act w s₀) := by rw [h0]
                _ = s₀ := hinv w s₀,
           by calc act w⁻¹ s₁ = act w⁻¹ (act w s₁) := by rw [h1]
                _ = s₁ := hinv w s₁⟩
  have hiS : ∀ w, act w s₀ = s₁ → act w s₁ = s₀ → act w⁻¹ s₀ = s₁ ∧ act w⁻¹ s₁ = s₀ := by
    intro w h0 h1
    exact ⟨by calc act w⁻¹ s₀ = act w⁻¹ (act w s₁) := by rw [h1]
                _ = s₁ := hinv w s₁,
           by calc act w⁻¹ s₁ = act w⁻¹ (act w s₀) := by rw [h0]
                _ = s₀ := hinv w s₀⟩
  let N : Subgroup G :=
    { carrier := {w | act w s₀ = s₀ ∧ act w s₁ = s₁}
      mul_mem' := by
        rintro x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
        refine ⟨?_, ?_⟩
        · rw [hmul, hy0, hx0]
        · rw [hmul, hy1, hx1]
      one_mem' := ⟨hone _, hone _⟩
      inv_mem' := fun {x} hx => hiT x hx.1 hx.2 }
  have hcomm : ⁅L, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have e1 : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]
    show act ⁅x, y⁆ s₀ = s₀ ∧ act ⁅x, y⁆ s₁ = s₁
    rw [e1]
    simp only [hmul]
    rcases hmap x hx with ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩ <;>
    rcases hmap y hy with ⟨hy0, hy1⟩ | ⟨hy0, hy1⟩
    · obtain ⟨hx0', hx1'⟩ := hiT x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiT y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiT x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiS y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiS x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiT y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
    · obtain ⟨hx0', hx1'⟩ := hiS x hx0 hx1
      obtain ⟨hy0', hy1'⟩ := hiS y hy0 hy1
      simp [hx0, hx1, hy0, hy1, hx0', hx1', hy0', hy1']
  intro w hw
  exact hcomm (hL hw)


end T7Z

end CFSG.ClassicalInvolution.Asc77
