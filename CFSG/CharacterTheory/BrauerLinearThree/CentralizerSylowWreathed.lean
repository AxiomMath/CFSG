module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerStructure
public import CFSG.CharacterTheory.Wreathed.BrauerWongSupport

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.Wreathed CFSG.Wreathed.BrauerWong

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

section Relations

variable {k : ℕ} {α : Fˣ}

theorem wreath_diagGL_left_pow (hα : orderOf α = 2 ^ k) :
    (diagGL α 1 : GL (Fin 2) F) ^ 2 ^ k = 1 := by
  rw [diagGL_pow, ← hα, pow_orderOf_eq_one, one_pow, diagGL_one_one]

theorem wreath_diagGL_right_pow (hα : orderOf α = 2 ^ k) :
    (diagGL 1 α : GL (Fin 2) F) ^ 2 ^ k = 1 := by
  rw [diagGL_pow, ← hα, pow_orderOf_eq_one, one_pow, diagGL_one_one]

theorem wreath_diagGL_comm (α : Fˣ) :
    (diagGL α 1 : GL (Fin 2) F) * diagGL 1 α = diagGL 1 α * diagGL α 1 := by
  rw [diagGL_mul, diagGL_mul, mul_comm α 1, mul_comm 1 α]

theorem wreath_swapGL_conj (α : Fˣ) :
    (swapGL : GL (Fin 2) F)⁻¹ * diagGL α 1 * swapGL = diagGL 1 α := by
  rw [inv_eq_of_mul_eq_one_right swapGL_mul_self, swapGL_mul_diagGL, mul_assoc, swapGL_mul_self,
    mul_one]

theorem wreath_swapGL_sq : (swapGL : GL (Fin 2) F) ^ 2 = 1 := by
  rw [sq, swapGL_mul_self]

theorem wreath_left_pow (hα : orderOf α = 2 ^ k) :
    linearCentralizerHom φ (diagGL α 1) ^ 2 ^ k = 1 := by
  rw [← map_pow, wreath_diagGL_left_pow hα, map_one]

theorem wreath_right_pow (hα : orderOf α = 2 ^ k) :
    linearCentralizerHom φ (diagGL 1 α) ^ 2 ^ k = 1 := by
  rw [← map_pow, wreath_diagGL_right_pow hα, map_one]

theorem wreath_swapW_sq : swapW φ ^ 2 = 1 := by
  rw [sq]
  exact swapW_mul_self φ

theorem wreath_comm (α : Fˣ) :
    linearCentralizerHom φ (diagGL α 1) * linearCentralizerHom φ (diagGL 1 α) =
      linearCentralizerHom φ (diagGL 1 α) * linearCentralizerHom φ (diagGL α 1) := by
  rw [← map_mul, ← map_mul, wreath_diagGL_comm]

theorem wreath_swapW_conj (α : Fˣ) :
    (swapW φ)⁻¹ * linearCentralizerHom φ (diagGL α 1) * swapW φ =
      linearCentralizerHom φ (diagGL 1 α) := by
  rw [swapW, ← map_inv, ← map_mul, ← map_mul, wreath_swapGL_conj]

end Relations

section Coordinates

variable {k : ℕ} {α : Fˣ} (hα : orderOf α = 2 ^ k)
include hα

theorem presentationHom_diagGL_injective :
    Function.Injective (presentationHom (wreath_diagGL_left_pow hα) (wreath_diagGL_right_pow hα)
      wreath_swapGL_sq (wreath_diagGL_comm α) (wreath_swapGL_conj α)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ k)).symm.surjective x
  change presentationHom _ _ _ _ _ (element _ a b e) = 1 at hx
  change element _ a b e = 1
  rw [presentationHom_element, diagGL_pow, diagGL_pow, one_pow, one_pow, diagGL_mul, mul_one,
    one_mul] at hx
  have hval : ∀ c : ZMod (2 ^ k), α ^ c.val = 1 → c = 0 := by
    intro c hc
    have : NeZero (2 ^ k) := ⟨by positivity⟩
    have h1 := orderOf_dvd_of_pow_eq_one hc
    rw [hα] at h1
    exact (ZMod.val_eq_zero c).mp (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt c))
  rcases swap_exponent_cases e with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, mul_one] at hx
    have h0 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hx
    have h1 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 1) hx
    simp only [diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_one] at h0 h1
    simp at h0 h1
    rw [hval a (Units.ext h0), hval b (Units.ext h1), element_zero]
  · exfalso
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one] at hx
    have h0 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hx
    simp [diagGL, swapGL, Matrix.mul_apply, Fin.sum_univ_two] at h0

theorem presentationHom_linearCentralizerHom :
    presentationHom (wreath_left_pow φ hα) (wreath_right_pow φ hα) (wreath_swapW_sq φ)
        (wreath_comm φ α) (wreath_swapW_conj φ α) =
      (linearCentralizerHom φ).comp (presentationHom (wreath_diagGL_left_pow hα)
        (wreath_diagGL_right_pow hα) wreath_swapGL_sq (wreath_diagGL_comm α)
        (wreath_swapGL_conj α)) := by
  ext x
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (2 ^ k)).symm.surjective x
  change presentationHom _ _ _ _ _ (element _ a b e) =
    linearCentralizerHom φ (presentationHom _ _ _ _ _ (element _ a b e))
  rw [presentationHom_element, presentationHom_element, map_mul, map_mul, map_pow, map_pow,
    map_pow]

variable (hZodd : Odd (Nat.card Z))
include hZodd

theorem presentationHom_linearCentralizerHom_injective :
    Function.Injective (presentationHom (wreath_left_pow φ hα) (wreath_right_pow φ hα)
      (wreath_swapW_sq φ) (wreath_comm φ α) (wreath_swapW_conj φ α)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [presentationHom_linearCentralizerHom φ hα, MonoidHom.comp_apply,
    linearCentralizerHom_eq_one_iff] at hx
  apply presentationHom_diagGL_injective hα
  rw [map_one]
  apply eq_one_of_mem_odd_of_pow_two_pow hZodd hx (j := k + 1)
  rw [← map_pow, pow_succ, mul_comm, element_pow_twice_modulus, map_one]

theorem card_closure_wreath (hk : 1 ≤ k) :
    Nat.card (Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
      linearCentralizerHom φ (diagGL 1 α), swapW φ}) = 2 ^ (2 * k + 1) := by
  rw [← presentationHom_range (wreath_left_pow φ hα) (wreath_right_pow φ hα) (wreath_swapW_sq φ)
      (wreath_comm φ α) (wreath_swapW_conj φ α) hk,
    ← Nat.card_congr (MonoidHom.ofInjective
      (presentationHom_linearCentralizerHom_injective φ hα hZodd)).toEquiv, card_wreath]
  ring

theorem wreathGenerators_diagGL (hk : 1 ≤ k) :
    WreathGenerators k (Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
        linearCentralizerHom φ (diagGL 1 α), swapW φ})
      (linearCentralizerHom φ (diagGL α 1)) (linearCentralizerHom φ (diagGL 1 α)) (swapW φ) where
  closure_eq := rfl
  card_eq := card_closure_wreath φ hα hZodd hk
  pow_left := wreath_left_pow φ hα
  pow_right := wreath_right_pow φ hα
  sq_swap := wreath_swapW_sq φ
  comm := wreath_comm φ α
  conj := wreath_swapW_conj φ α

end Coordinates

theorem closure_wreath_le_centralizer (α : Fˣ) :
    Subgroup.closure {linearCentralizerHom φ (diagGL α 1), linearCentralizerHom φ (diagGL 1 α),
      swapW φ} ≤ Subgroup.centralizer ({J} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl) <;> exact linearCentralizerHom_mem φ _

section Powers

variable {k : ℕ} {α : Fˣ} (hα : orderOf α = 2 ^ k)
include hα

theorem wreath_pow_two_pow_pred_eq_neg_one (hk : 1 ≤ k) : α ^ 2 ^ (k - 1) = -1 := by
  apply units_eq_neg_one_of_orderOf_eq_two
  have h : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [orderOf_pow_of_dvd (by positivity) ⟨2, by rw [hα, h]⟩, hα, h,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem wreath_left_pow_pred (hk : 1 ≤ k) :
    linearCentralizerHom φ (diagGL α 1) ^ 2 ^ (k - 1) = invJ₂ φ := by
  rw [← map_pow, diagGL_pow, wreath_pow_two_pow_pred_eq_neg_one hα hk, one_pow]

theorem wreath_right_pow_pred (hk : 1 ≤ k) :
    linearCentralizerHom φ (diagGL 1 α) ^ 2 ^ (k - 1) = invJ₁ φ := by
  rw [← map_pow, diagGL_pow, wreath_pow_two_pow_pred_eq_neg_one hα hk, one_pow]

theorem wreath_inv_mul_inv_pow_pred (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
    (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2) (hk : 1 ≤ k) :
    ((linearCentralizerHom φ (diagGL α 1))⁻¹ * (linearCentralizerHom φ (diagGL 1 α))⁻¹) ^
      2 ^ (k - 1) = J := by
  have hinv : ∀ a b : Fˣ, (diagGL a b : GL (Fin 2) F)⁻¹ = diagGL a⁻¹ b⁻¹ := fun a b =>
    inv_eq_of_mul_eq_one_right (by rw [diagGL_mul, mul_inv_cancel, mul_inv_cancel, diagGL_one_one])
  rw [← map_inv, ← map_inv, ← map_mul, ← map_pow, hinv, hinv, diagGL_mul, diagGL_pow, inv_one,
    mul_one, one_mul, inv_pow, wreath_pow_two_pow_pred_eq_neg_one hα hk, inv_neg_one,
    ← neg_one_eq_diagGL, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ]

end Powers

variable [Finite F]

theorem exists_orderOf_eq_two_pow_factorization :
    ∃ α : Fˣ, orderOf α = 2 ^ (Nat.card F - 1).factorization 2 := by
  have : Fintype F := Fintype.ofFinite F
  apply exists_orderOf_eq_of_dvd_natCard
  rw [Nat.card_units]
  exact Nat.ordProj_dvd _ _

theorem exists_sylow_map_eq_closure_wreath (hZodd : Odd (Nat.card Z))
    (hq : Nat.card F % 4 = 1) {k : ℕ} (hk : (Nat.card F - 1).factorization 2 = k) {α : Fˣ}
    (hα : orderOf α = 2 ^ k) :
    ∃ S : Sylow 2 (Subgroup.centralizer ({J} : Set G)),
      (S : Subgroup (Subgroup.centralizer ({J} : Set G))).map
          (Subgroup.centralizer ({J} : Set G)).subtype =
        Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
          linearCentralizerHom φ (diagGL 1 α), swapW φ} := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨hk2, -, w, hw, hcard⟩ := wreathed_arith hq hq1
  rw [hk] at hk2 hcard
  apply exists_sylow_map_subtype_eq (closure_wreath_le_centralizer φ α)
    (card_closure_wreath φ hα hZodd (by omega)) hw (z := Nat.card Z)
  rw [card_centralizer_J φ, hcard]

theorem exists_wreathed_sylow (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
    (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
    (hq : Nat.card F % 4 = 1) {k : ℕ} (hk : (Nat.card F - 1).factorization 2 = k) :
    2 ≤ k ∧ ∃ α : Fˣ, orderOf α = 2 ^ k ∧
      WreathGenerators k (Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
          linearCentralizerHom φ (diagGL 1 α), swapW φ})
        (linearCentralizerHom φ (diagGL α 1)) (linearCentralizerHom φ (diagGL 1 α)) (swapW φ) ∧
      Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
          linearCentralizerHom φ (diagGL 1 α), swapW φ} ≤ Subgroup.centralizer ({J} : Set G) ∧
      (∃ S : Sylow 2 (Subgroup.centralizer ({J} : Set G)),
        (S : Subgroup (Subgroup.centralizer ({J} : Set G))).map
            (Subgroup.centralizer ({J} : Set G)).subtype =
          Subgroup.closure {linearCentralizerHom φ (diagGL α 1),
            linearCentralizerHom φ (diagGL 1 α), swapW φ}) ∧
      ((linearCentralizerHom φ (diagGL α 1))⁻¹ * (linearCentralizerHom φ (diagGL 1 α))⁻¹) ^
          2 ^ (k - 1) = J ∧
      linearCentralizerHom φ (diagGL α 1) ^ 2 ^ (k - 1) = invJ₂ φ ∧
      linearCentralizerHom φ (diagGL 1 α) ^ 2 ^ (k - 1) = invJ₁ φ := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hk2 : 2 ≤ k := hk ▸ (wreathed_arith hq hq1).1
  obtain ⟨α, hα⟩ := exists_orderOf_eq_two_pow_factorization (F := F)
  rw [hk] at hα
  exact ⟨hk2, α, hα, wreathGenerators_diagGL φ hα hZodd (by omega),
    closure_wreath_le_centralizer φ α, exists_sylow_map_eq_closure_wreath φ hZodd hq hk hα,
    wreath_inv_mul_inv_pow_pred φ hα hZ hZodd h2 hJ (by omega),
    wreath_left_pow_pred φ hα (by omega), wreath_right_pow_pred φ hα (by omega)⟩

end CFSG.BrauerLinearThree
