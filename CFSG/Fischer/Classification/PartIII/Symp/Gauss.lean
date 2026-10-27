module

public import CFSG.Fischer.Classification.PartIII.Symp.Transvection

public section

namespace CFSG.Fischer.Classification.LocalSymp

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Symplectic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Gauss

@[expose] def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b
  decide

theorem chi_zero : chi 0 = 1 := rfl

theorem chi_one : chi 1 = -1 := rfl

theorem chi_eq (a : ZMod 2) : chi a = 1 - 2 * (if a = 1 then 1 else 0) := by
  revert a
  decide

theorem sum_chi_eq_zero [Fintype V] (ℓ : V →ₗ[ZMod 2] ZMod 2) {u : V} (hu : ℓ u = 1) :
    ∑ x, chi (ℓ x) = 0 := by
  have h := Fintype.sum_equiv (Equiv.addRight u) (fun x => chi (ℓ (x + u))) (fun y => chi (ℓ y))
    fun x => rfl
  simp only [map_add, hu, chi_add, chi_one, mul_neg, mul_one, Finset.sum_neg_distrib] at h
  linarith

variable (Q : QuadraticForm (ZMod 2) V)

theorem quadratic_add_add (x z : V) : Q x + Q (x + z) = Q z + QuadraticMap.polar Q x z := by
  have key : ∀ a b c : ZMod 2, a + b = c + (b - a - c) := by decide
  exact key _ _ _

theorem sq_sum_chi_quadratic [Fintype V]
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    (∑ x, chi (Q x)) ^ 2 = Fintype.card V := by
  have hx : ∀ x, ∑ y, chi (Q x) * chi (Q y) =
      ∑ z, chi (Q z) * chi (QuadraticMap.polar Q x z) := by
    intro x
    rw [← Fintype.sum_equiv (Equiv.addLeft x) (fun z => chi (Q x) * chi (Q (x + z))) _
      fun z => rfl]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← chi_add, ← chi_add, quadratic_add_add]
  rw [sq, Finset.sum_mul_sum]
  simp_rw [hx]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single 0]
  · simp [chi_zero, QuadraticMap.polar]
  · intro z _ hz
    obtain ⟨u, hu⟩ : ∃ u, QuadraticMap.polar Q u z ≠ 0 := by
      by_contra! h
      exact hz (hnd z fun y => by rw [QuadraticMap.polar_comm]; exact h y)
    have := sum_chi_eq_zero ((QuadraticMap.polarBilin Q).flip z) (u := u) (by
      rw [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply]
      exact zmod_two_eq_one_of_ne_zero hu)
    simp only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply] at this
    rw [this, mul_zero]
  · simp

theorem two_mul_ncard_quadratic [Finite V]
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {m : ℕ} (hV : Nat.card V = 4 ^ m) :
    2 * {x | Q x = 1}.ncard + 2 ^ m = 4 ^ m ∨ 2 * {x | Q x = 1}.ncard = 4 ^ m + 2 ^ m := by
  classical
  have := Fintype.ofFinite V
  have hS : ∑ x, chi (Q x) = Fintype.card V - 2 * {x | Q x = 1}.ncard := by
    simp_rw [chi_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    simp
  have h2 := sq_sum_chi_quadratic Q hnd
  rw [← Nat.card_eq_fintype_card, hV] at h2 hS
  have h4 : ((4 ^ m : ℕ) : ℤ) = ((2 : ℤ) ^ m) ^ 2 := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4] at h2
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] at hS <;> push_cast at hS
  · left
    have : ((2 * {x | Q x = 1}.ncard + 2 ^ m : ℕ) : ℤ) = ((4 ^ m : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  · right
    have : ((2 * {x | Q x = 1}.ncard : ℕ) : ℤ) = ((4 ^ m + 2 ^ m : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this

end Gauss

section Perp

omit [Module (ZMod 2) V] in
theorem ncard_eq_of_add_image {S T : Set V} (t : V) (h : (fun x => x + t) '' S = T) :
    S.ncard = T.ncard := by
  rw [← h, Set.ncard_image_of_injective _ (add_left_injective t)]

variable (Q : QuadraticForm (ZMod 2) V)

theorem two_mul_ncard_perp [Finite V] {u v : V} (huv : QuadraticMap.polar Q u v = 1) :
    2 * {x | QuadraticMap.polar Q x v = 0}.ncard = Nat.card V := by
  have himg : (fun x => x + u) '' {x | QuadraticMap.polar Q x v = 0} =
      {x | QuadraticMap.polar Q x v = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [QuadraticMap.polar_add_left, hx, huv, zero_add]
    · intro hy
      refine ⟨y + u, ?_, show y + u + u = y by rw [add_assoc, zmod_two_add_self, add_zero]⟩
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rw [QuadraticMap.polar_add_left, hy, huv]
      rfl
  have hunion : {x | QuadraticMap.polar Q x v = 0} ∪ {x | QuadraticMap.polar Q x v = 1} =
      Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact zmod_two_cases _
  have hdisj : Disjoint {x | QuadraticMap.polar Q x v = 0} {x | QuadraticMap.polar Q x v = 1} :=
    Set.disjoint_left.2 fun x h0 h1 => by
      rw [Set.mem_ofPred_eq] at h0 h1
      rw [h0] at h1
      exact zero_ne_one h1
  have := Set.ncard_union_eq hdisj
  rw [hunion, Set.ncard_univ, ← ncard_eq_of_add_image u himg] at this
  omega

theorem four_mul_ncard_quadratic_perp [Finite V]
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) {v : V} (hv : Q v = 1) :
    4 * {w | Q w = 1 ∧ QuadraticMap.polar Q w v = 0}.ncard = Nat.card V := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨u, hu⟩ : ∃ u, QuadraticMap.polar Q u v ≠ 0 := by
    by_contra! h
    exact hv0 (hnd v fun y => by rw [QuadraticMap.polar_comm]; exact h y)
  have hK := two_mul_ncard_perp Q (zmod_two_eq_one_of_ne_zero hu)
  have hvv : QuadraticMap.polar Q v v = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, zmod2_add_self]
  have himg : (fun x => x + v) '' {w | Q w = 0 ∧ QuadraticMap.polar Q w v = 0} =
      {w | Q w = 1 ∧ QuadraticMap.polar Q w v = 0} := by
    have hQ : ∀ w, QuadraticMap.polar Q w v = 0 → Q (w + v) = Q w + 1 := fun w hw => by
      have := quadratic_add_add Q w v
      rw [hv, hw, add_zero] at this
      rw [← this, ← add_assoc, zmod2_add_self, zero_add]
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hxv⟩, rfl⟩
      refine ⟨by rw [hQ x hxv, hx0, zero_add], ?_⟩
      rw [QuadraticMap.polar_add_left, hxv, hvv, add_zero]
    · rintro ⟨hy1, hyv⟩
      have hyv' : QuadraticMap.polar Q (y + v) v = 0 := by
        rw [QuadraticMap.polar_add_left, hyv, hvv, add_zero]
      refine ⟨y + v, ⟨?_, hyv'⟩, show y + v + v = y by rw [add_assoc, zmod_two_add_self, add_zero]⟩
      rw [hQ y hyv, hy1]
      rfl
  have hunion : {w | Q w = 0 ∧ QuadraticMap.polar Q w v = 0} ∪
      {w | Q w = 1 ∧ QuadraticMap.polar Q w v = 0} = {x | QuadraticMap.polar Q x v = 0} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases zmod_two_cases (Q x) with h | h <;> simp [h]
  have hdisj : Disjoint {w | Q w = 0 ∧ QuadraticMap.polar Q w v = 0}
      {w | Q w = 1 ∧ QuadraticMap.polar Q w v = 0} :=
    Set.disjoint_left.2 fun x h0 h1 => by
      rw [Set.mem_ofPred_eq] at h0 h1
      rw [h0.1] at h1
      exact zero_ne_one h1.1
  have := Set.ncard_union_eq hdisj
  rw [hunion, ncard_eq_of_add_image v himg] at this
  omega

end Perp

end CFSG.Fischer.Classification.LocalSymp
