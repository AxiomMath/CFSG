module

public import CFSG.LieType.Steinberg.TypeExceptional
public import CFSG.LieType.Chevalley.WeylSpace
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def iform (x y : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * τ.symmetrizedCartan i j * y j

theorem symmetrizedCartan_symm (τ : Tag) (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.symmetrizedCartan j i := by
  have h := (posDef_symmetrizedCartan τ).isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  exact_mod_cast h.symm

theorem iform_comm (x y : Fin τ.rank → ℤ) : iform x y = iform y x := by
  simp only [iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm τ j i]
  ring

theorem iform_add_left (x x' y : Fin τ.rank → ℤ) : iform (x + x') y = iform x y + iform x' y := by
  simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem iform_add_right (x y y' : Fin τ.rank → ℤ) : iform x (y + y') = iform x y + iform x y' := by
  rw [iform_comm, iform_add_left, iform_comm y, iform_comm y']

theorem iform_smul_left (c : ℤ) (x y : Fin τ.rank → ℤ) : iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem iform_smul_right (c : ℤ) (x y : Fin τ.rank → ℤ) : iform x (c • y) = c * iform x y := by
  rw [iform_comm, iform_smul_left, iform_comm]

theorem iform_sub_left (x x' y : Fin τ.rank → ℤ) : iform (x - x') y = iform x y - iform x' y := by
  rw [sub_eq_add_neg, iform_add_left, ← neg_one_smul ℤ x', iform_smul_left]
  ring

theorem iform_sub_right (x y y' : Fin τ.rank → ℤ) : iform x (y - y') = iform x y - iform x y' := by
  rw [iform_comm, iform_sub_left, iform_comm y, iform_comm y']

theorem iform_single_left (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    iform (Pi.single i 1) y = τ.symmetrizer i i * ∑ j, τ.cartan i j * y j := by
  simp only [iform, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp [symmetrizedCartan_apply, Finset.mul_sum, mul_assoc]

theorem iform_single_right (x : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    iform x (Pi.single i 1) = τ.symmetrizer i i * ∑ j, τ.cartan i j * x j := by
  rw [iform_comm, iform_single_left]

theorem iform_single_single (i : Fin τ.rank) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i 1) = 2 * τ.symmetrizer i i := by
  rw [iform_single_left, sum_cartan_mul_single]
  ring

theorem iform_reflect (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    iform (reflect τ i x) (reflect τ i y) = iform x y := by
  have hx : reflect τ i x = x - (∑ j, τ.cartan i j * x j) • Pi.single i 1 := rfl
  have hy : reflect τ i y = y - (∑ j, τ.cartan i j * y j) • Pi.single i 1 := rfl
  rw [hx, hy, iform_sub_left, iform_sub_right, iform_sub_right, iform_smul_left,
    iform_smul_left, iform_smul_right, iform_smul_right, iform_single_single, iform_single_left,
    iform_single_right]
  ring

open Matrix in
theorem iform_self_pos {x : Fin τ.rank → ℤ} (hx : x ≠ 0) : 0 < iform x x := by
  have hx' : (fun j => (x j : ℝ)) ≠ 0 := fun h =>
    hx (funext fun j => by simpa using congrFun h j)
  have h := (posDef_symmetrizedCartan τ).dotProduct_mulVec_pos hx'
  have heq : star (fun j => (x j : ℝ)) ⬝ᵥ
      ((τ.symmetrizedCartan.map (Int.cast : ℤ → ℝ)) *ᵥ fun j => (x j : ℝ)) = (iform x x : ℝ) := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply, iform, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [heq] at h
  exact_mod_cast h

theorem iform_self_of_isRoot {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ j, iform γ γ = 2 * τ.symmetrizer j j := by
  induction hγ with
  | basis j => exact ⟨j, iform_single_single j⟩
  | reflect i _ ih =>
    rw [iform_reflect]
    exact ih

theorem iform_dvd_of_isRoot {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∀ x : Fin τ.rank → ℤ, iform α α ∣ 2 * iform α x := by
  induction hα with
  | basis j =>
    intro x
    rw [iform_single_single, iform_single_left]
    exact ⟨∑ k, τ.cartan j k * x k, by ring⟩
  | @reflect i v _ ih =>
    intro x
    rw [iform_reflect]
    have h := ih (reflect τ i x)
    rwa [← iform_reflect i v (reflect τ i x), reflect_reflect] at h

theorem linIndepPair_of_ne {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) : LinIndepPair α β := by
  by_contra h
  rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hα hβ h with h' | h'
  exacts [hne h', hne' h']

theorem iform_sq_lt {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β)
    (hne' : α ≠ -β) : iform α β ^ 2 < iform α α * iform β β := by
  have hb : 0 < iform β β := iform_self_pos hβ.ne_zero
  have hv : iform β β • α - iform α β • β ≠ 0 := by
    intro h0
    have := (linIndepPair_of_ne hα hβ hne hne') (iform β β) (-iform α β) (by
      rw [neg_smul, ← sub_eq_add_neg, h0])
    exact hb.ne' this.1
  have h := iform_self_pos hv
  simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right] at h
  rw [iform_comm β α] at h
  nlinarith

theorem pair_analysis {a b s t : ℤ} {i j : ℕ} (ha : a = 2 ∨ a = 4) (hb : b = 2 ∨ b = 4)
    (ht : t = 2 ∨ t = 4) (hab : s ^ 2 < a * b) (hsa : a ∣ 2 * s) (hsb : b ∣ 2 * s) (hi : 1 ≤ i)
    (hj : 1 ≤ j) (htij : t = (i : ℤ) ^ 2 * a + 2 * i * j * s + (j : ℤ) ^ 2 * b) :
    (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2 ∧ a = 4 ∧ b = 2 ∧ s = -2) ∨
      (i = 2 ∧ j = 1 ∧ a = 2 ∧ b = 4 ∧ s = -2) := by
  have hab' : 1 ≤ a * b - s ^ 2 := by omega
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  have hbt : b * t = ((j : ℤ) * b + i * s) ^ 2 + (i : ℤ) ^ 2 * (a * b - s ^ 2) := by
    rw [htij]
    ring
  have hat : a * t = ((i : ℤ) * a + j * s) ^ 2 + (j : ℤ) ^ 2 * (a * b - s ^ 2) := by
    rw [htij]
    ring
  have hi4 : (i : ℤ) ^ 2 ≤ 16 := by
    have : (i : ℤ) ^ 2 ≤ b * t := by nlinarith [sq_nonneg ((j : ℤ) * b + i * s)]
    rcases hb with rfl | rfl <;> rcases ht with rfl | rfl <;> linarith
  have hj4 : (j : ℤ) ^ 2 ≤ 16 := by
    have : (j : ℤ) ^ 2 ≤ a * t := by nlinarith [sq_nonneg ((i : ℤ) * a + j * s)]
    rcases ha with rfl | rfl <;> rcases ht with rfl | rfl <;> linarith
  have hi' : i ≤ 4 := by
    by_contra h
    have : (5 : ℤ) ≤ i := by exact_mod_cast (show 5 ≤ i by omega)
    nlinarith
  have hj' : j ≤ 4 := by
    by_contra h
    have : (5 : ℤ) ≤ j := by exact_mod_cast (show 5 ≤ j by omega)
    nlinarith
  have h16 : s ^ 2 < 16 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> linarith
  have hs : s ≤ 3 ∧ -3 ≤ s := by
    constructor <;> nlinarith
  have hl1 : 2 * s < a + b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * s)]
  have hl2 : -(a + b) < 2 * s := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + 2 * s)]
  clear hbt hat hab hab' hi4 hj4 h16
  interval_cases i <;> interval_cases j <;> rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rcases ht with rfl | rfl <;> push_cast at htij <;> omega

@[expose] def NoG2 (τ : Tag) : Prop := ∀ i, τ.symmetrizer i i = 1 ∨ τ.symmetrizer i i = 2

theorem noG2_F4 : NoG2 .F4 := by
  intro i
  fin_cases i <;> decide

theorem noG2_E8 : NoG2 .E8 := fun i => Or.inl (by simp [Tag.symmetrizer])

theorem iform_nsmul_add_nsmul (i j : ℕ) (α β : Fin τ.rank → ℤ) :
    iform (i • α + j • β) (i • α + j • β) =
      (i : ℤ) ^ 2 * iform α α + 2 * i * j * iform α β + (j : ℤ) ^ 2 * iform β β := by
  rw [← Nat.cast_smul_eq_nsmul ℤ i α, ← Nat.cast_smul_eq_nsmul ℤ j β]
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
  rw [iform_comm β α]
  ring

theorem iform_self_cases (hτ : NoG2 τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    iform γ γ = 2 ∨ iform γ γ = 4 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rcases hτ j with h | h <;> rw [hj, h] <;> norm_num

theorem exponent_pair_cases (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : IsRoot τ (i • α + j • β)) :
    (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2 ∧ iform α α = 4 ∧ iform β β = 2 ∧ iform α β = -2) ∨
      (i = 2 ∧ j = 1 ∧ iform α α = 2 ∧ iform β β = 4 ∧ iform α β = -2) := by
  have ht := iform_self_cases hτ h
  rw [iform_nsmul_add_nsmul] at ht
  exact pair_analysis (iform_self_cases hτ hα) (iform_self_cases hτ hβ) ht
    (iform_sq_lt hα hβ hne hne') (iform_dvd_of_isRoot hα β)
    (by rw [iform_comm α β]; exact iform_dvd_of_isRoot hβ α) hi hj rfl

theorem not_isRoot_nsmul_add_nsmul (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : ¬((i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1))) :
    ¬IsRoot τ (i • α + j • β) := fun h => by
  rcases exponent_pair_cases hτ hα hβ hne hne' hi hj h with h | h | h
  · exact hij (Or.inl h)
  · exact hij (Or.inr (Or.inl ⟨h.1, h.2.1⟩))
  · exact hij (Or.inr (Or.inr ⟨h.1, h.2.1⟩))

theorem not_isRoot_add_two_and_two_add (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ¬(IsRoot τ (α + 2 • β) ∧ IsRoot τ (2 • α + β)) := by
  rintro ⟨h1, h2⟩
  have h1' : IsRoot τ (1 • α + 2 • β) := by rwa [one_smul]
  have h2' : IsRoot τ (2 • α + 1 • β) := by rwa [one_smul]
  rcases exponent_pair_cases hτ hα hβ hne hne' le_rfl (by norm_num) h1' with h | h | h
  · omega
  · rcases exponent_pair_cases hτ hα hβ hne hne' (by norm_num) le_rfl h2' with h' | h' | h'
    · omega
    · omega
    · omega
  · omega

theorem isRoot_add_of_isRoot_add_two_smul {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α → α ≠ β → α ≠ -β → IsRoot τ (α + 2 • β) →
      IsRoot τ (α + β) := by
  induction hβ with
  | basis j =>
    intro α hα hne hne' h
    obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα j hne hne'
    have h2 := (hs 2).1 (by rwa [show ((2 : ℤ) • Pi.single j 1 : Fin τ.rank → ℤ) =
      2 • Pi.single j 1 from Nat.cast_smul_eq_nsmul ℤ 2 _])
    have h1 := (hs 1).2 ⟨by omega, by omega⟩
    rwa [one_smul] at h1
  | @reflect i v hv ih =>
    intro α hα hne hne' h
    have hα' : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
    have hne₁ : reflect τ i α ≠ v := fun h' => hne (by rw [← h', reflect_reflect])
    have hne₂ : reflect τ i α ≠ -v := fun h' => hne' (by
      rw [← reflect_reflect τ i α, h', ← reflectHom_apply, ← reflectHom_apply, map_neg])
    have h' : IsRoot τ (reflect τ i α + 2 • v) := by
      rw [← isRoot_reflect_iff i]
      rwa [← reflectHom_apply, map_add, map_nsmul, reflectHom_apply, reflectHom_apply,
        reflect_reflect]
    have := ih hα' hne₁ hne₂ h'
    rw [← isRoot_reflect_iff i] at this
    rwa [← reflectHom_apply, map_add, reflectHom_apply, reflectHom_apply, reflect_reflect] at this

end CFSG.LieType.Steinberg.Adjoint
