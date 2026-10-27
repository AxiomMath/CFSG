module

public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent

public section

namespace CFSG.GH74.Generic.S45

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Perm

variable {X : Type} [Group X]

abbrev Comp (X : Type) [Group X] : Type := {M : Subgroup X // IsComponent M}

theorem conjSub_one_comp (K : Subgroup X) : conjSub 1 K = K := by
  ext v
  simp [conjSub, Subgroup.mem_map]

theorem conjSub_mul_comp (g h : X) (K : Subgroup X) :
    conjSub (g * h) K = conjSub g (conjSub h K) := by
  unfold conjSub
  rw [Subgroup.map_map]
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
    ext a
    simp [mul_assoc]
  rw [this]

@[expose] noncomputable def compPerm (g : X) : Equiv.Perm (Comp X) where
  toFun M := ⟨conjSub g M.1, isComponent_conjSub M.2 g⟩
  invFun M := ⟨conjSub g⁻¹ M.1, isComponent_conjSub M.2 g⁻¹⟩
  left_inv M := Subtype.ext (by
    show conjSub g⁻¹ (conjSub g M.1) = M.1
    rw [← conjSub_mul_comp, inv_mul_cancel, conjSub_one_comp])
  right_inv M := Subtype.ext (by
    show conjSub g (conjSub g⁻¹ M.1) = M.1
    rw [← conjSub_mul_comp, mul_inv_cancel, conjSub_one_comp])

@[expose] noncomputable def compPermHom : X →* Equiv.Perm (Comp X) where
  toFun := compPerm
  map_one' := Equiv.ext fun M => Subtype.ext (conjSub_one_comp M.1)
  map_mul' g h := Equiv.ext fun M => Subtype.ext (conjSub_mul_comp g h M.1)

omit [Group X] in
theorem eq_one_of_mem_commutator_units {Y : Type} [Group Y] (f : Y →* ℤˣ) {y : Y}
    (hy : y ∈ _root_.commutator Y) : f y = 1 := by
  have : _root_.commutator Y ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  exact this hy

theorem exists_second_swapped [Finite X] {t : X} (ht : t ∈ _root_.commutator X) (ht2 : t * t = 1)
    {A : Subgroup X} (hA : IsComponent A) (hne : conjSub t⁻¹ A ≠ A) :
    ∃ B : Subgroup X, IsComponent B ∧ conjSub t⁻¹ B ≠ B ∧ B ≠ A ∧ B ≠ conjSub t⁻¹ A := by
  classical
  have : Fintype (Comp X) := Fintype.ofFinite _
  set σ : Equiv.Perm (Comp X) := compPermHom t⁻¹ with hσ
  have hσs : Equiv.Perm.sign σ = 1 := by
    have h1 : t⁻¹ ∈ _root_.commutator X := inv_mem ht
    exact eq_one_of_mem_commutator_units (Equiv.Perm.sign.comp compPermHom) h1
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul, ← mul_inv_rev, ht2, inv_one, map_one]
  let a : Comp X := ⟨A, hA⟩
  let b : Comp X := σ a
  have hb : (b : Subgroup X) = conjSub t⁻¹ A := rfl
  have hab : a ≠ b := fun h => hne (by rw [← hb, ← h])
  set τ : Equiv.Perm (Comp X) := Equiv.swap a b with hτ
  set σ' : Equiv.Perm (Comp X) := σ * τ with hσ'
  have hσ'a : σ' a = a := by
    show σ (τ a) = a
    rw [hτ, Equiv.swap_apply_left]
    have := congrArg (fun p : Equiv.Perm (Comp X) => p a) hσσ
    simpa using this
  have hσ'b : σ' b = b := by
    show σ (τ b) = b
    rw [hτ, Equiv.swap_apply_right]
  have hsign : Equiv.Perm.sign σ' = -1 := by
    rw [hσ', Equiv.Perm.sign_mul, hσs, hτ, Equiv.Perm.sign_swap hab, one_mul]
  have hne1 : σ' ≠ 1 := fun h => by
    rw [h, Equiv.Perm.sign_one] at hsign
    exact absurd hsign (by decide)
  obtain ⟨m, hm⟩ : ∃ m : Comp X, σ' m ≠ m := by
    by_contra hcon
    push Not at hcon
    exact hne1 (Equiv.ext hcon)
  have hma : m ≠ a := fun h => hm (by rw [h]; exact hσ'a)
  have hmb : m ≠ b := fun h => hm (by rw [h]; exact hσ'b)
  have hτm : τ m = m := by
    rw [hτ]
    exact Equiv.swap_apply_of_ne_of_ne hma hmb
  have hσm : σ m ≠ m := by
    intro h
    apply hm
    show σ (τ m) = m
    rw [hτm]
    exact h
  refine ⟨m.1, m.2, ?_, fun h => hma (Subtype.ext h), fun h => hmb (Subtype.ext h)⟩
  intro h
  exact hσm (Subtype.ext h)

end Perm

end CFSG.GH74.Generic.S45
