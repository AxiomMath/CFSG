module

public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG.GroupTheory

theorem apply_mem_pair_of_commute {α : Type*} [DecidableEq α]
    {σ : Equiv.Perm α} {i j : α} (hij : i ≠ j)
    (h : Commute σ (Equiv.swap i j)) : σ i = i ∨ σ i = j := by
  by_contra hmem
  push Not at hmem
  have hfix : Equiv.swap i j (σ i) = σ i :=
    Equiv.swap_apply_of_ne_of_ne hmem.1 hmem.2
  have h1 : σ j = Equiv.swap i j (σ i) := by
    have h2 := congrArg (fun f : Equiv.Perm α => f i) h.eq
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h2
  have h2 : σ j = σ i := by rw [h1, hfix]
  exact hij (σ.injective h2).symm

theorem exists_swap_swap_of_not_commute {α : Type*} [DecidableEq α]
    {i j a b : α} (hij : i ≠ j) (hab : a ≠ b)
    (h : ¬ Commute (Equiv.swap i j) (Equiv.swap a b)) :
    ∃ i' j' k' : α, i' ≠ j' ∧ j' ≠ k' ∧ i' ≠ k' ∧
      Equiv.swap i j = Equiv.swap i' j' ∧ Equiv.swap a b = Equiv.swap j' k' := by
  have hmem : a = i ∨ a = j ∨ b = i ∨ b = j := by
    by_contra hcon
    push Not at hcon
    apply h
    exact (Equiv.Perm.disjoint_swap_swap (by
      simp [List.nodup_cons, hij, hab, hcon.1.symm, hcon.2.1.symm,
        hcon.2.2.1.symm, hcon.2.2.2.symm])).commute
  rcases hmem with hai | haj | hbi | hbj
  · have hbi : b ≠ i := fun h' => hab (hai.trans h'.symm)
    have hbj : b ≠ j := fun h' => h (by rw [hai, h'])
    exact ⟨j, i, b, hij.symm, hbi.symm, hbj.symm, Equiv.swap_comm i j, by rw [hai]⟩
  · have hbi : b ≠ i := fun h' => h (by rw [haj, h', Equiv.swap_comm])
    have hbj : b ≠ j := fun h' => hab (haj.trans h'.symm)
    exact ⟨i, j, b, hij, hbj.symm, hbi.symm, rfl, by rw [haj]⟩
  · have hai : a ≠ i := fun h' => hab (h'.trans hbi.symm)
    have haj : a ≠ j := fun h' => h (by rw [h', hbi, Equiv.swap_comm])
    exact ⟨j, i, a, hij.symm, hai.symm, haj.symm, Equiv.swap_comm i j,
      by rw [hbi, Equiv.swap_comm]⟩
  · have hai : a ≠ i := fun h' => h (by rw [h', hbj])
    have haj : a ≠ j := fun h' => hab (h'.trans hbj.symm)
    exact ⟨i, j, a, hij, haj.symm, hai.symm, rfl, by rw [hbj, Equiv.swap_comm]⟩

end CFSG.GroupTheory
