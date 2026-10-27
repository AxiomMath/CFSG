module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUp Equiv

private theorem comm_swap_apply {m : ℕ} {a b : Fin m} (hab : a ≠ b) {σ : Perm (Fin m)}
    (h : σ * swap a b = swap a b * σ) : σ a = a ∧ σ b = b ∨ σ a = b ∧ σ b = a := by
  have e1 : σ b = swap a b (σ a) := by
    have := congrArg (fun f : Perm (Fin m) => f a) h
    simpa using this
  by_cases h1 : σ a = a
  · left
    refine ⟨h1, ?_⟩
    rw [e1, h1]
    simp
  by_cases h2 : σ a = b
  · right
    refine ⟨h2, ?_⟩
    rw [e1, h2]
    simp
  · exfalso
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at e1
    exact hab (σ.injective e1.symm)

private theorem le_alternating_of_perfect {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} (hperf : ⁅H, H⁆ = H) : H ≤ alternatingGroup α := by
  calc H = ⁅H, H⁆ := hperf.symm
    _ ≤ commutator (Perm α) := Subgroup.commutator_mono le_top le_top
    _ ≤ alternatingGroup α := alternatingGroup.commutator_perm_le

private theorem fixes_of_perfect_comm_swap {m : ℕ} {a b : Fin m} (hab : a ≠ b)
    {H : Subgroup (Perm (Fin m))} (hperf : ⁅H, H⁆ = H)
    (hcomm : ∀ σ ∈ H, σ * swap a b = swap a b * σ) : ∀ σ ∈ H, σ a = a := by
  classical
  have hP : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  let f : ↥H →* Multiplicative (ZMod 2) :=
    { toFun := fun σ => if (σ : Perm (Fin m)) a = a then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := by
        intro σ τ
        have hσ := comm_swap_apply hab (hcomm σ σ.2)
        have hτ := comm_swap_apply hab (hcomm τ τ.2)
        have hba : b ≠ a := Ne.symm hab
        rcases hσ with ⟨hσa, hσb⟩ | ⟨hσa, hσb⟩ <;> rcases hτ with ⟨hτa, hτb⟩ | ⟨hτa, hτb⟩
        · simp [hσa, hτa]
        · simp [hσa, hσb, hτa, hba]
        · simp [hσa, hτa, hba]
        · simp [hσa, hσb, hτa, hba]
          decide }
  have hrange : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isMulCommutative (G := f.range) inferInstance
  intro σ hσ
  have h1 : f ⟨σ, hσ⟩ = 1 := by
    have : (⟨f ⟨σ, hσ⟩, ⟨_, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  by_contra hne
  simp [f, hne] at h1


theorem eq_altStabilizer_of_perfect_comm_swap {n : ℕ} (hn : 2 ≤ n) {a b : Fin (n + 2)}
    (hab : a ≠ b)
    {H : Subgroup (Perm (Fin (n + 2)))} (hperf : ⁅H, H⁆ = H)
    (hcomm : ∀ σ ∈ H, σ * swap a b = swap a b * σ) (hcard : Nat.card ↥H = n.factorial / 2) :
    H = (altStabilizer (n + 2) {a, b}).map (alternatingGroup (Fin (n + 2))).subtype := by
  have hfix := fixes_of_perfect_comm_swap hab hperf hcomm
  have hfixb : ∀ σ ∈ H, σ b = b := by
    intro σ hσ
    rcases comm_swap_apply hab (hcomm σ hσ) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd ((hfix σ hσ).symm.trans h) hab
  have hle : H ≤ (altStabilizer (n + 2) {a, b}).map (alternatingGroup (Fin (n + 2))).subtype := by
    intro σ hσ
    have hA : σ ∈ alternatingGroup (Fin (n + 2)) := le_alternating_of_perfect hperf hσ
    refine ⟨⟨σ, hA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_altStabilizer_iff]
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hfix σ hσ
    · exact hfixb σ hσ
  have h2 : ({a, b} : Finset (Fin (n + 2))).card = 2 := Finset.card_pair hab
  have hcard2 : Nat.card ((altStabilizer (n + 2) {a, b}).map
      (alternatingGroup (Fin (n + 2))).subtype) = n.factorial / 2 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin (n + 2))).subtype_injective]
    have h3 := card_altStabilizer (m := n + 2) (F := {a, b}) (by rw [h2]; omega)
    rw [h2] at h3
    simpa using h3
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard2])

end CFSG.CGT.PushingUpLit.CGT6
