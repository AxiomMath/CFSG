module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseVanishing

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalGeneralBase

theorem coefficient_off_middle {m M : ℕ} [NeZero m] (hm : m = 2 * M)
    (f : ZMod m → ZMod m → ℂ) (hsym : ∀ i j, f i j = f j i ∧ f i j = f j (-i - j)) (ξ : ℂ)
    (h00 : f 0 0 = 0) (hMM : f M M = 0)
    (hdiag : ∀ t ∈ Finset.Ico 1 M,
      f t t = ξ ∧ f ((t + M : ℕ) : ZMod m) ((t + M : ℕ) : ZMod m) = ξ)
    {V : Finset (ZMod m × ZMod m)}
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I)
    (hgen : ∀ I ∈ V, f I.1 I.2 = ξ) :
    (∀ i j, (i, j) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
        (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = 0) ∧
      ∀ i j, (i, j) ∉ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
        (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) → f i j = ξ := by
  have hinv : ∀ I J : ZMod m × ZMod m, J ∈ MulAction.orbit (dualGroup m) I →
      f J.1 J.2 = f I.1 I.2 := fun I J hJ => base_column_orbit_invariant f hsym hJ
  have hmid := orbit_middle (m := m) hm
  have hMorb : ∀ i j, (i, j) ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) →
      f i j = 0 := fun i j h => by
    rw [hinv _ (i, j) h]
    exact hMM
  have hSorb : ∀ i j, (i, j) ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) →
      (i, j) ∈ ({(0, 0), ((M : ZMod m), (M : ZMod m)), ((M : ZMod m), 0),
        (0, (M : ZMod m))} : Set (ZMod m × ZMod m)) := fun i j h => by
    rw [hmid] at h
    exact Set.mem_insert_of_mem _ h
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rcases h with h | h
    · rw [Prod.mk.injEq] at h
      rw [h.1, h.2]
      exact h00
    · rw [← hmid] at h
      exact hMorb i j h
  · rcases orbit_trichotomy (i, j) with h0 | ⟨r, hr, hr'⟩ | h6
    · have hself : (i, j) ∈ MulAction.orbit (dualGroup m) (i, j) := MulAction.mem_orbit_self _
      rw [h0] at hself
      exact absurd (Or.inl hself) h
    · have hmem : (i, j) ∈ MulAction.orbit (dualGroup m) (r, r) := by
        rw [← hr']
        exact MulAction.mem_orbit_self _
      rw [hinv _ (i, j) hmem]
      have hval : ((r.val : ℕ) : ZMod m) = r := ZMod.natCast_zmod_val r
      have hlt : r.val < m := ZMod.val_lt r
      have hpos : r.val ≠ 0 := fun h0 => hr ((ZMod.val_eq_zero r).mp h0)
      rcases lt_trichotomy r.val M with hlt' | heq | hgt
      · rw [← hval]
        exact (hdiag r.val (Finset.mem_Ico.mpr ⟨Nat.pos_of_ne_zero hpos, hlt'⟩)).1
      · exfalso
        rw [← hval, heq] at hmem
        exact h (hSorb i j hmem)
      · have ht : r.val - M ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        have hr2 : ((r.val - M + M : ℕ) : ZMod m) = r := by
          rw [Nat.sub_add_cancel hgt.le, hval]
        have h2 := (hdiag (r.val - M) ht).2
        rw [hr2] at h2
        exact h2
    · obtain ⟨J, ⟨hJV, hJorb⟩, -⟩ := hVrep (i, j) h6
      rw [← hinv (i, j) J hJorb]
      exact hgen J hJV

theorem orbit_cover {m M : ℕ} [NeZero m] (hm : m = 2 * M) {V : Finset (ZMod m × ZMod m)}
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I) (I : ZMod m × ZMod m) :
    I = (0, 0) ∨ I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
      (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
        I ∈ MulAction.orbit (dualGroup m) (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m))) ∨
      ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I' := by
  rcases orbit_trichotomy I with h0 | ⟨r, hr, hr'⟩ | h6
  · left
    have hself : I ∈ MulAction.orbit (dualGroup m) I := MulAction.mem_orbit_self _
    rw [h0] at hself
    exact hself
  · have hmem : I ∈ MulAction.orbit (dualGroup m) (r, r) := by
      rw [← hr']
      exact MulAction.mem_orbit_self _
    have hval : ((r.val : ℕ) : ZMod m) = r := ZMod.natCast_zmod_val r
    have hlt : r.val < m := ZMod.val_lt r
    have hpos : r.val ≠ 0 := fun h0 => hr ((ZMod.val_eq_zero r).mp h0)
    rcases lt_trichotomy r.val M with hlt' | heq | hgt
    · refine Or.inr (Or.inr (Or.inl ⟨r.val, Finset.mem_Ico.mpr
        ⟨Nat.pos_of_ne_zero hpos, hlt'⟩, Or.inl ?_⟩))
      rw [hval]
      exact hmem
    · refine Or.inr (Or.inl ?_)
      rw [← hval, heq] at hmem
      exact hmem
    · refine Or.inr (Or.inr (Or.inl ⟨r.val - M, Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
        Or.inr ?_⟩))
      rw [Nat.sub_add_cancel hgt.le, hval]
      exact hmem
  · obtain ⟨J, ⟨hJV, hJorb⟩, -⟩ := hVrep I h6
    exact Or.inr (Or.inr (Or.inr ⟨J, hJV, MulAction.mem_orbit_symm.mp hJorb⟩))

theorem value_eq_zero_of_residual {m M : ℕ} [NeZero m] (hm : m = 2 * M) (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (f : ZMod m → ZMod m → ℂ)
    (hsym : ∀ i j, f i j = f j i ∧ f i j = f j (-i - j)) (ξ : ℂ) (h00 : f 0 0 = 0)
    (hMM : f M M = 0)
    (hdiag : ∀ t ∈ Finset.Ico 1 M,
      f t t = ξ ∧ f ((t + M : ℕ) : ZMod m) ((t + M : ℕ) : ZMod m) = ξ)
    {V : Finset (ZMod m × ZMod m)}
    (hVrep : ∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
      ∃! J, J ∈ V ∧ J ∈ MulAction.orbit (dualGroup m) I)
    (hgen : ∀ I ∈ V, f I.1 I.2 = ξ) (X : ℕ → ℂ) (hX : ∀ j ∈ Finset.Ico 1 m, X j = 0)
    {val A₁ A₂ : ℂ}
    (hval : 2 * val = A₁ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) * X j +
      A₂ * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) *
        (∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i))) :
    val = 0 := by
  obtain ⟨hf0, hf1⟩ := coefficient_off_middle hm f hsym ξ h00 hMM hdiag hVrep hgen
  have hD := antidiagonal_difference hm hM ξ f hf0 hf1 (fun l => ∑ i : ZMod m, f i (l - i))
    fun l => rfl
  simp only [Nat.cast_one] at hval
  exact row_value_eq_zero hm hM hζ X
    (fun j => ∑ i : ZMod m, f i (0 - i) - ∑ i : ZMod m, f i (-(j : ZMod m) - i)) hval hX hD

end CFSG.Wreathed.ConditionalCompleteBase
