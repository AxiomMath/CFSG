module

public import CFSG.LieType.SpinGeom.Mem

public section

namespace CFSG.LieType.SpinGeom

open scoped Matrix

variable {K : Type} [Field K]

theorem addSubgroup_eq_bot_or_top_of_transvection (N : AddSubgroup (Fin 3 → K))
    (hN : ∀ (i j : Fin 3), i ≠ j → ∀ (s : K) (v : Fin 3 → K), v ∈ N →
      (Matrix.transvection i j s *ᵥ v) ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases hbot : ∀ x ∈ N, x = 0
  · exact Or.inl ((AddSubgroup.eq_bot_iff_forall N).2 hbot)
  right
  obtain ⟨v, hvN, hv0⟩ : ∃ v ∈ N, v ≠ 0 :=
    Classical.byContradiction fun h => hbot fun x hx =>
      Classical.byContradiction fun hx0 => h ⟨x, hx, hx0⟩
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, hj⟩
  have h1 : ∀ i, i ≠ j → ∀ s : K, (Pi.single i s : Fin 3 → K) ∈ N := by
    intro i hij s
    have h := N.sub_mem (hN i j hij (s / v j) v hvN) hvN
    convert h using 1
    ext l
    rw [Pi.sub_apply, transvection_mulVec_apply]
    by_cases hl : i = l
    · subst hl
      simp [hj]
    · simp [hl, Ne.symm hl]
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 3, i ≠ j := by
    by_cases hj0 : j = 0
    · exact ⟨1, by rw [hj0]; decide⟩
    · exact ⟨0, fun h => hj0 h.symm⟩
  have h2 : ∀ s : K, (Pi.single j s : Fin 3 → K) ∈ N := by
    intro s
    have h := N.sub_mem (hN j i₀ hi₀.symm s (Pi.single i₀ 1) (h1 i₀ hi₀ 1)) (h1 i₀ hi₀ 1)
    convert h using 1
    ext l
    rw [Pi.sub_apply, transvection_mulVec_apply]
    by_cases hl : j = l
    · subst hl
      simp [hi₀]
    · simp [Pi.single_apply, hl, Ne.symm hl]
  have h3 : ∀ k s, (Pi.single k s : Fin 3 → K) ∈ N := by
    intro k s
    by_cases hk : k = j
    · subst hk
      exact h2 s
    · exact h1 k hk s
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  exact AddSubgroup.sum_mem _ fun k _ => h3 k (x k)

end CFSG.LieType.SpinGeom
