module

public import CFSG.ClassicalGroups.Unitary.Transitivity

public section

noncomputable section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {n : ℕ}

theorem herm_smul_smul_eq_zero {K : Type} [Field K] {σ : K ≃+* K}
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {v : Fin n → K} (hv : herm σ v v = 0) (c : K) :
    herm σ (c • v) (c • v) = 0 := by
  rw [herm_smul_left, herm_smul_right, hv, mul_zero, mul_zero]

theorem addSubgroup_eq_top_of_T_invariant_of_span {K : Type} [Field K] [CharP K 2]
    {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n)
    (hspan : AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} = ⊤)
    (W : AddSubgroup (Fin n → K))
    (hW : ∀ t ∈ T σ n, ∀ v ∈ W, t • v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hiso : ∃ a ∈ W, a ≠ 0 ∧ herm σ a a = 0
  ·
    right
    obtain ⟨a, haW, ha0, ha⟩ := hiso
    have hall : ∀ b : Fin n → K, b ≠ 0 → herm σ b b = 0 → b ∈ W := by
      intro b hb0 hb
      obtain ⟨t, ht, htab⟩ := exists_mem_T_smul_eq_of_iso hσ hn ha0 ha hb0 hb
      rw [← htab]
      exact hW t ht a haW
    have hle : AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} ≤ W := by
      refine (AddSubgroup.closure_le W).mpr ?_
      intro b hb
      by_cases hb0 : b = 0
      · rw [hb0]
        exact W.zero_mem
      · exact hall b hb0 hb
    rw [hspan] at hle
    exact eq_top_iff.mpr hle
  ·
    push Not at hiso
    left
    refine (AddSubgroup.eq_bot_iff_forall W).mpr ?_
    intro w hw
    by_contra hw0
    have hwne : herm σ w w ≠ 0 := hiso w hw hw0
    have hex : ∃ u : Fin n → K, herm σ u u = 0 ∧ herm σ u w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      let Z : AddSubgroup (Fin n → K) :=
        { carrier := {y | herm σ y w = 0}
          zero_mem' := by
            simp only [Set.mem_setOf_eq]
            rw [herm_zero_left]
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq] at hx hy ⊢
            rw [herm_add_left, hx, hy, add_zero]
          neg_mem' := by
            intro x hx
            simp only [Set.mem_setOf_eq] at hx ⊢
            rw [herm_neg_left, hx, neg_zero] }
      have hle : AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} ≤ Z := by
        refine (AddSubgroup.closure_le Z).mpr ?_
        intro u hu
        exact hcon u hu
      have hwZ : w ∈ Z := by
        have hwS : w ∈ AddSubgroup.closure {v : Fin n → K | herm σ v v = 0} := by
          rw [hspan]
          exact AddSubgroup.mem_top w
        exact hle hwS
      exact hwne (show herm σ w w = 0 from hwZ)
    obtain ⟨u₀, hu₀iso, hu₀w⟩ := hex
    set s := herm σ u₀ w with hs
    have hs0 : s ≠ 0 := hu₀w
    set u : Fin n → K := (σ s)⁻¹ • u₀ with hu
    have hu_iso : herm σ u u = 0 := by
      rw [hu]
      exact herm_smul_smul_eq_zero hσ.invol hu₀iso _
    have hu_w : herm σ u w = 1 := by
      rw [hu, herm_smul_left, ← hs, map_inv₀, hσ.invol]
      exact inv_mul_cancel₀ hs0
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, herm_zero_left] at hu_w
      exact zero_ne_one hu_w
    have hc : (1 : K) + σ 1 = 0 := by
      rw [map_one]
      exact CharTwo.add_self_eq_zero 1
    have htvm : tv hσ.invol hu_iso hc ∈ T σ n := tv_mem_T hσ.invol hu_iso hc
    have hmem : tv hσ.invol hu_iso hc • w ∈ W := hW _ htvm w hw
    rw [tv_smul hσ.invol hu_iso hc w] at hmem
    have hwu : w + u ∈ W := by
      simpa [hu_w, one_smul] using hmem
    have huW : u ∈ W := by
      have := W.sub_mem hwu hw
      simpa using this
    exact hiso u huW hu0 hu_iso

end CFSG.ClassicalGroups.Unitary

end

end
