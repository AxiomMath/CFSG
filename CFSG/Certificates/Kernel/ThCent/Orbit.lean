module

public import CFSG.Certificates.Kernel.ThCent.Sound

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.Spec.Dce

abbrev Vec24 : Type := Fin 24 → ZMod 2

theorem card_le_mul [DecidableEq Mat24ˣ] (H : Finset Mat24ˣ)
    (hH : ∀ c ∈ H, ∀ d ∈ H, c * d⁻¹ ∈ H)
    (V : Finset Vec24) (hV : ∀ c ∈ H, ∀ u ∈ V, Matrix.vecMul u c.val ∈ V)
    {α : Type*} [DecidableEq α] (f : Vec24 → α)
    (hf : ∀ c ∈ H, ∀ u, f (Matrix.vecMul u c.val) = f u) {u₁ : Vec24} (hu₁ : u₁ ∈ V) :
    H.card ≤ (V.filter fun u => f u = f u₁).card *
      (H.filter fun c : Mat24ˣ => Matrix.vecMul u₁ c.val = u₁).card := by
  classical
  let π : Mat24ˣ → Vec24 := fun c => Matrix.vecMul u₁ c.val
  have hmaps : ∀ c ∈ H, π c ∈ V.filter fun u => f u = f u₁ := by
    intro c hc
    exact Finset.mem_filter.2 ⟨hV c hc u₁ hu₁, hf c hc u₁⟩
  rw [mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to hmaps _ fun y _ => ?_
  by_cases hne : ∃ c₀ ∈ H, π c₀ = y
  · obtain ⟨c₀, hc₀, hy⟩ := hne
    refine Finset.card_le_card_of_injOn (fun c => c * c₀⁻¹) ?_ ?_
    · intro c hc
      rw [Finset.coe_filter] at hc
      obtain ⟨hcH, hcy⟩ := hc
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hH c hcH c₀ hc₀, ?_⟩)
      have e1 : Matrix.vecMul u₁ (c : Mat24) = Matrix.vecMul u₁ (c₀ : Mat24) := hcy.trans hy.symm
      calc Matrix.vecMul u₁ ((c * c₀⁻¹ : Mat24ˣ) : Mat24)
          = Matrix.vecMul (Matrix.vecMul u₁ (c : Mat24)) ((c₀⁻¹ : Mat24ˣ) : Mat24) := by
            rw [Matrix.vecMul_vecMul, Units.val_mul]
        _ = u₁ := by
            rw [e1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.vecMul_one]
    · intro c _ d _ hcd
      exact mul_right_cancel hcd
  · push Not at hne
    have : (H.filter fun c => π c = y) = ∅ := by
      ext c
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact hne c
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

theorem getD_mem_or : ∀ (l : List Mat24) (p : ℕ), l.getD p 0 ∈ l ∨ l.getD p 0 = 0
  | [], p => Or.inr (by simp)
  | a :: l, 0 => Or.inl (by simp)
  | a :: l, p + 1 => by
    rcases getD_mem_or l p with h | h
    · exact Or.inl (by simp only [List.getD_cons_succ]; exact List.mem_cons_of_mem _ h)
    · exact Or.inr (by simp only [List.getD_cons_succ]; exact h)

theorem compM_invariant (S : Set Vec24) (B : Mat24) (Ps FL : List Mat24) (c : Mat24ˣ)
    (hPs : ∀ P ∈ Ps, (c : Mat24) * P = P * c) (hB : (c : Mat24) * B * (c : Mat24).transpose = B)
    (hS : ∀ u, Matrix.vecMul u (c : Mat24) ∈ S ↔ u ∈ S) (hFL : FL.Nodup)
    (hc1 : ∀ Y ∈ FL, (c : Mat24) * Y * ((c⁻¹ : Mat24ˣ) : Mat24) ∈ FL)
    (hc2 : ∀ Y ∈ FL, ((c⁻¹ : Mat24ˣ) : Mat24) * Y * (c : Mat24) ∈ FL) (u : Vec24) (q : ℕ) :
    compM S B Ps FL (Matrix.vecMul u (c : Mat24)) q = compM S B Ps FL u q := by
  classical
  have hcc : (c : Mat24) * ((c⁻¹ : Mat24ˣ) : Mat24) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcc' : ((c⁻¹ : Mat24ˣ) : Mat24) * (c : Mat24) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hP : (c : Mat24) * Ps.getD (q / 3) 0 = Ps.getD (q / 3) 0 * c := by
    rcases getD_mem_or Ps (q / 3) with h | h
    · exact hPs _ h
    · rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have hw : Matrix.vecMul (Matrix.vecMul u (c : Mat24)) (Ps.getD (q / 3) 0) =
      Matrix.vecMul (Matrix.vecMul u (Ps.getD (q / 3) 0)) (c : Mat24) := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hP]
  have key : ∀ x w : Vec24, Matrix.vecMul (Matrix.vecMul x (c : Mat24)) B ⬝ᵥ
      Matrix.vecMul w (c : Mat24) = Matrix.vecMul x B ⬝ᵥ w := by
    intro x w
    have e : Matrix.vecMul w (c : Mat24) = Matrix.mulVec (c : Mat24).transpose w := by
      rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
    rw [e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
      hB]
  have hzero : ∀ w : Vec24, Matrix.vecMul w (c : Mat24) = 0 ↔ w = 0 := by
    intro w
    constructor
    · intro h
      have := congrArg (fun x => Matrix.vecMul x ((c⁻¹ : Mat24ˣ) : Mat24)) h
      simp only [Matrix.vecMul_vecMul, hcc, Matrix.vecMul_one, Matrix.zero_vecMul] at this
      exact this
    · intro h
      rw [h, Matrix.zero_vecMul]
  unfold compM
  by_cases h3 : q = 3 * Ps.length
  · rw [if_pos h3, if_pos h3]
    unfold codeFM
    rw [← List.toFinset_card_of_nodup (hFL.filter _), ← List.toFinset_card_of_nodup (hFL.filter _)]
    simp only [List.toFinset_filter]
    refine Finset.card_bij (fun Y _ => (c : Mat24) * Y * ((c⁻¹ : Mat24ˣ) : Mat24)) ?_ ?_ ?_
    · intro Y hY
      rw [Finset.mem_filter, List.mem_toFinset] at hY ⊢
      refine ⟨hc1 Y hY.1, ?_⟩
      have h1 := of_decide_eq_true hY.2
      rw [decide_eq_true_iff]
      calc Matrix.vecMul u ((c : Mat24) * Y * ((c⁻¹ : Mat24ˣ) : Mat24))
          = Matrix.vecMul (Matrix.vecMul (Matrix.vecMul u (c : Mat24)) Y)
              ((c⁻¹ : Mat24ˣ) : Mat24) := by simp only [Matrix.vecMul_vecMul]
        _ = u := by rw [h1, Matrix.vecMul_vecMul, hcc, Matrix.vecMul_one]
    · intro Y _ Z _ hYZ
      have := congrArg (fun X => ((c⁻¹ : Mat24ˣ) : Mat24) * X * (c : Mat24)) hYZ
      simp only [Matrix.mul_assoc, hcc', Matrix.mul_one] at this
      simp only [← Matrix.mul_assoc, hcc', Matrix.one_mul] at this
      exact this
    · intro Z hZ
      rw [Finset.mem_filter, List.mem_toFinset] at hZ
      refine ⟨((c⁻¹ : Mat24ˣ) : Mat24) * Z * (c : Mat24), ?_, ?_⟩
      · rw [Finset.mem_filter, List.mem_toFinset]
        refine ⟨hc2 Z hZ.1, ?_⟩
        have h1 := of_decide_eq_true hZ.2
        rw [decide_eq_true_iff]
        calc Matrix.vecMul (Matrix.vecMul u (c : Mat24))
              (((c⁻¹ : Mat24ˣ) : Mat24) * Z * (c : Mat24))
            = Matrix.vecMul (Matrix.vecMul u ((c : Mat24) * ((c⁻¹ : Mat24ˣ) : Mat24) * Z))
                (c : Mat24) := by simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
          _ = Matrix.vecMul u (c : Mat24) := by rw [hcc, Matrix.one_mul, h1]
      · simp only [← Matrix.mul_assoc, hcc, Matrix.one_mul]
        rw [Matrix.mul_assoc, hcc, Matrix.mul_one]
  rw [if_neg h3, if_neg h3, hw]
  by_cases h0 : q % 3 = 0
  · rw [if_pos h0, if_pos h0]
    simp only [hzero]
  rw [if_neg h0, if_neg h0]
  by_cases h1 : q % 3 = 1
  · rw [if_pos h1, if_pos h1, key]
  rw [if_neg h1, if_neg h1]
  simp only [hS]

end CFSG.KC.ThCent

end
