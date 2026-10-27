module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DataE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def eqπ {n : ℕ} (a b : Wr n) : Prop := a = b ∨ a = b * allOnes n

instance {n : ℕ} (a b : Wr n) : Decidable (eqπ a b) := by unfold eqπ; infer_instance

@[expose] def look (t : Wr 7) : List Nat :=
  match s32.find? (fun c => decide (eqπ c.1 t)) with
  | some c => c.2
  | none => []

@[expose] def stepW (c1 t : Wr 7) : Wr 7 := evalW [aW, bW, c1] (look t)

@[expose] def inS (t : Wr 7) : Prop := ∃ c ∈ s32, eqπ c.1 t

instance (t : Wr 7) : Decidable (inS t) := by unfold inS; infer_instance

theorem dyn_ok : ∀ e ∈ s32, inS e.1 ∧ inS (stepW e.1 e.1) ∧ inS (stepW e.1 (stepW e.1 e.1)) ∧
    eqπ (stepW e.1 (stepW e.1 (stepW e.1 e.1))) hW := by decide +kernel

theorem look_spec {t : Wr 7} (ht : inS t) : eqπ (evalW [aW, bW, hW] (look t)) t := by
  unfold look
  obtain ⟨c, hc, hct⟩ := ht
  have hsome : (s32.find? (fun c => decide (eqπ c.1 t))).isSome :=
    List.find?_isSome.mpr ⟨c, hc, by simpa using hct⟩
  cases hf : s32.find? (fun c => decide (eqπ c.1 t)) with
  | none => rw [hf] at hsome; simp at hsome
  | some c' =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only
    rw [s32_words c' h2]
    simpa using h1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
