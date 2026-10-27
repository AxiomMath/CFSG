module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NV
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NT1

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem dCols_fix_zk : ∀ p q : Fin 2, lin dCols (p, 0, 0, q) = (p, 0, 0, q) → p = 0 := by decide

theorem comm_conj_of_commute {G : Type*} [Group G] {a g b : G} (h : a * g = g * a) :
    a * (g * b * g⁻¹) * a⁻¹ * (g * b * g⁻¹)⁻¹ = g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by
  have h' : a = g * a * g⁻¹ := by rw [← h]; group
  conv_lhs => rw [h']
  group

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable {I : S.Inst}

theorem k_eq_wV (I : S.Inst) : ∃ κ : Fin 2, S.k = I.wV (κ, 0, 0, 1) := by
  rcases I.ki_eq with h | h
  · exact ⟨0, by simp [wV, h]⟩
  · refine ⟨1, ?_⟩
    simp only [wV, h, Fin.val_one, pow_one, Fin.val_zero, pow_zero, mul_one]
    rw [← mul_assoc, ← pow_two, S.z_sq, one_mul]

theorem zk_eq_wV (I : S.Inst) (a b : Fin 2) :
    ∃ p q : Fin 2, S.z ^ (a : ℕ) * S.k ^ (b : ℕ) = I.wV (p, 0, 0, q) := by
  obtain ⟨κ, hκ⟩ := I.k_eq_wV
  refine ⟨a + κ * b, b, ?_⟩
  have hz : S.z = I.wV (1, 0, 0, 0) := by simp [wV]
  rw [hz, hκ, ← I.wV_smul, ← I.wV_smul, ← I.wV_add]
  congr 1
  fin_cases a <;> fin_cases b <;> fin_cases κ <;> rfl

variable {H : S.Sec6Hyp T₁} (P : I.Pre6 H)

namespace Pre6

theorem exists_u {v : X} (hvT : v ∈ T₁) (hvM : I.Mat v vC) (hvd : v * P.d = P.d * v) :
    ∃ u, (u = I.ui ∨ u = S.t * I.ui) ∧ u * v = v * u := by
  set d := P.d with hd
  have huT : I.ui ∈ T₁ := H.le I.ui_mem_T
  obtain ⟨a, b, hab⟩ := H.commutator_mem huT hvT
  obtain ⟨p, q, hpq⟩ := I.zk_eq_wV a b
  rw [hpq] at hab
  have h1 : d * (I.ui * v * I.ui⁻¹) = (I.ui * v * I.ui⁻¹) * d := by
    have e1 : (I.ui * v * I.ui⁻¹) * (I.ui * d * I.ui⁻¹) =
        (I.ui * d * I.ui⁻¹) * (I.ui * v * I.ui⁻¹) := by
      calc (I.ui * v * I.ui⁻¹) * (I.ui * d * I.ui⁻¹) = I.ui * (v * d) * I.ui⁻¹ := by group
        _ = I.ui * (d * v) * I.ui⁻¹ := by rw [hvd]
        _ = (I.ui * d * I.ui⁻¹) * (I.ui * v * I.ui⁻¹) := by group
    rw [P.d_inv] at e1
    calc d * (I.ui * v * I.ui⁻¹) = d * ((I.ui * v * I.ui⁻¹) * d⁻¹) * d := by group
      _ = d * (d⁻¹ * (I.ui * v * I.ui⁻¹)) * d := by rw [e1]
      _ = (I.ui * v * I.ui⁻¹) * d := by group
  have h2 : d * I.wV (p, 0, 0, q) * d⁻¹ = I.wV (p, 0, 0, q) := by
    rw [← hab]
    have hA : d * (I.ui * v * I.ui⁻¹) * d⁻¹ = I.ui * v * I.ui⁻¹ := by rw [h1]; group
    have hv' : d * v⁻¹ * d⁻¹ = v⁻¹ := by
      calc d * v⁻¹ * d⁻¹ = v⁻¹ * (v * d) * v⁻¹ * d⁻¹ := by group
        _ = v⁻¹ * (d * v) * v⁻¹ * d⁻¹ := by rw [hvd]
        _ = v⁻¹ := by group
    calc d * (I.ui * v * I.ui⁻¹ * v⁻¹) * d⁻¹ =
        (d * (I.ui * v * I.ui⁻¹) * d⁻¹) * (d * v⁻¹ * d⁻¹) := by group
      _ = I.ui * v * I.ui⁻¹ * v⁻¹ := by rw [hA, hv']
  rw [P.d_mat.conj] at h2
  have hp : p = 0 := dCols_fix_zk p q (I.wV_injective h2)
  subst hp
  have hki : I.wV (0, 0, 0, q) = I.ki ^ (q : ℕ) := by simp [wV]
  rw [hki] at hab
  have huv : I.ui * v * I.ui⁻¹ = I.ki ^ (q : ℕ) * v := by
    calc I.ui * v * I.ui⁻¹ = I.ui * v * I.ui⁻¹ * v⁻¹ * v := by group
      _ = I.ki ^ (q : ℕ) * v := by rw [hab]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with rfl | rfl
  · refine ⟨I.ui, Or.inl rfl, ?_⟩
    simp only [Fin.val_zero, pow_zero, one_mul] at huv
    calc I.ui * v = I.ui * v * I.ui⁻¹ * I.ui := by group
      _ = v * I.ui := by rw [huv]
  · refine ⟨S.t * I.ui, Or.inr rfl, ?_⟩
    simp only [Fin.val_one, pow_one] at huv
    have htv : S.t * v * S.t⁻¹ = I.ki * v := by
      have hvt : v * S.t * v⁻¹ = S.t * I.ki := by
        rw [hvM.conj_t]; simp [vC, wV]
      have htk : S.t * I.ki = I.ki * S.t := I.comm I.t_mem_E I.ki_mem_E
      have ht2 : S.t * S.t = 1 := by rw [← pow_two]; exact S.t_sq
      have hti : S.t⁻¹ = S.t := inv_eq_of_mul_eq_one_right ht2
      calc S.t * v * S.t⁻¹ = S.t * (v * S.t * v⁻¹) * v * S.t⁻¹ * S.t⁻¹ := by group
        _ = S.t * (S.t * I.ki) * v * (S.t * S.t)⁻¹ := by rw [hvt]; group
        _ = I.ki * v := by rw [ht2, inv_one, mul_one, ← mul_assoc, ht2, one_mul]
    have hkv : I.ki * v = v * I.ki := by
      have := hvM.conj_ki
      rw [show I.wV (vC 3) = I.ki by simp [vC, wV]] at this
      calc I.ki * v = v * (v⁻¹ * I.ki * v) := by group
        _ = v * I.ki := by
            congr 1
            calc v⁻¹ * I.ki * v = v⁻¹ * (v * I.ki * v⁻¹) * v := by rw [this]
              _ = I.ki := by group
    have hki2 : I.ki * I.ki = 1 := by rw [← pow_two]; exact I.ki_sq
    have htk : S.t * I.ki = I.ki * S.t := I.comm I.t_mem_E I.ki_mem_E
    calc S.t * I.ui * v = S.t * (I.ui * v * I.ui⁻¹) * I.ui := by group
      _ = S.t * (I.ki * v) * I.ui := by rw [huv]
      _ = (S.t * I.ki) * v * I.ui := by group
      _ = I.ki * (S.t * v * S.t⁻¹) * S.t * I.ui := by rw [htk]; group
      _ = I.ki * (I.ki * v) * S.t * I.ui := by rw [htv]
      _ = v * (S.t * I.ui) := by rw [← mul_assoc, hki2, one_mul]; group

end Pre6

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
