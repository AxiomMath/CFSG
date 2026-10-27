module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7TFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

@[expose] noncomputable def W (yi : X) (a b c d : Fin 2) : X :=
  S.z ^ (a : ℕ) * yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ)

theorem W_mem_T {yi : X} (hyi : yi ∈ S.data.T) (a b c d : Fin 2) : S.W yi a b c d ∈ S.data.T :=
  mul_mem (mul_mem (mul_mem (pow_mem S.z_mem.1 _) (pow_mem hyi _)) (pow_mem S.data.t_mem_T _))
    (pow_mem S.k_mem _)

theorem W_mem_E {yi : X} (a b c d : Fin 2) : S.W yi a b c d ∈ S.E yi :=
  mul_mem (mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
    (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _))
    (pow_mem (subset_closure (by simp)) _)

theorem eq_W {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {e : X} (he : e ∈ S.E yi) :
    ∃ a b c d : Fin 2, e = S.W yi a b c d := by
  rcases hyi with rfl | rfl
  · exact S.eq_of_mem_E S.y_mem S.y_sq (S.z_comm_of_mem_T S.y_mem.1) he
  · exact S.eq_of_mem_E S.xy_mem S.xy_sq (S.z_comm_of_mem_T S.xy_mem.1) he

theorem W_injective {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {a b c d a' b' c' d' : Fin 2}
    (h : S.W yi a b c d = S.W yi a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  rcases hyi with rfl | rfl
  · have h' : S.coords ⟨S.z ^ (a : ℕ) * S.y ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ),
        S.W_mem_T S.y_mem.1 a b c d⟩ =
        S.coords ⟨S.z ^ (a' : ℕ) * S.y ^ (b' : ℕ) * S.t ^ (c' : ℕ) * S.k ^ (d' : ℕ),
          S.W_mem_T S.y_mem.1 a' b' c' d'⟩ := congrArg S.coords (Subtype.ext h)
    have e1 := S.coords_prod S.y_mem.1 S.coords_y a b c d (S.W_mem_T S.y_mem.1 a b c d)
    have e2 := S.coords_prod S.y_mem.1 S.coords_y a' b' c' d' (S.W_mem_T S.y_mem.1 a' b' c' d')
    have h'' := e1.symm.trans (h'.trans e2)
    clear h h' e1 e2
    revert h''
    revert a b c d a' b' c' d'
    decide
  · have h' : S.coords ⟨S.z ^ (a : ℕ) * (S.x * S.y) ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ),
        S.W_mem_T S.xy_mem.1 a b c d⟩ =
        S.coords ⟨S.z ^ (a' : ℕ) * (S.x * S.y) ^ (b' : ℕ) * S.t ^ (c' : ℕ) * S.k ^ (d' : ℕ),
          S.W_mem_T S.xy_mem.1 a' b' c' d'⟩ := congrArg S.coords (Subtype.ext h)
    have e1 := S.coords_prod S.xy_mem.1 S.coords_xy a b c d (S.W_mem_T S.xy_mem.1 a b c d)
    have e2 := S.coords_prod S.xy_mem.1 S.coords_xy a' b' c' d'
      (S.W_mem_T S.xy_mem.1 a' b' c' d')
    have h'' := e1.symm.trans (h'.trans e2)
    clear h h' e1 e2
    revert h''
    revert a b c d a' b' c' d'
    decide

theorem W_mul {yi : X} (hyi : yi ∈ S.data.R) (hyi2 : yi ^ 2 = 1) (a b c d a' b' c' d' : Fin 2) :
    S.W yi a b c d * S.W yi a' b' c' d' = S.W yi (a + a') (b + b') (c + c') (d + d') := by
  have hc : ∀ {p q : X}, p ∈ S.E yi → q ∈ S.E yi → p * q = q * p := fun hp hq =>
    S.E_comm hyi hp hq
  have hz : S.z ∈ S.E yi := subset_closure (by simp)
  have hy : yi ∈ S.E yi := subset_closure (by simp)
  have ht : S.t ∈ S.E yi := subset_closure (by simp)
  have hk : S.k ∈ S.E yi := subset_closure (by simp)
  have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
  rw [W, W, W, pow_fin_add hz2, pow_fin_add hyi2, pow_fin_add S.t_sq, pow_fin_add S.k_sq]
  set A := S.z ^ (a : ℕ)
  set B := yi ^ (b : ℕ)
  set Cc := S.t ^ (c : ℕ)
  set D := S.k ^ (d : ℕ)
  set A' := S.z ^ (a' : ℕ)
  set B' := yi ^ (b' : ℕ)
  set C' := S.t ^ (c' : ℕ)
  set D' := S.k ^ (d' : ℕ)
  have hA' : A' ∈ S.E yi := pow_mem hz _
  have hB : B ∈ S.E yi := pow_mem hy _
  have hB' : B' ∈ S.E yi := pow_mem hy _
  have hC : Cc ∈ S.E yi := pow_mem ht _
  have hC' : C' ∈ S.E yi := pow_mem ht _
  have hD : D ∈ S.E yi := pow_mem hk _
  calc A * B * Cc * D * (A' * B' * C' * D')
      = A * (B * Cc * D * A') * (B' * C' * D') := by group
    _ = A * (A' * (B * Cc * D)) * (B' * C' * D') := by
        rw [hc (mul_mem (mul_mem hB hC) hD) hA']
    _ = A * A' * B * (Cc * D * B') * (C' * D') := by group
    _ = A * A' * B * (B' * (Cc * D)) * (C' * D') := by
        rw [hc (mul_mem hC hD) hB']
    _ = A * A' * (B * B') * Cc * (D * C') * D' := by group
    _ = A * A' * (B * B') * Cc * (C' * D) * D' := by rw [hc hD hC']
    _ = A * A' * (B * B') * (Cc * C') * (D * D') := by group

theorem conjTo_W_xy (a c d : Fin 2) :
    ConjTo S.t (S.W (S.x * S.y) a 1 c d) ↔ ConjTo S.t (S.W (S.x * S.y) 1 0 c d) := by
  have hf : S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X) :=
    mul_mem (mem_sup_left (pow_mem (mem_zpowers _) _)) (mem_sup_right (pow_mem (mem_zpowers _) _))
  have h1 : S.W (S.x * S.y) 1 0 c d = S.z * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ)) := by
    simp [W, mul_assoc]
  rw [h1]
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
  · have h0 : S.W (S.x * S.y) 0 1 c d = S.x * S.y * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ)) := by
      simp [W, mul_assoc]
    rw [h0]
    exact (S.conjTo_xy_iff hf).1
  · have h0 : S.W (S.x * S.y) 1 1 c d = S.z * (S.x * S.y) * (S.t ^ (c : ℕ) * S.k ^ (d : ℕ)) := by
      simp [W, mul_assoc]
    rw [h0]
    exact (S.conjTo_xy_iff hf).2

theorem conjTo_W_y (a c d : Fin 2) :
    ConjTo S.t (S.W S.y a 1 c d) ↔ ConjTo S.t (S.W S.y (1 + d) 0 c d) := by
  have hmul := S.W_mul S.y_mem S.y_sq
  have hsplit : S.W S.y a 1 c d = S.W S.y (a + d) 1 0 0 * S.W S.y d 0 c d := by
    rw [hmul]
    have e1 : a + d + d = a := by
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
        rcases Fin.exists_fin_two.mp ⟨d, rfl⟩ with rfl | rfl <;> rfl
    rw [e1, add_zero, zero_add, zero_add]
  have hzf : S.W S.y (1 + d) 0 c d = S.z * S.W S.y d 0 c d := by
    rw [show S.z = S.W S.y 1 0 0 0 by simp [W], hmul, add_zero, zero_add, zero_add]
  have hf : S.W S.y d 0 c d = 1 ∨ S.W S.y d 0 c d = S.t ∨ S.W S.y d 0 c d = S.z * S.k ∨
      S.W S.y d 0 c d = S.t * (S.z * S.k) := by
    fin_cases c <;> fin_cases d
    · left; simp [W]
    · right; right; left; simp [W]
    · right; left; simp [W]
    · right; right; right
      simp only [W, Fin.isValue, pow_one, Fin.val_zero, pow_zero, mul_one]
      rw [← mul_assoc, S.z_comm_of_mem_T S.data.t_mem_T]
  rw [hsplit, hzf]
  have hr : S.W S.y (a + d) 1 0 0 = S.y ∨ S.W S.y (a + d) 1 0 0 = S.z * S.y := by
    rcases Fin.exists_fin_two.mp ⟨a + d, rfl⟩ with h | h <;> rw [h]
    · left; simp [W]
    · right; simp [W]
  rcases hr with hr | hr <;> rw [hr]
  · exact (S.conjTo_y_iff hf).1
  · exact (S.conjTo_y_iff hf).2

theorem W_mem_B (yi : X) (a c d : Fin 2) : S.W yi a 0 c d ∈ S.B := by
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  rw [W, Fin.val_zero, pow_zero, mul_one]
  exact mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem hkB _)

theorem conjTo_W_B_iff {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {p q r : Fin 2}
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W yi p 0 q r) (a c d : Fin 2) :
    ConjTo S.t (S.W yi a 0 c d) ↔ (a = 0 ∧ c = 1 ∧ d = 0) ∨ (a = p ∧ c = q ∧ d = r) := by
  rw [hO _ (S.W_mem_B yi a c d), show S.t = S.W yi 0 0 1 0 by simp [W]]
  constructor
  · rintro (h | h)
    · obtain ⟨h1, -, h3, h4⟩ := S.W_injective hyi h
      exact Or.inl ⟨h1, h3, h4⟩
    · obtain ⟨h1, -, h3, h4⟩ := S.W_injective hyi h
      exact Or.inr ⟨h1, h3, h4⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem conjTo_E_xy_iff {p q r : Fin 2}
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W (S.x * S.y) p 0 q r) (a b c d : Fin 2) :
    ConjTo S.t (S.W (S.x * S.y) a b c d) ↔
      (b = 0 ∧ ((a = 0 ∧ c = 1 ∧ d = 0) ∨ (a = p ∧ c = q ∧ d = r))) ∨
        (b = 1 ∧ ((1 = 0 ∧ c = 1 ∧ d = 0) ∨ (1 = p ∧ c = q ∧ d = r))) := by
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · rw [S.conjTo_W_B_iff (Or.inr rfl) hO]
    simp
  · rw [S.conjTo_W_xy, S.conjTo_W_B_iff (Or.inr rfl) hO]
    simp

theorem conjTo_E_y_iff {p q r : Fin 2}
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W S.y p 0 q r) (a b c d : Fin 2) :
    ConjTo S.t (S.W S.y a b c d) ↔
      (b = 0 ∧ ((a = 0 ∧ c = 1 ∧ d = 0) ∨ (a = p ∧ c = q ∧ d = r))) ∨
        (b = 1 ∧ ((1 + d = 0 ∧ c = 1 ∧ d = 0) ∨ (1 + d = p ∧ c = q ∧ d = r))) := by
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · rw [S.conjTo_W_B_iff (Or.inl rfl) hO]
    simp
  · rw [S.conjTo_W_y, S.conjTo_W_B_iff (Or.inl rfl) hO]
    simp

end A7Base

end CFSG.ComponentClassification.HSFLit
