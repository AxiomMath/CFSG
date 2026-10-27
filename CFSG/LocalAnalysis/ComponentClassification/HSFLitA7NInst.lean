module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2Make

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

@[expose] def Fus : Prop :=
  ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z ∨ b = S.t * S.k ∨ b = S.t * S.z * S.k

theorem conjTo_W_iff (hO : S.Fus) {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) (a b c d : Fin 2) :
    ConjTo S.t (S.W yi a b c d) ↔ c = 1 := by
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hB : ∀ a' c' d' : Fin 2, ConjTo S.t (S.W yi a' 0 c' d') ↔ c' = 1 := by
    intro a' c' d'
    rw [hO _ (S.W_mem_B yi a' c' d')]
    have e1 : S.t = S.W yi 0 0 1 0 := by simp [W]
    have e2 : S.t * S.z = S.W yi 1 0 1 0 := by simp [W, hzt]
    have e3 : S.t * S.k = S.W yi 0 0 1 1 := by simp [W]
    have e4 : S.t * S.z * S.k = S.W yi 1 0 1 1 := by simp [W, hzt]
    rw [e4, e2, e3, e1, S.W_eq_iff hyi, S.W_eq_iff hyi, S.W_eq_iff hyi, S.W_eq_iff hyi]
    clear e1 e2 e3 e4
    revert a' c' d'
    decide
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · exact hB a c d
  · rcases hyi with rfl | rfl
    · rw [S.conjTo_W_y, hB]
    · rw [S.conjTo_W_xy, hB]

structure Inst where
  yi : X
  ki : X
  ui : X
  spec : (yi = S.x * S.y ∧ ki = S.k ∧ ui = S.y) ∨
    (yi = S.y ∧ ki = S.z * S.k ∧ ui = S.z * (S.x * S.y))

@[expose] noncomputable def inst₁ : S.Inst := ⟨S.x * S.y, S.k, S.y, Or.inl ⟨rfl, rfl, rfl⟩⟩

@[expose] noncomputable def inst₂ : S.Inst :=
  ⟨S.y, S.z * S.k, S.z * (S.x * S.y), Or.inr ⟨rfl, rfl, rfl⟩⟩

namespace Inst

variable {S} (I : S.Inst)

theorem yi_or : I.yi = S.y ∨ I.yi = S.x * S.y := by
  rcases I.spec with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inr h
  · exact Or.inl h

theorem yi_mem : I.yi ∈ S.data.R := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact S.y_mem
  · exact S.xy_mem

theorem yi_sq : I.yi ^ 2 = 1 := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact S.y_sq
  · exact S.xy_sq

theorem yi_not_mem_B : I.yi ∉ S.B := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact S.y_not_mem_B
  · exact S.xy_not_mem_B

@[expose] noncomputable def E : Subgroup X := S.E I.yi

theorem z_mem_E : S.z ∈ I.E := subset_closure (by simp)

theorem yi_mem_E : I.yi ∈ I.E := subset_closure (by simp)

theorem t_mem_E : S.t ∈ I.E := subset_closure (by simp)

theorem k_mem_E : S.k ∈ I.E := subset_closure (by simp)

theorem ki_eq : I.ki = S.k ∨ I.ki = S.z * S.k := by
  rcases I.spec with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem ki_mem_E : I.ki ∈ I.E := by
  rcases I.ki_eq with h | h <;> rw [h]
  · exact I.k_mem_E
  · exact mul_mem I.z_mem_E I.k_mem_E

theorem ki_mem_B : I.ki ∈ S.B := by
  have hz : S.z ∈ S.B := subset_closure (by simp)
  have hk : S.k ∈ S.B := subset_closure (by simp)
  rcases I.ki_eq with h | h <;> rw [h]
  · exact hk
  · exact mul_mem hz hk

theorem E_le_T : I.E ≤ S.data.T := S.E_le_T I.yi_mem

theorem comm {a b : X} (ha : a ∈ I.E) (hb : b ∈ I.E) : a * b = b * a := S.E_comm I.yi_mem ha hb

theorem sq_eq_one {a : X} (ha : a ∈ I.E) : a ^ 2 = 1 := S.E_sq I.yi_mem I.yi_sq ha

theorem ki_sq : I.ki ^ 2 = 1 := I.sq_eq_one I.ki_mem_E

@[expose] noncomputable def wV (v : V4) : X :=
  S.z ^ (v.1 : ℕ) * I.yi ^ (v.2.1 : ℕ) * S.t ^ (v.2.2.1 : ℕ) * I.ki ^ (v.2.2.2 : ℕ)

theorem wV_mem (v : V4) : I.wV v ∈ I.E :=
  mul_mem (mul_mem (mul_mem (pow_mem I.z_mem_E _) (pow_mem I.yi_mem_E _)) (pow_mem I.t_mem_E _))
    (pow_mem I.ki_mem_E _)

theorem wV_add (v w : V4) : I.wV (addV v w) = I.wV v * I.wV w := by
  have hc : ∀ {p q : X}, p ∈ I.E → q ∈ I.E → p * q = q * p := fun hp hq => I.comm hp hq
  have hz := I.z_mem_E
  have hy := I.yi_mem_E
  have ht := I.t_mem_E
  have hk := I.ki_mem_E
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [wV, addV]
  rw [pow_fin_add S.z_sq, pow_fin_add I.yi_sq, pow_fin_add S.t_sq, pow_fin_add I.ki_sq]
  set A := S.z ^ (a : ℕ)
  set B := I.yi ^ (b : ℕ)
  set Cc := S.t ^ (c : ℕ)
  set D := I.ki ^ (d : ℕ)
  set A' := S.z ^ (a' : ℕ)
  set B' := I.yi ^ (b' : ℕ)
  set C' := S.t ^ (c' : ℕ)
  set D' := I.ki ^ (d' : ℕ)
  have hA' : A' ∈ I.E := pow_mem hz _
  have hB : B ∈ I.E := pow_mem hy _
  have hB' : B' ∈ I.E := pow_mem hy _
  have hC : Cc ∈ I.E := pow_mem ht _
  have hC' : C' ∈ I.E := pow_mem ht _
  have hD : D ∈ I.E := pow_mem hk _
  symm
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

theorem wV_zero : I.wV (0, 0, 0, 0) = 1 := by simp [wV]

theorem wV_eq_W (v : V4) : ∃ a : Fin 2, I.wV v = S.W I.yi a v.2.1 v.2.2.1 v.2.2.2 ∧
    (I.ki = S.k → a = v.1) ∧ (I.ki = S.z * S.k → a = v.1 + v.2.2.2) := by
  obtain ⟨a, b, c, d⟩ := v
  have hzk : ∀ {g : X}, g ∈ S.data.T → S.z * g = g * S.z := fun hg => S.z_comm_of_mem_T hg
  rcases I.ki_eq with h | h
  · refine ⟨a, ?_, fun _ => rfl, fun h' => ?_⟩
    · simp [wV, W, h]
    · exfalso
      rw [h] at h'
      apply S.z_ne_one
      have := mul_right_cancel (h'.symm.trans (one_mul S.k).symm)
      exact this
  · refine ⟨a + d, ?_, fun h' => ?_, fun _ => rfl⟩
    · simp only [wV, W, h]
      have hzT := S.z_mem.1
      have hcomm : ∀ (e : ℕ), (S.z * S.k) ^ e = S.z ^ e * S.k ^ e := fun e =>
        (Commute.mul_pow (S.central_of_mem_B (subset_closure (by simp)) S.k_mem) e)
      rw [hcomm, pow_fin_add S.z_sq]
      have h1 : S.z ^ (d : ℕ) * (I.yi ^ (b : ℕ) * S.t ^ (c : ℕ)) =
          I.yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.z ^ (d : ℕ) :=
        (Commute.pow_left (hzk (mul_mem (pow_mem I.yi_mem.1 _) (pow_mem S.data.t_mem_T _)))
          _).eq
      calc S.z ^ (a : ℕ) * I.yi ^ (b : ℕ) * S.t ^ (c : ℕ) * (S.z ^ (d : ℕ) * S.k ^ (d : ℕ))
          = S.z ^ (a : ℕ) * (I.yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.z ^ (d : ℕ)) * S.k ^ (d : ℕ) := by
            group
        _ = S.z ^ (a : ℕ) * (S.z ^ (d : ℕ) * (I.yi ^ (b : ℕ) * S.t ^ (c : ℕ))) *
            S.k ^ (d : ℕ) := by rw [h1]
        _ = _ := by group
    · exfalso
      rw [h] at h'
      apply S.z_ne_one
      exact mul_right_cancel (h'.trans (one_mul S.k).symm)

theorem eq_wV {e : X} (he : e ∈ I.E) : ∃ v : V4, e = I.wV v := by
  obtain ⟨a, b, c, d, rfl⟩ := S.eq_W I.yi_or he
  rcases I.ki_eq with h | h
  · refine ⟨(a, b, c, d), ?_⟩
    obtain ⟨a', h1, h2, -⟩ := I.wV_eq_W (a, b, c, d)
    have h2' : a' = a := h2 h
    rw [h1, h2']
  · refine ⟨(a + d, b, c, d), ?_⟩
    obtain ⟨a', h1, -, h3⟩ := I.wV_eq_W (a + d, b, c, d)
    have h3' : a' = a + d + d := h3 h
    have h4 : a + d + d = a := by
      rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
        rcases Fin.exists_fin_two.mp ⟨d, rfl⟩ with rfl | rfl <;> rfl
    rw [h1, h3', h4]

theorem wV_injective {v w : V4} (h : I.wV v = I.wV w) : v = w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  obtain ⟨p, hp, hp1, hp2⟩ := I.wV_eq_W (a, b, c, d)
  obtain ⟨q, hq, hq1, hq2⟩ := I.wV_eq_W (a', b', c', d')
  rw [hp, hq] at h
  obtain ⟨hpq, hb, hc, hd⟩ := S.W_injective I.yi_or h
  simp only at hb hc hd
  subst hb hc hd
  rcases I.ki_eq with hk | hk
  · have e1 : p = a := hp1 hk
    have e2 : q = a' := hq1 hk
    rw [← e1, ← e2, hpq]
  · have e1 : p = a + d := hp2 hk
    have e2 : q = a' + d := hq2 hk
    have : a = a' := by
      have h3 : a + d = a' + d := e1.symm.trans (hpq.trans e2)
      simpa using h3
    rw [this]

theorem conjTo_wV_iff (hO : S.Fus) (v : V4) : ConjTo S.t (I.wV v) ↔ v.2.2.1 = 1 := by
  obtain ⟨a, h, -, -⟩ := I.wV_eq_W v
  rw [h, S.conjTo_W_iff hO I.yi_or]

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
