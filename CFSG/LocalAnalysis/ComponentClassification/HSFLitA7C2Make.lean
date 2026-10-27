module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2h
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Words

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem t_eq_W (yi : X) : S.t = S.W yi 0 0 1 0 := by simp [W]

theorem z_eq_W (yi : X) : S.z = S.W yi 1 0 0 0 := by simp [W]

theorem W_B_eq (yi yi' : X) (a c d : Fin 2) : S.W yi a 0 c d = S.W yi' a 0 c d := by simp [W]

theorem W_not_mem_B {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) (a c d : Fin 2) :
    S.W yi a 1 c d ∉ S.B := by
  intro h
  have hc := S.coords_of_mem_B h
  rcases hyi with rfl | rfl
  · have e1 := S.coords_prod S.y_mem.1 S.coords_y a 1 c d (S.W_mem_T S.y_mem.1 a 1 c d)
    have : (S.coords ⟨S.W S.y a 1 c d, S.B_le_T h⟩).1 = (r 2) ^ (a : ℕ) * (sr 0) ^ 1 :=
      congrArg Prod.fst e1
    rw [this] at hc
    clear this e1 h
    revert hc
    revert a
    decide
  · have e1 := S.coords_prod S.xy_mem.1 S.coords_xy a 1 c d (S.W_mem_T S.xy_mem.1 a 1 c d)
    have : (S.coords ⟨S.W (S.x * S.y) a 1 c d, S.B_le_T h⟩).1 = (r 2) ^ (a : ℕ) * (sr 3) ^ 1 :=
      congrArg Prod.fst e1
    rw [this] at hc
    clear this e1 h
    revert hc
    revert a
    decide

theorem W_not_mem_tz (yi : X) (a c : Fin 2) :
    S.W yi a 0 c 1 ∉ (zpowers S.t ⊔ zpowers S.z : Subgroup X) := by
  intro h
  have hN : zpowers S.z ≤ normalizer (zpowers S.t : Set X) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (S.z_comm_of_mem_T S.data.t_mem_T).symm n)).eq
  have h' : S.W yi a 0 c 1 ∈ (zpowers S.t : Set X) * (zpowers S.z : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hN]
    exact h
  obtain ⟨g, hg, g', hg', hgg⟩ := h'
  have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
  have hfin : ∀ (c' a' : Fin 2), S.t ^ (c' : ℕ) * S.z ^ (a' : ℕ) = S.W S.y a' 0 c' 0 := by
    intro c' a'
    simp only [W, Fin.val_zero, pow_zero, mul_one]
    have hc : Commute S.t S.z := (S.z_comm_of_mem_T S.data.t_mem_T).symm
    exact (hc.pow_pow _ _).eq
  obtain ⟨c', rfl⟩ : ∃ c' : Fin 2, g = S.t ^ (c' : ℕ) := by
    rcases eq_one_or_eq_of_mem_zpowers S.t_sq hg with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  obtain ⟨a', rfl⟩ : ∃ a' : Fin 2, g' = S.z ^ (a' : ℕ) := by
    rcases eq_one_or_eq_of_mem_zpowers hz2 hg' with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  simp only at hgg
  rw [hfin, S.W_B_eq yi S.y] at hgg
  have := (S.W_injective (Or.inl rfl) hgg).2.2.2
  exact absurd this (by decide)

theorem W_eq_iff {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) (a b c d a' b' c' d' : Fin 2) :
    S.W yi a b c d = S.W yi a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · exact S.W_injective hyi
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem sectRank4_of_tc (hH : HaradaInput) {T₁ : Subgroup X} (hT₁p : IsPGroup 2 T₁)
    (hTT₁ : S.data.T ≤ T₁) (hT₁N : T₁ ≤ normalizer (S.data.T : Set X))
    (hcard : Nat.card T₁ = 2 * Nat.card S.data.T) (fc : Fin 2)
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W S.y 0 0 (1 + fc) 1) : SectRank4 X := by
  have hmul := S.W_mul S.y_mem S.y_sq
  have htf : S.t * S.W S.y 0 0 fc 1 = S.W S.y 0 0 (1 + fc) 1 := by
    rw [S.t_eq_W S.y, hmul]
    rfl
  have hzu : S.z * S.W S.y 1 1 (1 + fc) 1 = S.W S.y 0 1 (1 + fc) 1 := by
    rw [S.z_eq_W S.y, hmul]
    simp only [zero_add]
    rfl
  have hO' : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W (S.x * S.y) 0 0 (1 + fc) 1 := by
    intro b hb
    rw [hO b hb, S.W_B_eq S.y (S.x * S.y)]
  let C : S.Case2 :=
    { yb := S.y
      ys := S.x * S.y
      f := S.W S.y 0 0 fc 1
      u := S.W S.y 1 1 (1 + fc) 1
      hy := Or.inl ⟨rfl, rfl⟩
      f_mem := S.W_mem_B _ _ _ _
      f_not_mem := S.W_not_mem_tz _ _ _
      u_mem := S.W_mem_E _ _ _ _
      u_not_mem := S.W_not_mem_B (Or.inl rfl) _ _ _
      fusion := fun b hb => by rw [htf]; exact hO b hb
      omega_big := fun e he => by
        obtain ⟨a, b, c, d, rfl⟩ := S.eq_W (Or.inl rfl) he
        rw [S.conjTo_E_y_iff hO, htf, hzu, S.t_eq_W S.y, S.W_eq_iff (Or.inl rfl),
          S.W_eq_iff (Or.inl rfl), S.W_eq_iff (Or.inl rfl), S.W_eq_iff (Or.inl rfl)]
        clear he hO hO' htf hzu
        fin_cases fc <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
      omega_small := fun e he => by
        obtain ⟨a, b, c, d, rfl⟩ := S.eq_W (Or.inr rfl) he
        rw [S.conjTo_E_xy_iff hO', htf, S.W_B_eq S.y (S.x * S.y), S.t_eq_W (S.x * S.y),
          S.W_eq_iff (Or.inr rfl), S.W_eq_iff (Or.inr rfl)]
        clear he hO hO' htf hzu
        fin_cases fc <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
      T₁ := T₁
      T₁_p := hT₁p
      T_le := hTT₁
      T₁_le := hT₁N
      card_T₁ := hcard }
  exact C.sectRank4 hH

theorem sectRank4_of_tzc (hH : HaradaInput) {T₁ : Subgroup X} (hT₁p : IsPGroup 2 T₁)
    (hTT₁ : S.data.T ≤ T₁) (hT₁N : T₁ ≤ normalizer (S.data.T : Set X))
    (hcard : Nat.card T₁ = 2 * Nat.card S.data.T) (fc : Fin 2)
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W (S.x * S.y) 1 0 (1 + fc) 1) :
    SectRank4 X := by
  have hmul := S.W_mul S.xy_mem S.xy_sq
  have htf : S.t * S.W (S.x * S.y) 1 0 fc 1 = S.W (S.x * S.y) 1 0 (1 + fc) 1 := by
    rw [S.t_eq_W (S.x * S.y), hmul]
    rfl
  have hzu : S.z * S.W (S.x * S.y) 0 1 (1 + fc) 1 = S.W (S.x * S.y) 1 1 (1 + fc) 1 := by
    rw [S.z_eq_W (S.x * S.y), hmul]
    simp only [zero_add]
    rfl
  have hO' : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.W S.y 1 0 (1 + fc) 1 := by
    intro b hb
    rw [hO b hb, S.W_B_eq (S.x * S.y) S.y]
  let C : S.Case2 :=
    { yb := S.x * S.y
      ys := S.y
      f := S.W (S.x * S.y) 1 0 fc 1
      u := S.W (S.x * S.y) 0 1 (1 + fc) 1
      hy := Or.inr ⟨rfl, rfl⟩
      f_mem := S.W_mem_B _ _ _ _
      f_not_mem := S.W_not_mem_tz _ _ _
      u_mem := S.W_mem_E _ _ _ _
      u_not_mem := S.W_not_mem_B (Or.inr rfl) _ _ _
      fusion := fun b hb => by rw [htf]; exact hO b hb
      omega_big := fun e he => by
        obtain ⟨a, b, c, d, rfl⟩ := S.eq_W (Or.inr rfl) he
        rw [S.conjTo_E_xy_iff hO, htf, hzu, S.t_eq_W (S.x * S.y), S.W_eq_iff (Or.inr rfl),
          S.W_eq_iff (Or.inr rfl), S.W_eq_iff (Or.inr rfl), S.W_eq_iff (Or.inr rfl)]
        clear he hO hO' htf hzu
        fin_cases fc <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
      omega_small := fun e he => by
        obtain ⟨a, b, c, d, rfl⟩ := S.eq_W (Or.inl rfl) he
        rw [S.conjTo_E_y_iff hO', htf, S.W_B_eq (S.x * S.y) S.y, S.t_eq_W S.y,
          S.W_eq_iff (Or.inl rfl), S.W_eq_iff (Or.inl rfl)]
        clear he hO hO' htf hzu
        fin_cases fc <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
      T₁ := T₁
      T₁_p := hT₁p
      T_le := hTT₁
      T₁_le := hT₁N
      card_T₁ := hcard }
  exact C.sectRank4 hH

end A7Base

end CFSG.ComponentClassification.HSFLit
