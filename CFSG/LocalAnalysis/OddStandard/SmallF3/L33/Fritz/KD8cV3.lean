module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cV2

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace VSide

variable (V : VSide S T₁)

open Classical in
noncomputable def vN : X := if V.D.v ^ 2 = 1 then V.D.v else V.D.v * t

theorem vN_eq : V.vN = V.D.v ∨ V.vN = V.D.v * t := by
  unfold vN
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem vN_sq : V.vN ^ 2 = 1 := by
  unfold vN
  split_ifs with h
  · exact h
  · have hk : V.D.v ^ 2 = V.ki := V.v_sq_eq.resolve_left h
    have ht := V.v_conj_t
    calc (V.D.v * t) ^ 2 = (V.D.v * t * V.D.v⁻¹) * V.D.v ^ 2 * t := by
          rw [pow_two, pow_two]; group
      _ = 1 := by
        rw [ht, hk, mul_assoc t, V.ki_sq, mul_one, tt (A := A)]

theorem vN_mul_vN : V.vN * V.vN = 1 := by rw [← pow_two, V.vN_sq]

theorem vN_inv : V.vN⁻¹ = V.vN := by rw [inv_eq_iff_mul_eq_one, V.vN_mul_vN]

theorem vN_conj_T_of_conj {g : X} (hg : g ∈ A.T) :
    V.vN * g * V.vN⁻¹ = V.D.v * g * V.D.v⁻¹ := by
  unfold vN
  split_ifs
  · rfl
  · rw [show V.D.v * t * g * (V.D.v * t)⁻¹ = V.D.v * (t * g * t⁻¹) * V.D.v⁻¹ by group,
      ← A.commute_t hg, mul_inv_cancel_right]

theorem vN_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e * V.vN⁻¹ = e := by
  rw [V.vN_conj_T_of_conj (V.F.E0_le_T he), V.v_conj_E0 he]

theorem vN_conj_t : V.vN * t * V.vN⁻¹ = t * V.ki := by
  rw [V.vN_conj_T_of_conj A.t_mem_T, V.v_conj_t]

theorem vN_conj_z : V.vN * S.z * V.vN⁻¹ = S.z := V.vN_conj_E0 V.z_mem_E0

theorem vN_conj_yi : V.vN * V.yi * V.vN⁻¹ = V.yi := V.vN_conj_E0 V.yi_mem_E0

theorem vN_conj_ki : V.vN * V.ki * V.vN⁻¹ = V.ki := V.vN_conj_E0 V.ki_mem_E0

theorem vN_conj_x : V.vN * S.x * V.vN⁻¹ = V.ki * S.x := by
  rw [V.vN_conj_T_of_conj (x_mem_T S), V.v_conj_x]

theorem u_comm_vN : V.D.u * V.vN = V.vN * V.D.u := by
  unfold vN
  split_ifs
  · exact V.u_comm_v
  · rw [← mul_assoc, V.u_comm_v, mul_assoc, A.commute_t V.u_mem_T, mul_assoc]

theorem u_conj_vN : V.D.u * V.vN * V.D.u⁻¹ = V.vN := by
  rw [V.u_comm_vN, mul_inv_cancel_right]

theorem vN_mem_closure : V.vN ∈ closure ({t, V.ki, V.D.v} : Set X) := by
  unfold vN
  split_ifs
  · exact subset_closure (by simp)
  · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem vN_mem_C : V.vN ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ V.vN_mem_closure

theorem vN_mem_T₁ : V.vN ∈ T₁ := by
  unfold vN
  split_ifs
  · exact V.v_mem_T₁
  · exact mul_mem V.v_mem_T₁ V.t_mem_T₁

theorem vN_mem_S₁ : V.vN ∈ V.D.S₁ := by
  rcases V.vN_eq with h | h <;> rw [h]
  · exact V.v_mem_S₁
  · exact mul_mem V.v_mem_S₁ V.t_mem_S₁

theorem vN_conj_of_zk {b : X} (h : b ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.vN * b * V.vN⁻¹ = b := V.conj_zk_of_fix V.vN_conj_z V.vN_conj_ki h

theorem vN_conj_of_t {b : X} (h : b * t ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.vN * b * V.vN⁻¹ = b * V.ki := by
  have hb' : b = b * t * t := by rw [mul_assoc, tt (A := A), mul_one]
  calc V.vN * b * V.vN⁻¹ = (V.vN * (b * t) * V.vN⁻¹) * (V.vN * t * V.vN⁻¹) := by
        nth_rewrite 1 [hb']; group
    _ = (b * t) * (t * V.ki) := by rw [V.vN_conj_of_zk h, V.vN_conj_t]
    _ = b * (t * t) * V.ki := by group
    _ = b * V.ki := by rw [tt (A := A), mul_one]

theorem vN_conj_B {b : X} (hb : b ∈ S.B) :
    V.vN * b * V.vN⁻¹ = b ∨ V.vN * b * V.vN⁻¹ = b * V.ki := by
  rcases V.mem_B_cases hb with h | h
  · exact Or.inl (V.vN_conj_of_zk h)
  · exact Or.inr (V.vN_conj_of_t h)

theorem elemAbelianTwo_ki : ElemAbelianTwo (zpowers V.ki) := elemAbelianTwo_zpowers V.ki_sq'

theorem t_not_mem_ki : t ∉ zpowers V.ki := fun h => V.t_not_mem_zk (mem_sup_right h)

theorem t_comm_ki {a : X} (ha : a ∈ zpowers V.ki) : t * a = a * t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
  exact (Commute.zpow_right (B_comm_B S Frame.t_mem_B V.ki_mem_B) n).eq

theorem card_kt : Nat.card (zpowers V.ki ⊔ zpowers t : Subgroup X) = 4 := by
  rw [Sec7.card_sup_of_not_mem V.elemAbelianTwo_ki (SD.t_sq (A := A)) V.t_not_mem_ki
    (fun a ha => V.t_comm_ki ha), Nat.card_zpowers, orderOf_eq_prime V.ki_sq' V.ki_ne_one]

theorem eq_of_mem_ki {c : X} (hc : c ∈ zpowers V.ki) : c = 1 ∨ c = V.ki :=
  eq_one_or_eq_of_mem_zpowers V.ki_sq' hc

theorem mem_C {c : X} (hc : c ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X)) :
    c ∈ (zpowers V.ki ⊔ zpowers t : Subgroup X) ∨
      c * V.vN⁻¹ ∈ (zpowers V.ki ⊔ zpowers t : Subgroup X) := by
  have hN : V.vN ∈ normalizer ((zpowers V.ki ⊔ zpowers t : Subgroup X) : Set X) :=
    mem_normalizer_of_conj_gens (by rw [V.vN_conj_ki]; exact mem_sup_left (mem_zpowers _))
      (by rw [V.vN_conj_t]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _)))
  have hv2 : V.vN ^ 2 ∈ (zpowers V.ki ⊔ zpowers t : Subgroup X) := by
    rw [V.vN_sq]; exact one_mem _
  have hle : closure ({t, V.ki, V.D.v} : Set X) ≤
      (zpowers V.ki ⊔ zpowers t : Subgroup X) ⊔ zpowers V.vN := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_left (mem_sup_left (mem_zpowers _))
    · rcases V.vN_eq with h | h
      · rw [← h]; exact mem_sup_right (mem_zpowers _)
      · have : V.D.v = V.vN * t⁻¹ := by rw [h]; group
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers _))
          (mem_sup_left (mem_sup_right (inv_mem (mem_zpowers _))))
  exact Sec7.mem_or_of_mem_sup_zpowers hN hv2 (hle (V.D.C_eq ▸ hc))

theorem w₁_conj_t : V.D.w₁ * t * V.D.w₁⁻¹ = t * S.z * V.ki := V.act.2.2.1

theorem w₂_conj_t : V.D.w₂ * t * V.D.w₂⁻¹ = t * V.yi * V.ki := V.act.2.2.2.1

theorem w₁_conj_z : V.D.w₁ * S.z * V.D.w₁⁻¹ = S.z := V.act.2.2.2.2.1

theorem w₂_conj_yi : V.D.w₂ * V.yi * V.D.w₂⁻¹ = V.yi := V.act.2.2.2.2.2.1

theorem w₂_conj_z : V.D.w₂ * S.z * V.D.w₂⁻¹ = S.z * V.ki := V.act.2.2.2.2.2.2.1

theorem w₁_conj_yi : V.D.w₁ * V.yi * V.D.w₁⁻¹ = V.yi * V.ki := V.act.2.2.2.2.2.2.2.1

theorem w₁_conj_ki : V.D.w₁ * V.ki * V.D.w₁⁻¹ = V.ki := V.act.2.2.2.2.2.2.2.2.1

theorem w₂_conj_ki : V.D.w₂ * V.ki * V.D.w₂⁻¹ = V.ki := V.act.2.2.2.2.2.2.2.2.2

theorem w₁_sq : V.D.w₁ ^ 2 = 1 := by
  have h := V.D.q0_holds
  rw [V.hq] at h
  exact h.1

theorem w₂_sq : V.D.w₂ ^ 2 = 1 := by
  have h := V.D.q0_holds
  rw [V.hq] at h
  exact h.2.1

theorem w₁_mul : V.D.w₁ * V.D.w₁ = 1 := by rw [← pow_two, V.w₁_sq]

theorem w₂_mul : V.D.w₂ * V.D.w₂ = 1 := by rw [← pow_two, V.w₂_sq]

theorem w₁_inv : V.D.w₁⁻¹ = V.D.w₁ := by rw [inv_eq_iff_mul_eq_one, V.w₁_mul]

theorem w₂_inv : V.D.w₂⁻¹ = V.D.w₂ := by rw [inv_eq_iff_mul_eq_one, V.w₂_mul]

theorem w₁_conj_k : V.D.w₁ * S.k * V.D.w₁⁻¹ = S.k :=
  V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki V.k_mem_zk

theorem w₁_conj_B {b : X} (hb : b ∈ S.B) :
    V.D.w₁ * b * V.D.w₁⁻¹ = b ∨ V.D.w₁ * b * V.D.w₁⁻¹ = b * (S.z * V.ki) := by
  rcases V.mem_B_cases hb with h | h
  · exact Or.inl (V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h)
  · right
    have hb' : b = b * t * t := by rw [mul_assoc, tt (A := A), mul_one]
    calc V.D.w₁ * b * V.D.w₁⁻¹ =
        (V.D.w₁ * (b * t) * V.D.w₁⁻¹) * (V.D.w₁ * t * V.D.w₁⁻¹) := by
          nth_rewrite 1 [hb']; group
      _ = (b * t) * (t * S.z * V.ki) := by
          rw [V.conj_zk_of_fix V.w₁_conj_z V.w₁_conj_ki h, V.w₁_conj_t]
      _ = b * (t * t) * (S.z * V.ki) := by group
      _ = b * (S.z * V.ki) := by rw [tt (A := A), mul_one]

theorem act_eq : V.D.act = .two := by
  have h := V.D.act_holds
  cases hact : V.D.act
  · exfalso
    rw [hact] at h
    have h1 := h.2.2.1
    rw [V.w₁_conj_t] at h1
    exact V.ki_ne_one (mul_eq_left.mp h1)
  · rfl

theorem zki_sq : (S.z * V.ki) ^ 2 = 1 := sq_of_mem_B S (mul_mem Frame.z_mem_B V.ki_mem_B)

theorem w₁_comm_C {c : X} (hc : c ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X)) :
    V.D.w₁ * c * V.D.w₁⁻¹ * c⁻¹ = 1 ∨ V.D.w₁ * c * V.D.w₁⁻¹ * c⁻¹ = S.z * V.ki := by
  have h := V.D.w₁_comm_C c hc
  rw [V.act_eq] at h
  change _ ∈ closure {S.z * V.ki} at h
  rw [← zpowers_eq_closure] at h
  exact eq_one_or_eq_of_mem_zpowers V.zki_sq h

theorem w₁_mem_Q0 : V.D.w₁ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ :=
  mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q0 : V.D.w₂ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := mem_sup_right (mem_zpowers _)

end VSide

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
