module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abSide

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem mem_normalizer_of_conj_gens₂ {a b g : X} (ha : g * a * g⁻¹ ∈ zpowers a ⊔ zpowers b)
    (hb : g * b * g⁻¹ ∈ zpowers a ⊔ zpowers b) :
    g ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
  have hle : (zpowers a ⊔ zpowers b : Subgroup X).map (MulAut.conj g).toMonoidHom ≤
      zpowers a ⊔ zpowers b := by
    rw [map_le_iff_le_comap]
    exact sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  refine Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

namespace ISide

variable (V : ISide S T₁)

theorem v_sq_eq : V.D.v ^ 2 = 1 ∨ V.D.v ^ 2 = V.ki := by
  have hvC := (V.v_mem_C).2
  have hv2C : V.D.v ^ 2 ∈ centralizer (V.D.D₁₁ : Set X) := pow_mem hvC 2
  have hfix : ∀ g ∈ centralizer (V.D.D₁₁ : Set X), ∀ δ ∈ V.D.D₁₁, δ * g * δ⁻¹ = g := by
    intro g hg δ hδ
    rw [(mem_centralizer_iff.mp hg) δ hδ, mul_inv_cancel_right]
  rcases V.eq_of_mem_zk V.v_sq_mem_zk with h | h | h | h
  · exact Or.inl h
  · exfalso
    exact V.not_fix_z (fun δ hδ => h ▸ hfix _ hv2C δ hδ)
  · exact Or.inr h
  · exfalso
    apply V.not_fix_z
    intro δ hδ
    have h1 := hfix _ hv2C δ hδ
    rw [h] at h1
    have h2 : δ * V.ki * δ⁻¹ = V.ki := V.D.k_fixed δ (V.D₁₁_mem_normalizer hδ)
    calc δ * S.z * δ⁻¹ = (δ * (S.z * V.ki) * δ⁻¹) * (δ * V.ki * δ⁻¹)⁻¹ := by group
      _ = S.z := by rw [h1, h2, mul_inv_cancel_right]

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

theorem vN_conj_T_of_conj {g : X} (hg : g ∈ A.T) :
    V.vN * g * V.vN⁻¹ = V.D.v * g * V.D.v⁻¹ := by
  unfold vN
  split_ifs
  · rfl
  · rw [show V.D.v * t * g * (V.D.v * t)⁻¹ = V.D.v * (t * g * t⁻¹) * V.D.v⁻¹ by group,
      ← A.commute_t hg, mul_inv_cancel_right]

theorem vN_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e * V.vN⁻¹ = e := by
  rw [V.vN_conj_T_of_conj (V.F.E0_le_T he), V.v_conj_E0 he]

theorem vN_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.vN * e = e * V.vN := by
  have h := V.vN_conj_E0 he
  calc V.vN * e = V.vN * e * V.vN⁻¹ * V.vN := by group
    _ = e * V.vN := by rw [h]

theorem vN_conj_t : V.vN * t * V.vN⁻¹ = t * V.ki := by
  rw [V.vN_conj_T_of_conj A.t_mem_T, V.v_conj_t]

theorem vN_conj_z : V.vN * S.z * V.vN⁻¹ = S.z := V.vN_conj_E0 V.z_mem_E0

theorem vN_conj_yi : V.vN * V.yi * V.vN⁻¹ = V.yi := V.vN_conj_E0 V.yi_mem_E0

theorem vN_conj_ki : V.vN * V.ki * V.vN⁻¹ = V.ki := V.vN_conj_E0 V.ki_mem_E0

theorem u_comm_v : V.D.u * V.D.v = V.D.v * V.D.u :=
  V.D.u_comm_C V.D.v (V.D.C_eq ▸ subset_closure (by simp))

theorem u_comm_vN : V.D.u * V.vN = V.vN * V.D.u := by
  unfold vN
  split_ifs
  · exact V.u_comm_v
  · rw [← mul_assoc, V.u_comm_v, mul_assoc, A.commute_t V.u_mem_T, mul_assoc]

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

theorem t_mem_S₁ : t ∈ V.D.S₁ := by
  rw [V.D.S₁_eq]
  exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (Frame.t_mem_E _))))

theorem vN_mem_S₁ : V.vN ∈ V.D.S₁ := by
  rcases V.vN_eq with h | h <;> rw [h]
  · exact V.v_mem_S₁
  · exact mul_mem V.v_mem_S₁ V.t_mem_S₁

theorem mem_C {c : X} (hc : c ∈ closure ({t, V.ki, V.D.v} : Set X)) :
    c ∈ (zpowers V.ki ⊔ zpowers t : Subgroup X) ∨
      c * V.vN⁻¹ ∈ (zpowers V.ki ⊔ zpowers t : Subgroup X) := by
  have hN : V.vN ∈ normalizer ((zpowers V.ki ⊔ zpowers t : Subgroup X) : Set X) :=
    mem_normalizer_of_conj_gens₂ (by rw [V.vN_conj_ki]; exact mem_sup_left (mem_zpowers _))
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
  exact Sec7.mem_or_of_mem_sup_zpowers hN hv2 (hle hc)

theorem w₁_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.w₁ * e * V.D.w₁⁻¹ = e :=
  (V.act.1 e he).2.1

theorem w₂_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.w₂ * e * V.D.w₂⁻¹ = e :=
  (V.act.1 e he).2.2

theorem w₁_conj_t : V.D.w₁ * t * V.D.w₁⁻¹ = t * S.z := V.act.2.2.1

theorem w₂_conj_t : V.D.w₂ * t * V.D.w₂⁻¹ = t * V.yi := V.act.2.2.2

theorem w₁_mem_Q0 : V.D.w₁ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ :=
  mem_sup_left (mem_sup_right (mem_zpowers _))

theorem w₂_mem_Q0 : V.D.w₂ ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := mem_sup_right (mem_zpowers _)

theorem Q0_comm {a b : X} (ha : a ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂)
    (hb : b ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂) : a * b = b * a := by
  have h := V.D.q0_holds
  rcases V.hq with hq | hq <;> rw [hq] at h
  · exact h.1 a ha b hb
  · exact h.2.2.1 a ha b hb

theorem E0_le_Q0 : S.E0 V.yi V.ki ≤ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := le_sup_left.trans le_sup_left

theorem w₁_sq_of_elem (h : V.D.q0 = .elem) : V.D.w₁ ^ 2 = 1 := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1 _ V.w₁_mem_Q0

theorem w₂_sq_of_elem (h : V.D.q0 = .elem) : V.D.w₂ ^ 2 = 1 := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1 _ V.w₂_mem_Q0

theorem w₁_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.D.w₁ ^ 2 = S.z := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.1

theorem w₂_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.D.w₂ ^ 2 = V.yi := by
  have hq := V.D.q0_holds
  rw [h] at hq
  exact hq.2.1

theorem w₁_sq_mem : V.D.w₁ ^ 2 ∈ S.E0 V.yi V.ki := by
  rcases V.hq with h | h
  · rw [V.w₁_sq_of_elem h]; exact one_mem _
  · rw [V.w₁_sq_of_homoc h]; exact V.z_mem_E0

theorem w₁_mem_normalizer_E0 : V.D.w₁ ∈ normalizer (S.E0 V.yi V.ki : Set X) := by
  rw [mem_normalizer_iff]
  intro e
  refine ⟨fun he => by rw [V.w₁_conj_E0 he]; exact he, fun he => ?_⟩
  have h1 := V.w₁_conj_E0 he
  have : e = V.D.w₁ * e * V.D.w₁⁻¹ := by
    calc e = V.D.w₁⁻¹ * (V.D.w₁ * e * V.D.w₁⁻¹) * V.D.w₁ := by group
      _ = V.D.w₁⁻¹ * (V.D.w₁ * (V.D.w₁ * e * V.D.w₁⁻¹) * V.D.w₁⁻¹) * V.D.w₁ := by rw [h1]
      _ = V.D.w₁ * e * V.D.w₁⁻¹ := by group
  rw [this]; exact he

@[expose] noncomputable def w₁N : X := V.D.u⁻¹ * V.D.w₂ * V.D.u * V.D.w₂⁻¹

theorem w₁N_def : V.w₁N = V.D.u⁻¹ * V.D.w₂ * V.D.u * V.D.w₂⁻¹ := rfl

theorem w₂_conj_u : V.D.w₂ * V.D.u * V.D.w₂⁻¹ = V.D.u * V.w₁N := by rw [w₁N_def]; group

theorem w₂_inv_conj_t : V.D.w₂⁻¹ * t * V.D.w₂ = t * V.yi := by
  have h1 := V.w₂_conj_t
  have h2 := V.w₂_conj_E0 V.yi_mem_E0
  calc V.D.w₂⁻¹ * t * V.D.w₂ = V.D.w₂⁻¹ * (t * V.yi * V.yi) * V.D.w₂ := by
        rw [mul_assoc t, V.yi_sq, mul_one]
    _ = V.D.w₂⁻¹ * ((V.D.w₂ * t * V.D.w₂⁻¹) * (V.D.w₂ * V.yi * V.D.w₂⁻¹)) * V.D.w₂ := by
        rw [h1, h2]
    _ = t * V.yi := by group

theorem w₁N_eq : ∃ e ∈ S.E0 V.yi V.ki, V.w₁N = V.D.w₁ * e := by
  have hc : V.w₁N ∈ S.E0 V.yi V.ki ⊔ zpowers V.D.w₁ := by
    have := V.D.S₁_commutator_mem _ (inv_mem V.u_mem_S₁) _ V.w₂_mem_S₁
    rwa [inv_inv] at this
  rcases Sec7.mem_or_of_mem_sup_zpowers V.w₁_mem_normalizer_E0 V.w₁_sq_mem hc with h | h
  · exfalso
    have h1 : (V.D.w₂ * V.D.u * V.D.w₂⁻¹) * t * (V.D.w₂ * V.D.u * V.D.w₂⁻¹)⁻¹ = t * S.z := by
      calc (V.D.w₂ * V.D.u * V.D.w₂⁻¹) * t * (V.D.w₂ * V.D.u * V.D.w₂⁻¹)⁻¹ =
          V.D.w₂ * (V.D.u * (V.D.w₂⁻¹ * t * V.D.w₂) * V.D.u⁻¹) * V.D.w₂⁻¹ := by group
        _ = V.D.w₂ * ((V.D.u * t * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹)) * V.D.w₂⁻¹ := by
          rw [V.w₂_inv_conj_t]; group
        _ = (V.D.w₂ * t * V.D.w₂⁻¹) * (V.D.w₂ * S.z * V.D.w₂⁻¹) *
            (V.D.w₂ * V.yi * V.D.w₂⁻¹) := by rw [V.u_conj_t, V.u_conj_yi]; group
        _ = t * V.yi * S.z * V.yi := by
          rw [V.w₂_conj_t, V.w₂_conj_E0 V.z_mem_E0, V.w₂_conj_E0 V.yi_mem_E0]
        _ = t * S.z := by
          rw [mul_assoc t, V.E0_comm V.yi_mem_E0 V.z_mem_E0, mul_assoc, mul_assoc, V.yi_sq,
            mul_one]
    have h2 : (V.D.u * V.w₁N) * t * (V.D.u * V.w₁N)⁻¹ = t := by
      have hct : V.w₁N * t * V.w₁N⁻¹ = t := by
        rw [← V.t_comm_E0 h, mul_inv_cancel_right]
      calc (V.D.u * V.w₁N) * t * (V.D.u * V.w₁N)⁻¹ =
          V.D.u * (V.w₁N * t * V.w₁N⁻¹) * V.D.u⁻¹ := by group
        _ = t := by rw [hct, V.u_conj_t]
    rw [V.w₂_conj_u, h2] at h1
    exact z_ne_one S (mul_eq_left.mp h1.symm)
  · refine ⟨V.D.w₁⁻¹ * V.w₁N, ?_, by group⟩
    have := Sec7.conj_mem_of_mem_normalizer (inv_mem V.w₁_mem_normalizer_E0) h
    rwa [show V.D.w₁⁻¹ * (V.w₁N * V.D.w₁⁻¹) * V.D.w₁⁻¹⁻¹ = V.D.w₁⁻¹ * V.w₁N by group] at this

theorem w₁N_conj_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.w₁N * e * V.w₁N⁻¹ = e := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw, show V.D.w₁ * c * e * (V.D.w₁ * c)⁻¹ = V.D.w₁ * (c * e * c⁻¹) * V.D.w₁⁻¹ by group,
    Sec7.conj_eq_of_comm (V.E0_comm hc he), V.w₁_conj_E0 he]

theorem w₁N_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.w₁N * e = e * V.w₁N := by
  have h := V.w₁N_conj_E0 he
  calc V.w₁N * e = V.w₁N * e * V.w₁N⁻¹ * V.w₁N := by group
    _ = e * V.w₁N := by rw [h]

theorem w₁N_conj_t : V.w₁N * t * V.w₁N⁻¹ = t * S.z := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw, show V.D.w₁ * c * t * (V.D.w₁ * c)⁻¹ = V.D.w₁ * (c * t * c⁻¹) * V.D.w₁⁻¹ by group,
    ← V.t_comm_E0 hc, mul_inv_cancel_right, V.w₁_conj_t]

theorem w₁N_mem_Q0 : V.w₁N ∈ S.Q0 V.yi V.ki V.D.w₁ V.D.w₂ := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw]; exact mul_mem V.w₁_mem_Q0 (V.E0_le_Q0 hc)

theorem w₂_comm_w₁N : V.D.w₂ * V.w₁N = V.w₁N * V.D.w₂ := V.Q0_comm V.w₂_mem_Q0 V.w₁N_mem_Q0

theorem w₁N_sq_eq : V.w₁N ^ 2 = V.D.w₁ ^ 2 := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  have hcw : V.D.w₁ * c = c * V.D.w₁ := V.Q0_comm V.w₁_mem_Q0 (V.E0_le_Q0 hc)
  have hc2 : c * c = 1 := by
    rw [← pow_two]; exact V.F.elemAbelianTwo_E0.sq_eq_one c hc
  rw [hw, pow_two, pow_two, show V.D.w₁ * c * (V.D.w₁ * c) = V.D.w₁ * (c * V.D.w₁) * c by group,
    ← hcw, show V.D.w₁ * (V.D.w₁ * c) * c = V.D.w₁ * V.D.w₁ * (c * c) by group, hc2, mul_one]

theorem w₁N_sq_of_elem (h : V.D.q0 = .elem) : V.w₁N ^ 2 = 1 := by
  rw [V.w₁N_sq_eq, V.w₁_sq_of_elem h]

theorem w₁N_sq_of_homoc (h : V.D.q0 = .homocyclic) : V.w₁N ^ 2 = S.z := by
  rw [V.w₁N_sq_eq, V.w₁_sq_of_homoc h]

theorem u_conj_w₁N : V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N⁻¹ := by
  have h1 : (V.D.u * V.w₁N) * (V.D.u * V.w₁N) = 1 := by
    rw [← V.w₂_conj_u, show V.D.w₂ * V.D.u * V.D.w₂⁻¹ * (V.D.w₂ * V.D.u * V.D.w₂⁻¹) =
      V.D.w₂ * (V.D.u * V.D.u) * V.D.w₂⁻¹ by group, V.u_sq, mul_one, mul_inv_cancel]
  rw [V.u_inv]
  calc V.D.u * V.w₁N * V.D.u = (V.D.u * V.w₁N) * (V.D.u * V.w₁N) * V.w₁N⁻¹ := by group
    _ = V.w₁N⁻¹ := by rw [h1, one_mul]

theorem u_conj_w₁N_of_elem (h : V.D.q0 = .elem) : V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N := by
  rw [V.u_conj_w₁N, inv_eq_iff_mul_eq_one, ← pow_two, V.w₁N_sq_of_elem h]

theorem u_conj_w₁N_of_homoc (h : V.D.q0 = .homocyclic) :
    V.D.u * V.w₁N * V.D.u⁻¹ = V.w₁N * S.z := by
  rw [V.u_conj_w₁N, inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, V.w₁N_sq_of_homoc h, zz S]

theorem w₁N_mem_T₁ : V.w₁N ∈ T₁ := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  rw [hw]
  exact mul_mem V.w₁_mem_T₁ (V.T_le_T₁ (V.F.E0_le_T hc))

theorem w₁N_mem_S₁ : V.w₁N ∈ V.D.S₁ := by
  rw [w₁N_def]
  exact mul_mem (mul_mem (mul_mem (inv_mem V.u_mem_S₁) V.w₂_mem_S₁) V.u_mem_S₁)
    (inv_mem V.w₂_mem_S₁)

theorem w₁_eq : ∃ c ∈ S.E0 V.yi V.ki, V.D.w₁ = V.w₁N * c := by
  obtain ⟨c, hc, hw⟩ := V.w₁N_eq
  exact ⟨c⁻¹, inv_mem hc, by rw [hw]; group⟩

end ISide

end KD8ab

end CFSG.ComponentClassification.HSFLit
