module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cV

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem mem_normalizer_of_conj_gens {a b g : X} (ha : g * a * g⁻¹ ∈ zpowers a ⊔ zpowers b)
    (hb : g * b * g⁻¹ ∈ zpowers a ⊔ zpowers b) :
    g ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
  have hle : (zpowers a ⊔ zpowers b : Subgroup X).map (MulAut.conj g).toMonoidHom ≤
      zpowers a ⊔ zpowers b := by
    rw [map_le_iff_le_comap]
    exact sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  refine Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_map_of_injective (MulAut.conj g).injective]

namespace VSide

variable (V : VSide S T₁)

theorem v_comm_E0 {e : X} (he : e ∈ S.E0 V.yi V.ki) : V.D.v * e = e * V.D.v := by
  have h := V.v_conj_E0 he
  calc V.D.v * e = V.D.v * e * V.D.v⁻¹ * V.D.v := by group
    _ = e * V.D.v := by rw [h]

theorem v_sq_comm_t : V.D.v ^ 2 * t = t * V.D.v ^ 2 := by
  have h1 := V.v_conj_t
  have h2 : V.D.v * t = t * V.ki * V.D.v := by rw [← h1]; group
  have h3 : V.D.v * V.ki = V.ki * V.D.v := V.v_comm_E0 V.ki_mem_E0
  calc V.D.v ^ 2 * t = V.D.v * (V.D.v * t) := by rw [pow_two, mul_assoc]
    _ = V.D.v * (t * V.ki * V.D.v) := by rw [h2]
    _ = (V.D.v * t) * (V.ki * V.D.v) := by group
    _ = (t * V.ki * V.D.v) * (V.ki * V.D.v) := by rw [h2]
    _ = t * V.ki * (V.D.v * V.ki) * V.D.v := by group
    _ = t * V.ki * (V.ki * V.D.v) * V.D.v := by rw [h3]
    _ = t * (V.ki * V.ki) * (V.D.v * V.D.v) := by group
    _ = t * V.D.v ^ 2 := by rw [V.ki_sq, pow_two, mul_one]

theorem v_sq_comm_yi : V.D.v ^ 2 * V.yi = V.yi * V.D.v ^ 2 := by
  have h := V.v_comm_E0 V.yi_mem_E0
  rw [pow_two, mul_assoc, h, ← mul_assoc, h, mul_assoc]

theorem v_sq_mem_E : V.D.v ^ 2 ∈ S.E V.yi :=
  mem_E_of_mem_T₁ S V.h4 V.hyi (pow_mem V.v_mem_T₁ 2) V.v_sq_comm_t V.v_sq_comm_yi

theorem v_sq_comm_u : V.D.v ^ 2 * V.D.u = V.D.u * V.D.v ^ 2 := by
  rw [pow_two, mul_assoc, ← V.u_comm_v, ← mul_assoc, ← V.u_comm_v, mul_assoc]

theorem v_sq_mem_zk : V.D.v ^ 2 ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) := by
  have h0 : V.D.v ^ 2 ∈ S.E0 V.yi V.ki :=
    V.mem_E0_of_comm_v V.v_sq_mem_E (by rw [pow_two]; group)
  have h0' : V.D.v ^ 2 ∈ S.E0 V.F.yF V.F.kF := h0
  rw [V.F.E0_eq'] at h0'
  rcases Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk V.F.yF_sq
    (fun _ hb => V.F.yF_comm_zk hb) h0' with h | h
  · exact h
  · exfalso
    set c := V.D.v ^ 2 * V.yi with hc
    have hv2 : V.D.v ^ 2 = c * V.yi := by
      rw [hc, mul_assoc, V.yi_sq, mul_one]
    have hcB : c ∈ S.B := V.zk_le_B h
    have h1 := V.v_sq_comm_u
    rw [hv2] at h1
    have h2 : V.D.u * (c * V.yi) * V.D.u⁻¹ = c * V.yi := by rw [← h1, mul_inv_cancel_right]
    rw [show V.D.u * (c * V.yi) * V.D.u⁻¹ = (V.D.u * c * V.D.u⁻¹) * (V.D.u * V.yi * V.D.u⁻¹) by
      group, V.u_conj_B hcB, V.u_conj_yi] at h2
    exact z_ne_one S (mul_eq_right.mp (mul_left_cancel h2))

theorem D₁₁_mem_normalizer {δ : X} (hδ : δ ∈ V.D.D₁₁) :
    δ ∈ normalizer (S.E V.yi : Set X) := (V.D.D₁₁_le hδ).1.1

theorem fix_yi_of_fix_z (hz : ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z) :
    ∀ δ ∈ V.D.D₁₁, δ * V.yi * δ⁻¹ = V.yi := by
  intro δ hδ
  have hN := V.D₁₁_mem_normalizer hδ
  have hk : δ * V.ki * δ⁻¹ = V.ki := V.D.k_fixed δ hN
  have hzδ := hz δ hδ
  have hmem := V.conj_mem_E0 hN V.yi_mem_E0
  have hmem' : δ * V.yi * δ⁻¹ ∈ S.E0 V.F.yF V.F.kF := hmem
  rw [V.F.E0_eq'] at hmem'
  rcases Sec7.mem_or_of_mem_sup V.F.elemAbelianTwo_zk V.F.yF_sq
    (fun _ hb => V.F.yF_comm_zk hb) hmem' with h | h
  · exfalso
    apply V.F.yF_not_mem_zk
    have hfix := V.conj_zk_of_fix hzδ hk h
    have : V.yi = δ * V.yi * δ⁻¹ := by
      calc V.yi = δ⁻¹ * (δ * V.yi * δ⁻¹) * δ := by group
        _ = δ⁻¹ * (δ * (δ * V.yi * δ⁻¹) * δ⁻¹) * δ := by rw [hfix]
        _ = δ * V.yi * δ⁻¹ := by group
    rw [show V.F.yF = V.yi from rfl, this]
    exact h
  · change δ * V.yi * δ⁻¹ * V.yi ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X) at h
    set c := δ * V.yi * δ⁻¹ * V.yi with hc
    have hcfix := V.conj_zk_of_fix hzδ hk h
    have hdy : δ * V.yi * δ⁻¹ = c * V.yi := by
      rw [hc, mul_assoc _ V.yi V.yi, V.yi_sq, mul_one]
    clear_value c
    have hpow : ∀ n : ℕ, δ ^ n * V.yi * (δ ^ n)⁻¹ = c ^ n * V.yi := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hcn : δ * c ^ n * δ⁻¹ = c ^ n := by
          rw [show δ * c ^ n * δ⁻¹ = (δ * c * δ⁻¹) ^ n by rw [conj_pow], hcfix]
        calc δ ^ (n + 1) * V.yi * (δ ^ (n + 1))⁻¹ = δ * (δ ^ n * V.yi * (δ ^ n)⁻¹) * δ⁻¹ := by
              rw [pow_succ']; group
          _ = (δ * c ^ n * δ⁻¹) * (δ * V.yi * δ⁻¹) := by rw [ih]; group
          _ = c ^ (n + 1) * V.yi := by rw [hcn, hdy, pow_succ, mul_assoc]
    obtain ⟨m, hm⟩ := V.D.isPGroup_D₁₁ ⟨δ, hδ⟩
    have hm' : δ ^ 3 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hc2 : c ^ 2 = 1 := sq_of_mem_B S (V.zk_le_B h)
    have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have hc1 : c ^ 3 ^ m = c := by
      rw [hj, pow_succ, pow_mul, hc2, one_pow, one_mul]
    have h1 := hpow (3 ^ m)
    rw [hm', hc1, one_mul, inv_one, mul_one] at h1
    have hc0 : c = 1 := mul_eq_right.mp h1.symm
    rw [hdy, hc0, one_mul]

theorem v_mem_C : V.D.v ∈ V.D.Q₁ ⊓ centralizer (V.D.D₁₁ : Set X) :=
  V.D.C_eq ▸ subset_closure (by simp)

theorem v_conj_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers V.ki : Subgroup X)) :
    V.D.v * c * V.D.v⁻¹ = c := V.v_conj_E0 (V.zk_le_E0 hc)

theorem v_mem_normalizer_B : V.D.v ∈ normalizer (S.B : Set X) := by
  have hv2 : V.D.v ^ 2 ∈ S.B := V.zk_le_B V.v_sq_mem_zk
  have hfwd : ∀ b ∈ S.B, V.D.v * b * V.D.v⁻¹ ∈ S.B := by
    intro b hb
    rcases V.mem_B_cases hb with h | h
    · rw [V.v_conj_zk h]; exact hb
    · have hb' : b = b * t * t := by rw [mul_assoc, tt (A := A), mul_one]
      rw [hb', show V.D.v * (b * t * t) * V.D.v⁻¹ =
        (V.D.v * (b * t) * V.D.v⁻¹) * (V.D.v * t * V.D.v⁻¹) by group, V.v_conj_zk h,
        V.v_conj_t]
      exact mul_mem (V.zk_le_B h) (mul_mem Frame.t_mem_B V.ki_mem_B)
  rw [mem_normalizer_iff]
  intro b
  refine ⟨hfwd b, fun h => ?_⟩
  have e : b = (V.D.v ^ 2)⁻¹ * (V.D.v * (V.D.v * b * V.D.v⁻¹) * V.D.v⁻¹) * V.D.v ^ 2 := by
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hv2) (hfwd _ h)) hv2

theorem yi_mem_Q₁ : V.yi ∈ V.D.Q₁ := V.D.Q0_le (mem_sup_left (mem_sup_left V.yi_mem_E0))

theorem not_fix_z : ¬ ∀ δ ∈ V.D.D₁₁, δ * S.z * δ⁻¹ = S.z := by
  intro hz
  have hy := V.fix_yi_of_fix_z hz
  have hyC : V.yi ∈ centralizer (V.D.D₁₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro δ hδ
    have := hy δ hδ
    calc δ * V.yi = δ * V.yi * δ⁻¹ * δ := by group
      _ = V.yi * δ := by rw [this]
  have hmem : V.yi ∈ closure ({t, V.ki, V.D.v} : Set X) := V.D.C_eq ▸ ⟨V.yi_mem_Q₁, hyC⟩
  have hle : closure ({t, V.ki, V.D.v} : Set X) ≤ S.B ⊔ zpowers V.D.v := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left Frame.t_mem_B
    · exact mem_sup_left V.ki_mem_B
    · exact mem_sup_right (mem_zpowers _)
  rcases Sec7.mem_or_of_mem_sup_zpowers V.v_mem_normalizer_B (V.zk_le_B V.v_sq_mem_zk)
    (hle hmem) with h | h
  · exact V.yi_not_mem_B h
  · have hvT : V.D.v ∈ A.T := by
      have := mul_mem (inv_mem (B_le_T S h)) V.yi_mem_T
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
    have h1 := V.v_conj_t
    rw [A.commute_t hvT, mul_inv_cancel_right] at h1
    exact V.ki_ne_one (mul_eq_left.mp h1.symm)

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

end VSide

end KD8c

end CFSG.ComponentClassification.HSFLit
