module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8IPair
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MA
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MB

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace ISide

variable (V : ISide S F T₁)

theorem conj_E {e f : X} (he : e ∈ S.E V.yi) (hf : f ∈ S.E V.yi) : e * f * e⁻¹ = f := by
  rw [V.hyi.elemAbelianTwo_E.comm _ he _ hf, mul_inv_cancel_right]

theorem w₂_conj_t' : V.D.w₂ * S.t * V.D.w₂⁻¹ = V.yi * S.t := by
  rw [V.w₂_conj_t]; exact (V.hyi.comm_B t_mem_B).symm

theorem w₁N_conj_t' : V.w₁N * S.t * V.w₁N⁻¹ = S.z * S.t := by
  rw [V.w₁N_conj_t]; exact commute_of_mem_B t_mem_B z_mem_B

theorem E_le_S₁ : S.E V.yi ≤ V.D.S₁ := by
  intro e he
  rw [V.D.S₁_eq]
  exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left he)))

theorem B_le_S₁ : S.B ≤ V.D.S₁ := (B_le_E V.yi).trans V.E_le_S₁

theorem yi_mem_S₁ : V.yi ∈ V.D.S₁ := V.E_le_S₁ (mem_E_self _)

end ISide

namespace IPair

variable (P : IPair S F T₁)

theorem pcXA (h : P.V.D.q0 = .elem) :
    MA.PcX P.V.D.w₂ P.V.D.u P.V.w₁N P.V.vN S.z P.V.yi S.t P.V.ki where
  w₂_sq := by rw [← pow_two]; exact P.V.w₂_sq_of_elem h
  w₂_u := P.V.w₂_conj_u
  w₂_w₁ := by rw [P.V.w₂_comm_w₁N, mul_inv_cancel_right]
  w₂_v := by rw [(P.option_of_elem h).1, mul_inv_cancel_right]
  w₂_z := P.V.w₂_conj_E0 (z_mem_E0 _ _)
  w₂_y := P.V.w₂_conj_E0 (yi_mem_E0 _ _)
  w₂_t := P.V.w₂_conj_t'
  w₂_k := P.V.w₂_conj_E0 (ki_mem_E0 _ _)
  u_sq := P.V.u_sq
  u_w₁ := P.V.u_conj_w₁N_of_elem h
  u_v := by rw [P.V.u_comm_vN, mul_inv_cancel_right]
  u_z := P.V.u_conj_z
  u_y := P.V.u_conj_yi
  u_t := P.V.u_conj_t
  u_k := P.V.u_conj_ki
  w₁_sq := by rw [← pow_two]; exact P.V.w₁N_sq_of_elem h
  w₁_v := by rw [(P.option_of_elem h).2, mul_inv_cancel_right]
  w₁_z := P.V.w₁N_conj_E0 (z_mem_E0 _ _)
  w₁_y := P.V.w₁N_conj_E0 (yi_mem_E0 _ _)
  w₁_t := P.V.w₁N_conj_t'
  w₁_k := P.V.w₁N_conj_E0 (ki_mem_E0 _ _)
  v_sq := P.V.vN_mul_vN
  v_z := P.V.vN_conj_z
  v_y := P.V.vN_conj_yi
  v_t := P.V.vN_conj_t
  v_k := P.V.vN_conj_ki
  z_sq := z_mul_z
  z_y := P.V.conj_E (z_mem_E _) (mem_E_self _)
  z_t := P.V.conj_E (z_mem_E _) (t_mem_E _)
  z_k := P.V.conj_E (z_mem_E _) (B_le_E _ P.V.hki.mem)
  y_sq := P.V.yi_sq
  y_t := P.V.conj_E (mem_E_self _) (t_mem_E _)
  y_k := P.V.conj_E (mem_E_self _) (B_le_E _ P.V.hki.mem)
  t_sq := t_mul_t
  t_k := P.V.conj_E (t_mem_E _) (B_le_E _ P.V.hki.mem)
  k_sq := P.V.ki_sq

theorem pcXB (h : P.V.D.q0 = .homocyclic) :
    MB.PcX P.V.D.w₂ P.V.D.u P.V.w₁N P.V.vN S.z P.V.yi S.t P.V.ki where
  w₂_sq := by rw [← pow_two]; exact P.V.w₂_sq_of_homoc h
  w₂_u := P.V.w₂_conj_u
  w₂_w₁ := by rw [P.V.w₂_comm_w₁N, mul_inv_cancel_right]
  w₂_v := (P.option_of_homoc h).1
  w₂_z := P.V.w₂_conj_E0 (z_mem_E0 _ _)
  w₂_y := P.V.w₂_conj_E0 (yi_mem_E0 _ _)
  w₂_t := P.V.w₂_conj_t'
  w₂_k := P.V.w₂_conj_E0 (ki_mem_E0 _ _)
  u_sq := P.V.u_sq
  u_w₁ := P.V.u_conj_w₁N_of_homoc h
  u_v := by rw [P.V.u_comm_vN, mul_inv_cancel_right]
  u_z := P.V.u_conj_z
  u_y := P.V.u_conj_yi
  u_t := P.V.u_conj_t
  u_k := P.V.u_conj_ki
  w₁_sq := by rw [← pow_two]; exact P.V.w₁N_sq_of_homoc h
  w₁_v := (P.option_of_homoc h).2
  w₁_z := P.V.w₁N_conj_E0 (z_mem_E0 _ _)
  w₁_y := P.V.w₁N_conj_E0 (yi_mem_E0 _ _)
  w₁_t := P.V.w₁N_conj_t'
  w₁_k := P.V.w₁N_conj_E0 (ki_mem_E0 _ _)
  v_sq := P.V.vN_mul_vN
  v_z := P.V.vN_conj_z
  v_y := P.V.vN_conj_yi
  v_t := P.V.vN_conj_t
  v_k := P.V.vN_conj_ki
  z_sq := z_mul_z
  z_y := P.V.conj_E (z_mem_E _) (mem_E_self _)
  z_t := P.V.conj_E (z_mem_E _) (t_mem_E _)
  z_k := P.V.conj_E (z_mem_E _) (B_le_E _ P.V.hki.mem)
  y_sq := P.V.yi_sq
  y_t := P.V.conj_E (mem_E_self _) (t_mem_E _)
  y_k := P.V.conj_E (mem_E_self _) (B_le_E _ P.V.hki.mem)
  t_sq := t_mul_t
  t_k := P.V.conj_E (t_mem_E _) (B_le_E _ P.V.hki.mem)
  k_sq := P.V.ki_sq

theorem zk_ne_one : S.z * P.V.ki ≠ 1 := fun h => by
  have := inv_eq_of_mul_eq_one_right h
  rw [z_inv'] at this
  exact (ki_not_mem_z P.V.hki).2 this.symm

noncomputable def ιA (h : P.V.D.q0 = .elem) : MA →* X :=
  Classical.choose (MA.exists_hom (P.pcXA h))

variable {P} in
theorem ιA_spec (h : P.V.D.q0 = .elem) : P.ιA h MA.w₂ = P.V.D.w₂ ∧ P.ιA h MA.u = P.V.D.u ∧
    P.ιA h MA.w₁ = P.V.w₁N ∧ P.ιA h MA.v = P.V.vN ∧ P.ιA h MA.z = S.z ∧
      P.ιA h MA.y = P.V.yi ∧ P.ιA h MA.t = S.t ∧ P.ιA h MA.k = P.V.ki :=
  Classical.choose_spec (MA.exists_hom (P.pcXA h))

noncomputable def ιB (h : P.V.D.q0 = .homocyclic) : MB →* X :=
  Classical.choose (MB.exists_hom (P.pcXB h))

variable {P} in
theorem ιB_spec (h : P.V.D.q0 = .homocyclic) : P.ιB h MB.w₂ = P.V.D.w₂ ∧
    P.ιB h MB.u = P.V.D.u ∧ P.ιB h MB.w₁ = P.V.w₁N ∧ P.ιB h MB.v = P.V.vN ∧
      P.ιB h MB.z = S.z ∧ P.ιB h MB.y = P.V.yi ∧ P.ιB h MB.t = S.t ∧ P.ιB h MB.k = P.V.ki :=
  Classical.choose_spec (MB.exists_hom (P.pcXB h))

variable {P} in
theorem ιA_injective (h : P.V.D.q0 = .elem) : Function.Injective (P.ιA h) := by
  obtain ⟨-, -, -, -, hz, -, -, hk⟩ := ιA_spec h
  exact MA.injective_of _ (by rw [hz]; exact S.z_ne_one) (by rw [hk]; exact P.V.hki.ne_one)
    (by rw [hz, hk]; exact P.zk_ne_one)

variable {P} in
theorem ιB_injective (h : P.V.D.q0 = .homocyclic) : Function.Injective (P.ιB h) := by
  obtain ⟨-, -, -, -, hz, -, -, hk⟩ := ιB_spec h
  exact MB.injective_of _ (by rw [hz]; exact S.z_ne_one) (by rw [hk]; exact P.V.hki.ne_one)
    (by rw [hz, hk]; exact P.zk_ne_one)

theorem S₁_le_of {H : Subgroup X} (hz : S.z ∈ H) (hy : P.V.yi ∈ H) (ht : S.t ∈ H)
    (hk : P.V.ki ∈ H) (hv : P.V.vN ∈ H) (hw₁ : P.V.w₁N ∈ H) (hw₂ : P.V.D.w₂ ∈ H)
    (hu : P.V.D.u ∈ H) : P.V.D.S₁ ≤ H := by
  have hB : S.B ≤ H := by
    rw [P.V.B_eq]
    exact sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hk)) (zpowers_le.mpr ht)
  have hE0 : S.E0 P.V.yi P.V.ki ≤ H := by
    rw [E0_eq]
    exact sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hk)) (zpowers_le.mpr hy)
  rw [P.V.D.S₁_eq]
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) (zpowers_le.mpr hw₂)) (zpowers_le.mpr hu)
  · rw [E_eq]; exact sup_le hB (zpowers_le.mpr hy)
  · refine zpowers_le.mpr ?_
    rcases P.V.vN_eq with h | h
    · rw [← h]; exact hv
    · have : P.V.D.v = P.V.vN * S.t⁻¹ := by rw [h]; group
      rw [this]; exact mul_mem hv (inv_mem ht)
  · refine zpowers_le.mpr ?_
    obtain ⟨c, hc, hw⟩ := P.V.w₁_eq
    rw [hw]; exact mul_mem hw₁ (hE0 hc)

theorem gens_mem_S₁ : S.z ∈ P.V.D.S₁ ∧ P.V.yi ∈ P.V.D.S₁ ∧ S.t ∈ P.V.D.S₁ ∧
    P.V.ki ∈ P.V.D.S₁ ∧ P.V.vN ∈ P.V.D.S₁ ∧ P.V.w₁N ∈ P.V.D.S₁ ∧ P.V.D.w₂ ∈ P.V.D.S₁ ∧
      P.V.D.u ∈ P.V.D.S₁ :=
  ⟨P.V.B_le_S₁ z_mem_B, P.V.yi_mem_S₁, P.V.B_le_S₁ t_mem_B, P.V.B_le_S₁ P.V.hki.mem,
    P.V.vN_mem_S₁, P.V.w₁N_mem_S₁, P.V.w₂_mem_S₁, P.V.u_mem_S₁⟩

variable {P} in
theorem range_ιA (h : P.V.D.q0 = .elem) : (P.ιA h).range = P.V.D.S₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ιA_spec h
  obtain ⟨g5, g6, g7, g8, g4, g3, g1, g2⟩ := P.gens_mem_S₁
  apply le_antisymm
  · refine MA.range_le _ fun g hg => ?_
    simp only [MA.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1]; exact g1
    · rw [h2]; exact g2
    · rw [h3]; exact g3
    · rw [h4]; exact g4
    · rw [h5]; exact g5
    · rw [h6]; exact g6
    · rw [h7]; exact g7
    · rw [h8]; exact g8
  · exact P.S₁_le_of ⟨_, h5⟩ ⟨_, h6⟩ ⟨_, h7⟩ ⟨_, h8⟩ ⟨_, h4⟩ ⟨_, h3⟩ ⟨_, h1⟩ ⟨_, h2⟩

variable {P} in
theorem range_ιB (h : P.V.D.q0 = .homocyclic) : (P.ιB h).range = P.V.D.S₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ιB_spec h
  obtain ⟨g5, g6, g7, g8, g4, g3, g1, g2⟩ := P.gens_mem_S₁
  apply le_antisymm
  · refine MB.range_le _ fun g hg => ?_
    simp only [MB.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1]; exact g1
    · rw [h2]; exact g2
    · rw [h3]; exact g3
    · rw [h4]; exact g4
    · rw [h5]; exact g5
    · rw [h6]; exact g6
    · rw [h7]; exact g7
    · rw [h8]; exact g8
  · exact P.S₁_le_of ⟨_, h5⟩ ⟨_, h6⟩ ⟨_, h7⟩ ⟨_, h8⟩ ⟨_, h4⟩ ⟨_, h3⟩ ⟨_, h1⟩ ⟨_, h2⟩

end IPair

end Sec8

end CFSG.ComponentClassification.HSFLit
