module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NMisc
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NInv

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

@[expose] def actOf (ε : Fin 2) : ActType := if ε = 0 then .one else .two

@[expose] def q0Of (ε s1 s4 : Fin 2) : Q0Type :=
  if ε = 0 then
    (if s1 = 0 then (if s4 = 0 then .elem else .e4q8)
      else (if s4 = 0 then .homocyclic else .exceptional))
  else .extraspecial

theorem q0Of_cases (ε s1 s4 : Fin 2) :
    (q0Of ε s1 s4 = .elem ∧ ε = 0 ∧ s1 = 0 ∧ s4 = 0) ∨
    (q0Of ε s1 s4 = .homocyclic ∧ ε = 0 ∧ s1 = 1 ∧ s4 = 0) ∨
    (q0Of ε s1 s4 = .e4q8 ∧ ε = 0 ∧ s1 = 0 ∧ s4 = 1) ∨
    (q0Of ε s1 s4 = .exceptional ∧ ε = 0 ∧ s1 = 1 ∧ s4 = 1) ∨
    (q0Of ε s1 s4 = .extraspecial ∧ ε = 1) := by
  fin_cases ε <;> fin_cases s1 <;> fin_cases s4 <;> simp [q0Of]

namespace Inst

variable {I : Inst S} {H : Hyp S R}

theorem wV_t (I : Inst S) : t = I.wV (0, 0, 1, 0) := by simp [wV]

theorem wV_t_mul (I : Inst S) (v : V4) : t * I.wV v = I.wV (addV (0, 0, 1, 0) v) := by
  rw [I.wV_add, show I.wV (0, 0, 1, 0) = t by simp [wV]]

theorem wV_z (I : Inst S) : S.z = I.wV (1, 0, 0, 0) := by simp [wV]

theorem wV_yi (I : Inst S) : I.yi = I.wV (0, 1, 0, 0) := by simp [wV]

theorem wV_ki (I : Inst S) : I.ki = I.wV (0, 0, 0, 1) := by simp [wV]

namespace Data6

variable (D : I.Data6 H)

theorem v_central : ∀ n ∈ normalizer (S.E I.yi : Set X), n * D.v * n⁻¹ * D.v⁻¹ ∈
    centralizer (S.E I.yi : Set X) := by
  intro n hn
  obtain ⟨ε', hε', -, hcl⟩ := I.exists_setup H
  obtain ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, hcols⟩ := hcl ⟨n, hn⟩
  have hnM : I.Mat n (HSFLit.cls ε' a b c σ₁ σ₂) := ⟨hn, hcols⟩
  have h1 := hnM.mul D.v_mat
  have h2 := D.v_mat.mul hnM
  rw [(vC_central ε' a b c σ₁ h₁ σ₂ h₂).resolve_left h12] at h1
  have hC := h2.inv_mul_mem_centralizer h1
  have e : n * D.v * n⁻¹ * D.v⁻¹ = (D.v * n) * ((D.v * n)⁻¹ * (n * D.v)) * (D.v * n)⁻¹ := by
    group
  rw [e]
  exact I.conj_mem_centralizerE (mul_mem D.v_mat.mem hn) hC

theorem normalizer_inf_centralizer :
    normalizer (S.E I.yi : Set X) ⊓ centralizer ({t} : Set X) =
      centralizer (S.E I.yi : Set X) ⊔ zpowers D.d ⊔ zpowers D.u := by
  have huT : D.u ∈ S.TE := by
    rcases D.u_eq with h | h <;> rw [h]
    · exact I.ui_mem_TE
    · exact mul_mem (t_mem_TE S) I.ui_mem_TE
  apply le_antisymm
  · intro n hn
    obtain ⟨σ₁, h₁, σ₂, h₂, h12, hσ⟩ := I.cols_of_mem_NC H.fus ⟨n, hn.1⟩ hn.2
    obtain ⟨i, j, hij⟩ := (sig_decomp σ₁ h₁ σ₂ h₂).resolve_left h12
    have hgM : I.Mat (D.d ^ (i : ℕ) * D.u ^ (j : ℕ)) (sigCols σ₁ σ₂) := by
      have := (D.d_mat.pw3 i).mul (D.u_mat.pw j)
      rwa [hij] at this
    have hc := hgM.inv_mul_mem_centralizer (⟨hn.1, hσ⟩ : I.Mat n (sigCols σ₁ σ₂))
    have e : n = D.d ^ (i : ℕ) * D.u ^ (j : ℕ) * ((D.d ^ (i : ℕ) * D.u ^ (j : ℕ))⁻¹ * n) := by
      group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_right (pow_mem (mem_zpowers _) _)))
      (mem_sup_right (pow_mem (mem_zpowers _) _))) (mem_sup_left (mem_sup_left hc))
  · refine sup_le (sup_le (fun c hc => mem_inf.mpr ⟨I.centralizer_le_normalizer hc, ?_⟩) ?_) ?_
    · rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hc) t I.t_mem_E).symm
    · exact zpowers_le.mpr (mem_inf.mpr ⟨D.d_mat.mem, D.d_mem_C_t⟩)
    · exact zpowers_le.mpr (mem_inf.mpr ⟨D.u_mat.mem, (TE_le_C S) huT⟩)

theorem isPGroup_D₁₁ : IsPGroup 3 (zpowers D.d) := by
  obtain ⟨a, ha⟩ := D.d_pow
  have hdvd : orderOf D.d ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem u_inv_D₁₁ : ∀ δ ∈ zpowers D.d, D.u * δ * D.u⁻¹ * δ ∈
    A7Base.oddCoreIn (centralizer (S.E I.yi : Set X)) := by
  rintro _ ⟨n, rfl⟩
  have h : D.u * D.d ^ n * D.u⁻¹ = (D.d ^ n)⁻¹ := by
    have e : D.u * D.d ^ n * D.u⁻¹ = (MulAut.conj D.u) (D.d ^ n) := rfl
    rw [e, map_zpow, MulAut.conj_apply, D.u_inv_d, inv_zpow]
  simp only
  rw [h, inv_mul_cancel]
  exact one_mem _

theorem d_cube_mem : D.d ^ 3 ∈ centralizer (S.E I.yi : Set X) := by
  apply Mat.mem_centralizer
  have := D.d_mat.mul (D.d_mat.mul D.d_mat)
  rwa [show comp dCols (comp dCols dCols) = bas from funext dCols_cube, ← pow_three] at this

theorem d_not_mem : D.d ∉ centralizer (S.E I.yi : Set X) := fun h =>
  dCols_ne_bas (D.d_mat.unique (Mat.of_mem_centralizer h))

theorem u_comm_w₁ : D.u * D.w₁ * D.u⁻¹ * D.w₁⁻¹ ∈ centralizer (S.E I.yi : Set X) := by
  obtain ⟨φ, hφ, hw⟩ := D.u_conj_w₁
  rw [hw]
  have hE : D.w₁ * I.wV φ * D.w₁⁻¹ ∈ I.E := (mem_normalizer_iff.mp D.w₁_mat.mem _).mp (I.wV_mem φ)
  exact I.E_le_centralizer hE

theorem act_holds : S.ActHolds I.yi I.ki D.v D.w₁ D.w₂ (actOf D.ε) := by
  have hv : ∀ e ∈ S.E0 I.yi I.ki, D.v * e * D.v⁻¹ = e := fun e he => by
    obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
    rw [D.v_mat.conj, vC_E0_fix]
  have hvt : D.v * t * D.v⁻¹ = t * I.ki := D.v_conj_t
  rcases Fin.exists_fin_two.mp ⟨D.ε, rfl⟩ with h | h
  · have hM1 : I.Mat D.w₁ (M1C 0) := h ▸ D.w₁_mat
    have hM2 : I.Mat D.w₂ (M2C 0) := h ▸ D.w₂_mat
    rw [h]
    refine ⟨fun e he => ⟨hv e he, ?_, ?_⟩, hvt, ?_, ?_⟩
    · obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
      rw [hM1.conj, M1C_fix_one]
    · obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
      rw [hM2.conj, M2C_fix_one]
    · rw [hM1.conj_t, M1C_zero_cols, I.wV_z, I.wV_t_mul]; rfl
    · rw [hM2.conj_t, M2C_zero_cols, I.wV_yi, I.wV_t_mul]; rfl
  · have hM1 : I.Mat D.w₁ (M1C 1) := h ▸ D.w₁_mat
    have hM2 : I.Mat D.w₂ (M2C 1) := h ▸ D.w₂_mat
    rw [h]
    refine ⟨hv, hvt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hM1.conj_t, M1C_one_cols, I.wV_z, I.wV_ki, I.wV_t_mul, ← I.wV_add]; rfl
    · rw [hM2.conj_t, M2C_one_cols, I.wV_yi, I.wV_ki, I.wV_t_mul, ← I.wV_add]; rfl
    · rw [hM1.conj_z, M1C_one_cols, I.wV_z]; rfl
    · rw [hM2.conj_yi, M2C_one_cols, I.wV_yi]; rfl
    · rw [hM2.conj_z, M2C_one_cols, I.wV_z, I.wV_ki, ← I.wV_add]; rfl
    · rw [hM1.conj_yi, M1C_one_cols, I.wV_yi, I.wV_ki, ← I.wV_add]; rfl
    · rw [hM1.conj_ki, M1C_one_cols, I.wV_ki]; rfl
    · rw [hM2.conj_ki, M2C_one_cols, I.wV_ki]; rfl

variable (Rl : D.Rel)

include Rl in
theorem q0_holds : S.Q0Holds I.yi I.ki D.v D.w₁ D.w₂ (q0Of D.ε Rl.s1 Rl.s4) := by
  have hγ := Rl.h0
  rcases q0Of_cases D.ε Rl.s1 Rl.s4 with ⟨hq, hε, h1, h4⟩ | ⟨hq, hε, h1, h4⟩ | ⟨hq, hε, h1, h4⟩ |
      ⟨hq, hε, h1, h4⟩ | ⟨hq, hε⟩ <;> rw [hq]
  · rw [h4] at hγ
    exact ⟨Rl.rel.comm_one hε hγ, Rl.rel.sq_one hε hγ h1 h4, Rl.rel.card_Q0⟩
  · rw [h4] at hγ
    refine ⟨?_, ?_, Rl.rel.comm_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_z]
    · rw [Rl.rel.sq2, h1, h4, I.wV_yi]; rfl
  · rw [h4] at hγ
    refine ⟨?_, ?_, Rl.rel.center_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_ki]
    · rw [Rl.rel.sq2, h1, h4, I.wV_ki]; rfl
  · rw [h4] at hγ
    refine ⟨?_, ?_, ?_, Rl.rel.center_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_z, I.wV_ki, ← I.wV_add]; rfl
    · rw [Rl.rel.sq2, h1, h4, I.wV_yi, I.wV_ki, ← I.wV_add]; rfl
    · rw [Rl.rel.comm, hγ, I.wV_ki]
  · obtain ⟨h1, h4⟩ := Rl.h1 hε
    have hact := D.act_holds
    rw [hε] at hact
    refine ⟨?_, ?_, hact, Rl.rel.center_two hε, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_zero]
    · rw [Rl.rel.sq2, h1, h4, show lin dCols (0, 0, 0, 0) = (0, 0, 0, 0) by decide, I.wV_zero]

end Data6

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
