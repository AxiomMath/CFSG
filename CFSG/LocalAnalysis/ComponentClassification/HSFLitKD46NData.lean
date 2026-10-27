module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NData
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NQ0

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

structure Data6 (H : Hyp S R) extends I.Pre6 H where
  ε : Fin 2
  hε : ε = 0 ↔ I.CaseI
  v : X
  v_T₁ : v ∈ R
  v_mat : I.Mat v vC
  v_d : v * d = d * v
  u : X
  u_eq : u = I.ui ∨ u = t * I.ui
  u_v : u * v = v * u
  w₁ : X
  w₁_T₁ : w₁ ∈ R
  w₁_mat : I.Mat w₁ (M1C ε)
  α : Fin 2
  v_w₁ : v * w₁ * v⁻¹ * w₁⁻¹ = I.wV (α, 0, 0, ε * α)
  w₁_sq : ε = 1 → w₁ ^ 2 = 1

variable {I} {H : Hyp S R}

theorem exists_data6 (I : Inst S) (H : Hyp S R) : Nonempty (I.Data6 H) := by
  obtain ⟨P⟩ := I.exists_pre6 H
  obtain ⟨ε, hε, -, -, w, hw, -, -, -, hwc, -⟩ := I.exists_vww H
  have hwM : I.Mat w (wC ε) := ⟨I.R_le H hw, hwc⟩
  obtain ⟨v, hvT, hvM, hvd⟩ := P.exists_v
  obtain ⟨u, hu, huv⟩ := P.exists_u hvT hvM hvd
  have hw₀M : I.Mat (w * v ^ (ε : ℕ)) (M1C ε) := hwM.mul (hvM.pw ε)
  have hw₀T : w * v ^ (ε : ℕ) ∈ R := mul_mem hw (pow_mem hvT _)
  obtain ⟨a, b, hab⟩ := H.commutator_mem hvT hw₀T
  obtain ⟨p, q, hpq⟩ := I.zk_eq_wV a b
  rw [hpq] at hab
  set j : Fin 2 := q + ε * p with hj
  have htj : t ^ (j : ℕ) = I.wV (0, 0, j, 0) := by simp [wV]
  have htjC : t ^ (j : ℕ) ∈ centralizer (I.E : Set X) :=
    I.E_le_centralizer (pow_mem I.t_mem_E _)
  have hw₁'M : I.Mat (w * v ^ (ε : ℕ) * t ^ (j : ℕ)) (M1C ε) := hw₀M.mul_central htjC
  have hw₁'T : w * v ^ (ε : ℕ) * t ^ (j : ℕ) ∈ R :=
    mul_mem hw₀T (pow_mem (H.le (t_mem_TE S)) _)
  have hvw₁' : v * (w * v ^ (ε : ℕ) * t ^ (j : ℕ)) * v⁻¹ *
      (w * v ^ (ε : ℕ) * t ^ (j : ℕ))⁻¹ = I.wV (p, 0, 0, ε * p) := by
    rw [comm_mul, hab, htj, hvM.conj, I.wV_inv, ← I.wV_add, vC_t_comm, hw₀M.conj, M1C_ki,
      ← I.wV_add]
    congr 1
    simp only [addV, add_zero]
    rw [hj, norm_t]
  rcases Fin.exists_fin_two.mp ⟨ε, rfl⟩ with hε0 | hε1
  ·
    subst hε0
    exact ⟨⟨P, 0, hε, v, hvT, hvM, hvd, u, hu, huv, _, hw₁'T, hw₁'M, p, hvw₁',
      fun h => absurd h (by decide)⟩⟩
  ·
    subst hε1
    set w₁' := w * v ^ ((1 : Fin 2) : ℕ) * t ^ (j : ℕ) with hw₁'
    obtain ⟨s1, s4, hs, γ, -, e, -, -, -, -, -, h2⟩ :=
      P.w_struct hvM hvd hw₁'T hw₁'M hvw₁' rfl
    have hs1 := h2 rfl
    subst hs1
    have hyC : I.yi ^ (s4 : ℕ) ∈ centralizer (I.E : Set X) :=
      I.E_le_centralizer (pow_mem I.yi_mem_E _)
    have hy : I.yi ^ (s4 : ℕ) = I.wV (0, s4, 0, 0) := by simp [wV]
    refine ⟨⟨P, 1, hε, v, hvT, hvM, hvd, u, hu, huv, w₁' * I.yi ^ (s4 : ℕ),
      mul_mem hw₁'T (pow_mem (H.le (I.E_le_TE I.yi_mem_E)) _), hw₁'M.mul_central hyC, p, ?_,
      fun _ => ?_⟩⟩
    · rw [comm_mul, hvw₁', hy, hvM.conj, I.wV_inv, ← I.wV_add, vC_yi_comm, I.wV_zero]
      group
    · have e1 : (w₁' * I.yi ^ (s4 : ℕ)) ^ 2 =
          w₁' ^ 2 * (w₁'⁻¹ * I.yi ^ (s4 : ℕ) * w₁'⁻¹⁻¹) * I.yi ^ (s4 : ℕ) := by
        simp only [pow_two]; group
      rw [e1, hs, hy, (hw₁'M.inv (M1C_sq 1)).conj, M1C_one_yi', ← I.wV_add, ← I.wV_add,
        norm_yi, I.wV_zero]

namespace Data6

variable (D : I.Data6 H)

@[expose] noncomputable def w₂ : X := D.d * D.w₁ * D.d⁻¹

theorem w₂_mat : I.Mat D.w₂ (M2C D.ε) := (D.d_mat.mul D.w₁_mat).mul (D.d_mat.inv dCols_ddCols)

theorem exists_qrel : ∃ s1 s4 : Fin 2, ∃ γ : V4, I.QRel D.ε D.w₁ D.w₂ s1 s4 γ ∧
    γ = (0, 0, 0, s4) ∧ (D.ε = 1 → s1 = 0 ∧ s4 = 0) ∧
    ∃ e : V4, D.d * D.w₂ * D.d⁻¹ = D.w₁ * D.w₂ * I.wV e ∧ e.2.2.1 = 0 ∧ e.1 = s1 ∧
      e.2.1 = s1 := by
  obtain ⟨s1, s4, hs, γ, hγ, e, he, het, h0, he1, he2, h1⟩ :=
    D.w_struct D.v_mat D.v_d D.w₁_T₁ D.w₁_mat D.v_w₁ rfl
  refine ⟨s1, s4, γ, ⟨D.w₁_mat, D.w₂_mat, hs, ?_, hγ, by rw [h0]⟩, h0, fun h => ?_, e, he, het,
    he1, he2⟩
  · rw [w₂, conj_pow, hs, D.d_mat.conj]
  · refine ⟨h1 h, ?_⟩
    have h2 := D.w₁_sq h
    rw [hs, h1 h, ← I.wV_zero] at h2
    have := I.wV_injective h2
    simp only [Prod.mk.injEq] at this
    exact this.2.2.2

end Data6

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
