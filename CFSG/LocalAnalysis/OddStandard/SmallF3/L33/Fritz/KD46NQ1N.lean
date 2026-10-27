module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NData
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NQ1N

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S} {H : Hyp S R}

namespace Data6

variable (D : I.Data6 H)

structure Rel where
  s1 : Fin 2
  s4 : Fin 2
  γ : V4
  e : V4
  rel : I.QRel D.ε D.w₁ D.w₂ s1 s4 γ
  h0 : γ = (0, 0, 0, s4)
  h1 : D.ε = 1 → s1 = 0 ∧ s4 = 0
  w₃ : D.d * D.w₂ * D.d⁻¹ = D.w₁ * D.w₂ * I.wV e
  e_E0 : e.2.2.1 = 0
  e_z : e.1 = s1
  e_y : e.2.1 = s1

theorem nonempty_rel : Nonempty D.Rel := by
  obtain ⟨s1, s4, γ, R, h0, h1, e, he, het, hez, hey⟩ := D.exists_qrel
  exact ⟨⟨s1, s4, γ, e, R, h0, h1, he, het, hez, hey⟩⟩

theorem v_Q₁ : D.v ∈ D.Q₁ := D.mem_Q₁_of_Mat (D.T₁_le D.v_T₁) D.v_mat transl_vC

theorem w₁_Q₁ : D.w₁ ∈ D.Q₁ := D.mem_Q₁_of_Mat (D.T₁_le D.w₁_T₁) D.w₁_mat (M1C_transl D.ε)

theorem w₂_Q₁ : D.w₂ ∈ D.Q₁ := D.d_mem_Q₁ D.w₁_Q₁

theorem u_S₁ : D.u ∈ D.S₁ := by
  rcases D.u_eq with h | h <;> rw [h]
  · exact D.T₁_le (H.le I.ui_mem_TE)
  · exact D.T₁_le (H.le (mul_mem (t_mem_TE S) I.ui_mem_TE))

theorem u_mat : I.Mat D.u xCols := by
  rcases D.u_eq with h | h <;> rw [h]
  · exact I.ui_mat H
  · exact (I.ui_mat H).central_mul (I.E_le_centralizer I.t_mem_E)

theorem u_inv_d : D.u * D.d * D.u⁻¹ = D.d⁻¹ := by
  rcases D.u_eq with h | h <;> rw [h]
  · exact D.d_inv
  · have hdt : D.d * t = t * D.d := (mem_centralizer_singleton_iff.mp D.d_mem_C_t)
    calc t * I.ui * D.d * (t * I.ui)⁻¹ = t * (I.ui * D.d * I.ui⁻¹) * t⁻¹ := by group
      _ = t * D.d⁻¹ * t⁻¹ := by rw [D.d_inv]
      _ = D.d⁻¹ := by
          have : D.d⁻¹ * t = t * D.d⁻¹ := by
            calc D.d⁻¹ * t = D.d⁻¹ * (t * D.d) * D.d⁻¹ := by group
              _ = D.d⁻¹ * (D.d * t) * D.d⁻¹ := by rw [hdt]
              _ = t * D.d⁻¹ := by group
          rw [← this]; group

theorem v_w₂ : D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹ = I.wV (lin dCols (D.α, 0, 0, D.ε * D.α)) := by
  rw [w₂, comm_conj_of_commute D.v_d, D.v_w₁, D.d_mat.conj]

theorem v_sq_E : D.v ^ 2 ∈ I.E :=
  D.mem_E_of_mem_Q₁ (pow_mem D.v_Q₁ 2) (Mat.mem_centralizer (by
    have := D.v_mat.mul D.v_mat
    rwa [show comp vC vC = bas from funext vC_vC, ← pow_two] at this))

theorem conj_E {n : X} {c : Fin 4 → V4} (hn : I.Mat n c)
    (hc : ∀ e : V4, (addV e (lin c e)).2.2.1 = 0)
    (hcc : ∀ i, comp c c i = bas i) (e : V4) :
    ∃ f ∈ S.E0 I.yi I.ki, I.wV e * n * (I.wV e)⁻¹ = n * f := by
  refine ⟨n⁻¹ * I.wV e * n * (I.wV e)⁻¹, ?_, by group⟩
  have h1 : n⁻¹ * I.wV e * n⁻¹⁻¹ = I.wV (lin c e) := (hn.inv hcc).conj e
  rw [inv_inv] at h1
  rw [h1, I.wV_inv, ← I.wV_add]
  have := hc e
  rw [show addV (lin c e) e = addV e (lin c e) by
    obtain ⟨a, b, c', d⟩ := e
    obtain ⟨a', b', c'', d'⟩ := lin c (a, b, c', d)
    simp only [addV, add_comm]]
  exact I.wV_mem_E0' this

theorem Q₁_eq (R : D.Rel) :
    D.Q₁ = I.E ⊔ zpowers D.v ⊔ zpowers D.w₁ ⊔ zpowers D.w₂ := by
  have hE : ∀ {n : X} {c : Fin 4 → V4}, I.Mat n c → n ∈ normalizer (I.E : Set X) := fun h => h.1
  have hv1 : D.v ∈ normalizer (I.E : Set X) := hE D.v_mat
  have hvE : D.v ∉ I.E := fun h =>
    vC_ne_bas (D.v_mat.unique (Mat.of_mem_centralizer (I.E_le_centralizer h)))
  have hc1 := card_sup_zpowers hv1 D.v_sq_E hvE
  have hmemEv : ∀ {x : X}, x ∈ I.E ⊔ zpowers D.v ↔ x ∈ I.E ∨ D.v⁻¹ * x ∈ I.E :=
    mem_sup_zpowers_iff hv1 D.v_sq_E
  have hw₁N : D.w₁ ∈ normalizer ((I.E ⊔ zpowers D.v : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rcases hmemEv.mp hx with h | h
    · exact mem_sup_left ((mem_normalizer_iff.mp (hE D.w₁_mat) x).mp h)
    · rw [hmemEv]; right
      have hwv : D.w₁ * D.v * D.w₁⁻¹ = (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹)⁻¹ * D.v := by group
      have e1 : D.v⁻¹ * (D.w₁ * x * D.w₁⁻¹) =
          D.v⁻¹ * (D.w₁ * D.v * D.w₁⁻¹) * (D.w₁ * (D.v⁻¹ * x) * D.w₁⁻¹) := by group
      rw [e1, hwv, D.v_w₁, I.wV_inv]
      have h2 : D.v⁻¹ * (I.wV (D.α, 0, 0, D.ε * D.α) * D.v) ∈ I.E := by
        have := (mem_normalizer_iff.mp (inv_mem hv1) _).mp (I.wV_mem (D.α, 0, 0, D.ε * D.α))
        simpa [mul_assoc] using this
      exact mul_mem h2 ((mem_normalizer_iff.mp (hE D.w₁_mat) _).mp h)
  have hw₁sq : D.w₁ ^ 2 ∈ I.E ⊔ zpowers D.v := by
    rw [R.rel.sq1]; exact mem_sup_left (I.wV_mem _)
  have hw₁Ev : D.w₁ ∉ I.E ⊔ zpowers D.v := by
    intro h
    rcases hmemEv.mp h with h' | h'
    · exact M1C_ne_bas D.ε (D.w₁_mat.unique (Mat.of_mem_centralizer (I.E_le_centralizer h')))
    · have := D.v_mat.mul_central (I.E_le_centralizer h')
      rw [mul_inv_cancel_left] at this
      exact M1C_ne_vC D.ε (D.w₁_mat.unique this)
  have hc2 := card_sup_zpowers hw₁N hw₁sq hw₁Ev
  set M := I.E ⊔ zpowers D.v ⊔ zpowers D.w₁ with hM
  have hmemM : ∀ {x : X}, x ∈ M ↔ x ∈ I.E ⊔ zpowers D.v ∨ D.w₁⁻¹ * x ∈ I.E ⊔ zpowers D.v :=
    mem_sup_zpowers_iff hw₁N hw₁sq
  have hMmat : ∀ x ∈ M, ∃ c a : Fin 2, ∃ e ∈ I.E, x = D.v ^ (c : ℕ) * D.w₁ ^ (a : ℕ) * e := by
    intro x hx
    rcases hmemM.mp hx with h | h <;> rcases hmemEv.mp h with h' | h'
    · exact ⟨0, 0, x, h', by simp⟩
    · exact ⟨1, 0, D.v⁻¹ * x, h', by simp⟩
    · refine ⟨0, 1, D.w₁⁻¹ * x, h', by simp⟩
    ·
      have hc : D.w₁ * D.v = D.v * D.w₁ * (D.w₁⁻¹ * (D.v⁻¹ * D.w₁ * D.v * D.w₁⁻¹) * D.w₁) := by
        group
      refine ⟨1, 1, (D.w₁⁻¹ * (D.v⁻¹ * D.w₁ * D.v * D.w₁⁻¹) * D.w₁) * (D.v⁻¹ * (D.w₁⁻¹ * x)),
        mul_mem ?_ h', ?_⟩
      · have h3 : D.v⁻¹ * D.w₁ * D.v * D.w₁⁻¹ ∈ I.E := by
          have e1 : D.v⁻¹ * D.w₁ * D.v * D.w₁⁻¹ =
              D.v⁻¹ * (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹)⁻¹ * D.v := by group
          rw [e1, D.v_w₁, I.wV_inv]
          have := (mem_normalizer_iff.mp (inv_mem hv1) _).mp (I.wV_mem (D.α, 0, 0, D.ε * D.α))
          simpa [mul_assoc] using this
        have := (mem_normalizer_iff.mp (inv_mem (hE D.w₁_mat)) _).mp h3
        simpa [mul_assoc] using this
      · rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, pow_one, pow_one]
        calc x = D.w₁ * D.v * (D.v⁻¹ * (D.w₁⁻¹ * x)) := by group
          _ = _ := by rw [hc]; group
  have hw₂N : D.w₂ ∈ normalizer (M : Set X) := by
    have hw₂E := hE D.w₂_mat
    have hvw₂ : D.w₂ * D.v * D.w₂⁻¹ ∈ M := by
      have e1 : D.w₂ * D.v * D.w₂⁻¹ = (D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹)⁻¹ * D.v := by group
      rw [e1, D.v_w₂, I.wV_inv]
      exact mul_mem (mem_sup_left (mem_sup_left (I.wV_mem _)))
        (mem_sup_left (mem_sup_right (mem_zpowers _)))
    have hw₁w₂ : D.w₂ * D.w₁ * D.w₂⁻¹ ∈ M := by
      have e1 : D.w₂ * D.w₁ * D.w₂⁻¹ = (D.w₁ * D.w₂ * D.w₁⁻¹ * D.w₂⁻¹)⁻¹ * D.w₁ := by group
      rw [e1, R.rel.comm, I.wV_inv]
      exact mul_mem (mem_sup_left (mem_sup_left (I.wV_mem _))) (mem_sup_right (mem_zpowers _))
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨c, a, e, he, rfl⟩ := hMmat x hx
    have e1 : D.w₂ * (D.v ^ (c : ℕ) * D.w₁ ^ (a : ℕ) * e) * D.w₂⁻¹ =
        (D.w₂ * D.v * D.w₂⁻¹) ^ (c : ℕ) * (D.w₂ * D.w₁ * D.w₂⁻¹) ^ (a : ℕ) *
          (D.w₂ * e * D.w₂⁻¹) := by
      rw [conj_pow, conj_pow]; group
    rw [e1]
    exact mul_mem (mul_mem (pow_mem hvw₂ _) (pow_mem hw₁w₂ _))
      (mem_sup_left (mem_sup_left ((mem_normalizer_iff.mp hw₂E e).mp he)))
  have hw₂sq : D.w₂ ^ 2 ∈ M := by
    rw [R.rel.sq2]; exact mem_sup_left (mem_sup_left (I.wV_mem _))
  have hw₂M : D.w₂ ∉ M := by
    intro h
    obtain ⟨c, a, e, he, he'⟩ := hMmat _ h
    have := ((D.v_mat.pw c).mul (D.w₁_mat.pw a)).mul_central (I.E_le_centralizer he)
    rw [← he'] at this
    exact M2C_ne D.ε c a (D.w₂_mat.unique this)
  have hc3 := card_sup_zpowers hw₂N hw₂sq hw₂M
  have hle : I.E ⊔ zpowers D.v ⊔ zpowers D.w₁ ⊔ zpowers D.w₂ ≤ D.Q₁ :=
    sup_le (sup_le (sup_le D.E_le_Q₁ (zpowers_le.mpr D.v_Q₁)) (zpowers_le.mpr D.w₁_Q₁))
      (zpowers_le.mpr D.w₂_Q₁)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [D.card_Q₁, hc3, hc2, hc1, Inst.E, (KD46.card_E S) I.yi_mem I.yi_sq I.yi_not_mem_B]

end Data6

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
