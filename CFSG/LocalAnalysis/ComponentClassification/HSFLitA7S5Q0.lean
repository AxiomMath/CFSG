module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Q

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem transCols_conj_d' : ∀ i, comp (comp dCols (transCols 0 1)) (comp dCols dCols) i =
    transCols 1 1 i := by decide

theorem transCols_comm : ∀ i,
    comp (comp (comp (transCols 1 0) (transCols 0 1)) (transCols 1 0)) (transCols 0 1) i =
      bas i := by decide

theorem transCols_one_one : ∀ i, comp (transCols 1 0) (transCols 0 1) i = transCols 1 1 i := by
  decide

theorem transCols_fix : ∀ a b p q r : Fin 2, lin (transCols a b) (p, q, 0, r) = (p, q, 0, r) := by
  decide

theorem transCols_inv_mul : ∀ i, comp (transCols 1 1) (transCols 1 1) i = bas i := by decide

theorem comm_relation : ∀ γ : V4, ∀ a : Fin 2,
    addV (addV (lin (transCols 1 0) γ) (a, 0, 0, 0)) (lin dCols (a, 0, 0, 0)) ≠
      lin dCols (lin dCols (a, 0, 0, 0)) ∨ γ = (0, 0, 0, 0) := by decide

theorem d_relation : ∀ p q a : Fin 2,
    addV (addV (lin dCols (p, q, 0, 0)) (p, q, 0, 0)) (lin dCols (a, 0, 0, 0)) ≠ (0, 0, 0, 0) ∨
      (p = a ∧ q = a) := by decide

theorem dCols_a : ∀ a : Fin 2, lin dCols (a, 0, 0, 0) = (0, a, 0, 0) := by decide

theorem dCols_pq : ∀ p q : Fin 2, lin dCols (p, q, 0, 0) = (q, p + q, 0, 0) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

structure Inst.QD (I : S.Inst) where
  Q : Subgroup X
  d : X
  isPGroup : IsPGroup 2 Q
  le : Q ≤ normalizer (I.E : Set X)
  inf_centralizer : Q ⊓ centralizer (I.E : Set X) = I.E
  d_mat : I.Mat d dCols
  d_normalizer : d ∈ normalizer (Q : Set X)
  d_cube : ∀ q ∈ Q, d ^ 3 * q = q * d ^ 3
  ki_central : ∀ q ∈ Q, q * I.ki = I.ki * q

namespace Inst.QD

variable {I : S.Inst} (D : I.QD)

@[expose] def w2 (w₁ : X) : X := D.d * w₁ * D.d⁻¹

@[expose] def w3 (w₁ : X) : X := D.d * D.w2 w₁ * D.d⁻¹

@[expose] def eL (w₁ : X) : X := D.w3 w₁ * (w₁ * D.w2 w₁)⁻¹

theorem conj_mem {q : X} (hq : q ∈ D.Q) : D.d * q * D.d⁻¹ ∈ D.Q :=
  (mem_normalizer_iff.mp D.d_normalizer q).mp hq

theorem E_le : I.E ≤ D.Q := by
  intro e he
  have : e ∈ D.Q ⊓ centralizer (I.E : Set X) := by rw [D.inf_centralizer]; exact he
  exact this.1

theorem mem_E {q : X} (hq : q ∈ D.Q) (hM : I.Mat q bas) : q ∈ I.E := by
  have : q ∈ D.Q ⊓ centralizer (I.E : Set X) := mem_inf.mpr ⟨hq, hM.mem_centralizer⟩
  rwa [D.inf_centralizer] at this

theorem d_inv_mat : I.Mat D.d⁻¹ (comp dCols dCols) := D.d_mat.inv dCols_ddCols'

omit D in
theorem wV_inv_self (v : V4) : (I.wV v)⁻¹ = I.wV v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact I.sq_eq_one (I.wV_mem _))

variable {w₁ : X} {p q a : Fin 2}

theorem w2_mem (hw₁ : w₁ ∈ D.Q) : D.w2 w₁ ∈ D.Q := D.conj_mem hw₁

theorem w2_mat (hM : I.Mat w₁ (transCols 1 0)) : I.Mat (D.w2 w₁) (transCols 0 1) := by
  have := (D.d_mat.mul hM).mul D.d_inv_mat
  rwa [show comp (comp dCols (transCols 1 0)) (comp dCols dCols) = transCols 0 1 from
    funext transCols_conj_d] at this

theorem w3_mem (hw₁ : w₁ ∈ D.Q) : D.w3 w₁ ∈ D.Q := D.conj_mem (D.w2_mem hw₁)

theorem w3_mat (hM : I.Mat w₁ (transCols 1 0)) : I.Mat (D.w3 w₁) (transCols 1 1) := by
  have := (D.d_mat.mul (D.w2_mat hM)).mul D.d_inv_mat
  rwa [show comp (comp dCols (transCols 0 1)) (comp dCols dCols) = transCols 1 1 from
    funext transCols_conj_d'] at this

theorem w12_mat (hM : I.Mat w₁ (transCols 1 0)) : I.Mat (w₁ * D.w2 w₁) (transCols 1 1) := by
  have := hM.mul (D.w2_mat hM)
  rwa [show comp (transCols 1 0) (transCols 0 1) = transCols 1 1 from
    funext transCols_one_one] at this

theorem eL_mem (hw₁ : w₁ ∈ D.Q) (hM : I.Mat w₁ (transCols 1 0)) : D.eL w₁ ∈ I.E := by
  refine D.mem_E (mul_mem (D.w3_mem hw₁) (inv_mem (mul_mem hw₁ (D.w2_mem hw₁)))) ?_
  have := (D.w3_mat hM).mul ((D.w12_mat hM).inv transCols_inv_mul)
  rwa [show comp (transCols 1 1) (transCols 1 1) = bas from funext transCols_inv_mul] at this

theorem eL_mul_ki (hw₁ : w₁ ∈ D.Q) : D.eL (w₁ * I.ki) = D.eL w₁ * I.ki := by
  have hdk : D.d * I.ki * D.d⁻¹ = I.ki := by
    rw [D.d_mat.conj_ki]; simp [dCols, sigCols, Inst.wV]
  have hk2 : D.w2 (w₁ * I.ki) = D.w2 w₁ * I.ki := by
    simp only [w2]
    calc D.d * (w₁ * I.ki) * D.d⁻¹ = D.d * w₁ * D.d⁻¹ * (D.d * I.ki * D.d⁻¹) := by group
      _ = D.d * w₁ * D.d⁻¹ * I.ki := by rw [hdk]
  have hk3 : D.w3 (w₁ * I.ki) = D.w3 w₁ * I.ki := by
    simp only [w3]
    rw [hk2]
    calc D.d * (D.w2 w₁ * I.ki) * D.d⁻¹ = D.d * D.w2 w₁ * D.d⁻¹ * (D.d * I.ki * D.d⁻¹) := by
          group
      _ = D.d * D.w2 w₁ * D.d⁻¹ * I.ki := by rw [hdk]
  have hc2 := D.ki_central _ (D.w2_mem hw₁)
  have hk1 : I.ki * I.ki = 1 := by rw [← pow_two, I.ki_sq]
  simp only [eL]
  rw [hk2, hk3]
  calc D.w3 w₁ * I.ki * (w₁ * I.ki * (D.w2 w₁ * I.ki))⁻¹ =
      D.w3 w₁ * I.ki * (w₁ * (I.ki * D.w2 w₁) * I.ki)⁻¹ := by group
    _ = D.w3 w₁ * I.ki * (w₁ * (D.w2 w₁ * I.ki) * I.ki)⁻¹ := by rw [hc2]
    _ = D.w3 w₁ * I.ki * (w₁ * D.w2 w₁ * (I.ki * I.ki))⁻¹ := by group
    _ = D.w3 w₁ * (w₁ * D.w2 w₁)⁻¹ * I.ki := by
        rw [hk1, mul_one]
        have hc : I.ki * (w₁ * D.w2 w₁)⁻¹ = (w₁ * D.w2 w₁)⁻¹ * I.ki := by
          have := D.ki_central _ (inv_mem (mul_mem hw₁ (D.w2_mem hw₁)))
          exact this.symm
        rw [mul_assoc, hc, ← mul_assoc]

theorem eL_mul_t (hw₁ : w₁ ∈ D.Q) (hM : I.Mat w₁ (transCols 1 0)) :
    D.eL (w₁ * S.t) = D.eL w₁ * (S.t * S.z) := by
  have hdt : D.d * S.t * D.d⁻¹ = S.t := by
    rw [D.d_mat.conj_t]; simp [dCols, sigCols, Inst.wV]
  have ht2 : D.w2 (w₁ * S.t) = D.w2 w₁ * S.t := by
    simp only [w2]
    calc D.d * (w₁ * S.t) * D.d⁻¹ = D.d * w₁ * D.d⁻¹ * (D.d * S.t * D.d⁻¹) := by group
      _ = D.d * w₁ * D.d⁻¹ * S.t := by rw [hdt]
  have ht3 : D.w3 (w₁ * S.t) = D.w3 w₁ * S.t := by
    simp only [w3]
    rw [ht2]
    calc D.d * (D.w2 w₁ * S.t) * D.d⁻¹ = D.d * D.w2 w₁ * D.d⁻¹ * (D.d * S.t * D.d⁻¹) := by
          group
      _ = D.d * D.w2 w₁ * D.d⁻¹ * S.t := by rw [hdt]
  have hw2M := D.w2_mat hM
  have hw3M := D.w3_mat hM
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have h2t : (D.w2 w₁)⁻¹ * S.t * D.w2 w₁ = S.t * I.yi := by
    have hinv := hw2M.inv (transCols_sq 0 1)
    have := hinv.conj_t
    rw [inv_inv] at this
    rw [this]
    simp [transCols, Inst.wV, S.data.commute_t I.yi_mem.1]
  have h3t : D.w3 w₁ * S.t * (D.w3 w₁)⁻¹ = S.t * (S.z * I.yi) := by
    rw [hw3M.conj_t]
    simp only [transCols, Inst.wV, Matrix.cons_val, Fin.val_one, Fin.val_zero, pow_one,
      pow_zero, mul_one]
    calc S.z * I.yi * S.t = S.z * (I.yi * S.t) := by group
      _ = S.z * (S.t * I.yi) := by rw [S.data.commute_t I.yi_mem.1]
      _ = S.t * (S.z * I.yi) := by rw [← mul_assoc, hzt, mul_assoc]
  have h3y : D.w3 w₁ * I.yi * (D.w3 w₁)⁻¹ = I.yi := by
    rw [hw3M.conj_yi]; simp [transCols, Inst.wV]
  have ht1 : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]
  have hyy : I.yi * I.yi = 1 := by rw [← pow_two, I.yi_sq]
  have hyt : I.yi * S.t = S.t * I.yi := (S.data.commute_t I.yi_mem.1)
  simp only [eL]
  rw [ht2, ht3]
  have e1 : (D.w2 w₁)⁻¹ * S.t = S.t * I.yi * (D.w2 w₁)⁻¹ := by
    rw [← h2t]; group
  have e2 : D.w3 w₁ * (S.t * I.yi) = S.t * S.z * D.w3 w₁ := by
    calc D.w3 w₁ * (S.t * I.yi) = (D.w3 w₁ * S.t * (D.w3 w₁)⁻¹) *
          (D.w3 w₁ * I.yi * (D.w3 w₁)⁻¹) * D.w3 w₁ := by group
      _ = S.t * (S.z * I.yi) * I.yi * D.w3 w₁ := by rw [h3t, h3y]
      _ = S.t * S.z * (I.yi * I.yi) * D.w3 w₁ := by group
      _ = S.t * S.z * D.w3 w₁ := by rw [hyy, mul_one]
  calc D.w3 w₁ * S.t * (w₁ * S.t * (D.w2 w₁ * S.t))⁻¹ =
      D.w3 w₁ * ((D.w2 w₁)⁻¹ * S.t⁻¹) * w₁⁻¹ := by group
    _ = D.w3 w₁ * ((D.w2 w₁)⁻¹ * S.t) * w₁⁻¹ := by
        rw [show S.t⁻¹ = S.t from inv_eq_of_mul_eq_one_right ht1]
    _ = D.w3 w₁ * (S.t * I.yi) * (D.w2 w₁)⁻¹ * w₁⁻¹ := by rw [e1]; group
    _ = S.t * S.z * D.w3 w₁ * (D.w2 w₁)⁻¹ * w₁⁻¹ := by rw [e2]
    _ = S.t * S.z * (D.w3 w₁ * (w₁ * D.w2 w₁)⁻¹) := by group
    _ = D.w3 w₁ * (w₁ * D.w2 w₁)⁻¹ * (S.t * S.z) := by
        have hE := D.eL_mem hw₁ hM
        simp only [eL] at hE
        rw [I.comm (mul_mem I.t_mem_E I.z_mem_E) hE]

omit D in
theorem conj_wV_transl {n : X} {a b : Fin 2} (h : I.Mat n (transCols a b)) (p q r : Fin 2) :
    n * I.wV (p, q, 0, r) * n⁻¹ = I.wV (p, q, 0, r) := by
  rw [h.conj, transCols_fix]

omit D in
theorem commute_wV_transl {n : X} {a b : Fin 2} (h : I.Mat n (transCols a b)) (p q r : Fin 2) :
    n * I.wV (p, q, 0, r) = I.wV (p, q, 0, r) * n := by
  calc n * I.wV (p, q, 0, r) = n * I.wV (p, q, 0, r) * n⁻¹ * n := by group
    _ = I.wV (p, q, 0, r) * n := by rw [conj_wV_transl h]

theorem w3_eq (he : D.eL w₁ = I.wV (p, q, 0, 0)) :
    D.w3 w₁ = I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁) := by
  rw [← he]; simp only [eL]; group

theorem commute_w₁_w₂ (hw₁ : w₁ ∈ D.Q) (hM : I.Mat w₁ (transCols 1 0))
    (he : D.eL w₁ = I.wV (p, q, 0, 0)) (hsq : w₁ ^ 2 = I.wV (a, 0, 0, 0)) :
    w₁ * D.w2 w₁ = D.w2 w₁ * w₁ := by
  have hw₂Q := D.w2_mem hw₁
  have hw₂M := D.w2_mat hM
  obtain ⟨c, hc⟩ : ∃ c, c = w₁ * D.w2 w₁ * w₁⁻¹ * (D.w2 w₁)⁻¹ := ⟨_, rfl⟩
  have hcQ : c ∈ D.Q := by
    rw [hc]; exact mul_mem (mul_mem (mul_mem hw₁ hw₂Q) (inv_mem hw₁)) (inv_mem hw₂Q)
  have hcM : I.Mat c bas := by
    have := ((hM.mul hw₂M).mul (hM.inv (transCols_sq 1 0))).mul (hw₂M.inv (transCols_sq 0 1))
    rwa [show comp (comp (comp (transCols 1 0) (transCols 0 1)) (transCols 1 0)) (transCols 0 1) =
      bas from funext transCols_comm, ← hc] at this
  obtain ⟨γ, hγ⟩ := I.eq_wV (D.mem_E hcQ hcM)
  have hsq₂ : (D.w2 w₁) ^ 2 = I.wV (lin dCols (a, 0, 0, 0)) := by
    rw [w2, conj_pow, hsq, D.d_mat.conj]
  have hsq₃ : (D.w3 w₁) ^ 2 = I.wV (lin dCols (lin dCols (a, 0, 0, 0))) := by
    rw [w3, conj_pow, hsq₂, D.d_mat.conj]
  have hecomm : I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁) = (w₁ * D.w2 w₁) * I.wV (p, q, 0, 0) :=
    (commute_wV_transl (D.w12_mat hM) p q 0).symm
  have hee : I.wV (p, q, 0, 0) * I.wV (p, q, 0, 0) = 1 := by
    rw [← pow_two]; exact I.sq_eq_one (I.wV_mem _)
  have h1 : (D.w3 w₁) ^ 2 = (w₁ * D.w2 w₁) ^ 2 := by
    rw [D.w3_eq he, pow_two, pow_two]
    calc I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁) * (I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁)) =
        I.wV (p, q, 0, 0) * ((w₁ * D.w2 w₁) * I.wV (p, q, 0, 0)) * (w₁ * D.w2 w₁) := by group
      _ = I.wV (p, q, 0, 0) * (I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁)) * (w₁ * D.w2 w₁) := by
          rw [← hecomm]
      _ = (I.wV (p, q, 0, 0) * I.wV (p, q, 0, 0)) * (w₁ * D.w2 w₁) * (w₁ * D.w2 w₁) := by group
      _ = w₁ * D.w2 w₁ * (w₁ * D.w2 w₁) := by rw [hee, one_mul]
  have h2 : (w₁ * D.w2 w₁) ^ 2 = (w₁ * c⁻¹ * w₁⁻¹) * w₁ ^ 2 * (D.w2 w₁) ^ 2 := by
    rw [hc]; simp only [pow_two]; group
  have hcinv : c⁻¹ = I.wV γ := by rw [hγ, wV_inv_self]
  have h3 : w₁ * c⁻¹ * w₁⁻¹ = I.wV (lin (transCols 1 0) γ) := by rw [hcinv, hM.conj]
  rw [h2, h3, hsq, hsq₂, ← I.wV_add, ← I.wV_add, hsq₃] at h1
  have hγ0 := (comm_relation γ a).resolve_left (by rw [I.wV_injective h1]; exact fun h => h rfl)
  have hc1 : c = 1 := by rw [hγ, hγ0, I.wV_zero]
  calc w₁ * D.w2 w₁ = c * D.w2 w₁ * w₁ := by rw [hc]; group
    _ = D.w2 w₁ * w₁ := by rw [hc1, one_mul]

theorem eL_eq (hw₁ : w₁ ∈ D.Q) (hM : I.Mat w₁ (transCols 1 0))
    (he : D.eL w₁ = I.wV (p, q, 0, 0)) (hsq : w₁ ^ 2 = I.wV (a, 0, 0, 0)) : p = a ∧ q = a := by
  have hcomm := D.commute_w₁_w₂ hw₁ hM he hsq
  have hw₂M := D.w2_mat hM
  have hsq₂ : (D.w2 w₁) ^ 2 = I.wV (lin dCols (a, 0, 0, 0)) := by
    rw [w2, conj_pow, hsq, D.d_mat.conj]
  have hd3 : D.d * D.w3 w₁ * D.d⁻¹ = w₁ := by
    have h := D.d_cube w₁ hw₁
    calc D.d * D.w3 w₁ * D.d⁻¹ = D.d ^ 3 * w₁ * (D.d ^ 3)⁻¹ := by
          simp only [w3, w2, pow_succ, pow_zero, one_mul]; group
      _ = w₁ := by rw [h]; group
  have hc2 : D.w2 w₁ * I.wV (p, q, 0, 0) = I.wV (p, q, 0, 0) * D.w2 w₁ :=
    commute_wV_transl hw₂M p q 0
  have key : D.d * D.w3 w₁ * D.d⁻¹ =
      I.wV (lin dCols (p, q, 0, 0)) * I.wV (p, q, 0, 0) * w₁ * (D.w2 w₁) ^ 2 := by
    have e1 : D.d * D.w3 w₁ * D.d⁻¹ =
        (D.d * I.wV (p, q, 0, 0) * D.d⁻¹) * D.w2 w₁ * D.w3 w₁ := by
      conv_lhs => rw [D.w3_eq he]
      calc D.d * (I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁)) * D.d⁻¹ =
          (D.d * I.wV (p, q, 0, 0) * D.d⁻¹) * (D.d * w₁ * D.d⁻¹) * (D.d * D.w2 w₁ * D.d⁻¹) := by
            group
        _ = (D.d * I.wV (p, q, 0, 0) * D.d⁻¹) * D.w2 w₁ * D.w3 w₁ := rfl
    rw [e1, D.d_mat.conj, D.w3_eq he]
    calc I.wV (lin dCols (p, q, 0, 0)) * D.w2 w₁ * (I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁)) =
        I.wV (lin dCols (p, q, 0, 0)) * (D.w2 w₁ * I.wV (p, q, 0, 0)) * w₁ * D.w2 w₁ := by group
      _ = I.wV (lin dCols (p, q, 0, 0)) * (I.wV (p, q, 0, 0) * D.w2 w₁) * w₁ * D.w2 w₁ := by
          rw [hc2]
      _ = I.wV (lin dCols (p, q, 0, 0)) * I.wV (p, q, 0, 0) * (D.w2 w₁ * w₁) * D.w2 w₁ := by
          group
      _ = I.wV (lin dCols (p, q, 0, 0)) * I.wV (p, q, 0, 0) * (w₁ * D.w2 w₁) * D.w2 w₁ := by
          rw [hcomm]
      _ = I.wV (lin dCols (p, q, 0, 0)) * I.wV (p, q, 0, 0) * w₁ * (D.w2 w₁) ^ 2 := by
          rw [pow_two]; group
  rw [hd3, hsq₂] at key
  rw [dCols_a, dCols_pq] at key
  have hcw : w₁ * I.wV (0, a, 0, 0) = I.wV (0, a, 0, 0) * w₁ := commute_wV_transl hM 0 a 0
  have e2 : w₁ = I.wV (q, p + q, 0, 0) * I.wV (p, q, 0, 0) * I.wV (0, a, 0, 0) * w₁ := by
    rw [mul_assoc (I.wV (q, p + q, 0, 0) * I.wV (p, q, 0, 0)) (I.wV (0, a, 0, 0)) w₁, ← hcw,
      ← mul_assoc]
    exact key
  have h1 : I.wV (q, p + q, 0, 0) * I.wV (p, q, 0, 0) * I.wV (0, a, 0, 0) = 1 := by
    calc I.wV (q, p + q, 0, 0) * I.wV (p, q, 0, 0) * I.wV (0, a, 0, 0) =
        I.wV (q, p + q, 0, 0) * I.wV (p, q, 0, 0) * I.wV (0, a, 0, 0) * w₁ * w₁⁻¹ := by group
      _ = w₁ * w₁⁻¹ := by rw [← e2]
      _ = 1 := mul_inv_cancel _
  rw [← I.wV_add, ← I.wV_add, ← I.wV_zero] at h1
  have h2 := I.wV_injective h1
  rw [← dCols_a, ← dCols_pq] at h2
  rcases d_relation p q a with h | h
  · exact absurd h2 h
  · exact h

theorem d_w2 (hw₁ : w₁ ∈ D.Q) (hM : I.Mat w₁ (transCols 1 0))
    (he : D.eL w₁ = I.wV (p, q, 0, 0)) (hsq : w₁ ^ 2 = I.wV (a, 0, 0, 0)) :
    D.d * D.w2 w₁ * D.d⁻¹ = (D.w2 w₁ * w₁)⁻¹ := by
  obtain ⟨hp, hq⟩ := D.eL_eq hw₁ hM he hsq
  rw [hp, hq] at he
  have hw₂M := D.w2_mat hM
  have hsq₂ : (D.w2 w₁) ^ 2 = I.wV (0, a, 0, 0) := by
    rw [w2, conj_pow, hsq, D.d_mat.conj, dCols_a]
  have hinv : ∀ {g : X} {v : V4}, g ^ 2 = I.wV v → g⁻¹ = g * I.wV v := by
    intro g v h
    have h4 : g ^ 2 * g ^ 2 = 1 := by rw [h, ← pow_two]; exact I.sq_eq_one (I.wV_mem _)
    rw [← h]
    calc g⁻¹ = g⁻¹ * (g ^ 2 * g ^ 2) := by rw [h4, mul_one]
      _ = g * g ^ 2 := by simp only [pow_two]; group
  have hi₁ : w₁⁻¹ = w₁ * I.wV (a, 0, 0, 0) := hinv hsq
  have hi₂ : (D.w2 w₁)⁻¹ = D.w2 w₁ * I.wV (0, a, 0, 0) := hinv hsq₂
  have hc : I.wV (a, 0, 0, 0) * D.w2 w₁ = D.w2 w₁ * I.wV (a, 0, 0, 0) :=
    (commute_wV_transl hw₂M a 0 0).symm
  have hc1 : I.wV (a, a, 0, 0) * w₁ = w₁ * I.wV (a, a, 0, 0) :=
    (commute_wV_transl hM a a 0).symm
  have hc2 : I.wV (a, a, 0, 0) * D.w2 w₁ = D.w2 w₁ * I.wV (a, a, 0, 0) :=
    (commute_wV_transl hw₂M a a 0).symm
  have hadd : I.wV (a, 0, 0, 0) * I.wV (0, a, 0, 0) = I.wV (a, a, 0, 0) := by
    rw [← I.wV_add]; simp [addV]
  have hz1 : I.wV (a, 0, 0, 0) * I.wV (a, 0, 0, 0) = 1 := by
    rw [← pow_two]; exact I.sq_eq_one (I.wV_mem _)
  show D.w3 w₁ = _
  rw [D.w3_eq he, mul_inv_rev, hi₁, hi₂]
  calc I.wV (a, a, 0, 0) * (w₁ * D.w2 w₁) = w₁ * D.w2 w₁ * I.wV (a, a, 0, 0) := by
        rw [← mul_assoc, hc1, mul_assoc, hc2, ← mul_assoc]
    _ = w₁ * (D.w2 w₁ * I.wV (a, 0, 0, 0)) * I.wV (0, a, 0, 0) := by
        rw [← hadd]; group
    _ = w₁ * (I.wV (a, 0, 0, 0) * D.w2 w₁) * I.wV (0, a, 0, 0) := by rw [hc]
    _ = w₁ * I.wV (a, 0, 0, 0) * (D.w2 w₁ * I.wV (0, a, 0, 0)) := by group

end Inst.QD

end A7Base

end CFSG.ComponentClassification.HSFLit
