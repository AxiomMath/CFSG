module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl1
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma p12a_hyp_t_sq (h : Hyp G t L) : t * t = 1 := by
  have h1 := pow_orderOf_eq_one t
  rw [h.ord_t] at h1
  simpa [pow_two] using h1

private lemma p12a_hyp_t_not_mem_L (h : Hyp G t L) : t ∉ L := by
  intro htL
  have hmem : t ∈ twoCore t ⊓ L := ⟨h.mem_twoCore, htL⟩
  rw [h.twoCore_inf, Subgroup.mem_bot] at hmem
  have h2 : orderOf t = 1 := by rw [hmem, orderOf_one]
  rw [h.ord_t] at h2
  omega

private lemma p12a_x1_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) : x₁ ∈ L := by
  have hmem : x₁ ∈ S ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.2

private lemma p12a_x2_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) : x₂ ∈ L := by
  have hmem : x₂ ∈ S ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.2

private lemma p12a_y_z_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) :
    x₁ ^ 2 ∈ L ∧ (x₁ * x₂) ^ 2 ∈ L :=
  ⟨Subgroup.pow_mem L (p12a_x1_mem_L h) 2,
    Subgroup.pow_mem L (Subgroup.mul_mem L (p12a_x1_mem_L h) (p12a_x2_mem_L h)) 2⟩

private lemma p12a_fourGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : fourGrp x₁ x₂ ≤ L := by
  rw [fourGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (p12a_y_z_mem_L h).1
  · exact (p12a_y_z_mem_L h).2

private lemma p12a_ctxN_le_ctxX (t tau x₁ x₂ : G) :
    ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxN, ctxX]
  refine (Subgroup.closure_le (K := closure {t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2})).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private lemma p12a_mul_t_mul_t (t x y : G) (ht2 : t * t = 1) (hxt : x * t = t * x) :
    (t * x) * (t * y) = x * y := by
  calc (t * x) * (t * y) = ((t * x) * t) * y := by rw [← mul_assoc]
    _ = (t * (x * t)) * y := by rw [mul_assoc t x t]
    _ = (t * (t * x)) * y := by rw [hxt]
    _ = ((t * t) * x) * y := by rw [← mul_assoc t t x]
    _ = x * y := by rw [ht2, one_mul]

private lemma p12a_mul_mul_comm (t x y : G) (h : t * x = x * t) :
    t * (x * y) = x * (t * y) := by
  calc t * (x * y) = (t * x) * y := by rw [mul_assoc]
    _ = (x * t) * y := by rw [h]
    _ = x * (t * y) := by rw [mul_assoc]

private lemma p12a_mem_of_mem_pCoreOf {H : Subgroup G} {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 H) : x ∈ H :=
  Subgroup.map_subtype_le (CFSG.pCore 2 H) hx

private lemma p12a_wreath_x1_sq (h : WreathRel x₁ x₂ lam) : x₁ ^ 2 * x₁ ^ 2 = 1 := by
  have h4 : x₁ ^ 4 = 1 := by simpa [h.ord_x₁] using pow_orderOf_eq_one x₁
  rw [← pow_two, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, h4]

private lemma p12a_wreath_x1x2_sq (h : WreathRel x₁ x₂ lam) :
    (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
  have h4 : (x₁ * x₂) ^ 4 = 1 := by
    rw [(show Commute x₁ x₂ from h.comm).mul_pow]
    rw [show x₁ ^ 4 = 1 from by simpa [h.ord_x₁] using pow_orderOf_eq_one x₁,
      show x₂ ^ 4 = 1 from by simpa [h.ord_x₂] using pow_orderOf_eq_one x₂, mul_one]
  rw [← pow_two, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, h4]

private lemma p12a_t_comm_tau (hc : Ctx4 t L S x₁ x₂ lam rho tau) : t * tau = tau * t := by
  have h : tau ∈ invCent t := hc.le_invCent hc.tau_mem
  exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

private lemma p12a_t_comm_mem_L (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a : G} (ha : a ∈ L) :
    t * a = a * t :=
  (Subgroup.mem_centralizer_iff.mp hc.hyp.mem_centralizer a ha).symm

private lemma p12a_tau_inv_x1x2 (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have h12 : x₁⁻¹ * x₂⁻¹ = x₂⁻¹ * x₁⁻¹ := by
    have h := congrArg Inv.inv hc.wreath.comm
    simpa only [mul_inv_rev] using h.symm
  calc tau * (x₁ * x₂) * tau⁻¹ = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [hc.tau_x₁, hc.tau_x₂]
    _ = (x₁ * x₂)⁻¹ := by rw [mul_inv_rev, h12]

private lemma p12a_conj_sq_eq_self (a tau : G) (hinv : tau * a * tau⁻¹ = a⁻¹)
    (h4 : a ^ 4 = 1) : tau * a ^ 2 * tau⁻¹ = a ^ 2 := by
  have hconj : tau * a ^ 2 * tau⁻¹ = (tau * a * tau⁻¹) ^ 2 := conj_pow.symm
  rw [hconj, hinv]
  have hsq : a ^ 2 * a ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, h4]
  rw [inv_pow, inv_eq_of_mul_eq_one_right hsq]

private lemma p12a_tau_comm_x1sq (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    tau * x₁ ^ 2 = x₁ ^ 2 * tau := by
  have h4 : x₁ ^ 4 = 1 := by simpa [hc.wreath.ord_x₁] using pow_orderOf_eq_one x₁
  have hconj : tau * x₁ ^ 2 * tau⁻¹ = x₁ ^ 2 := p12a_conj_sq_eq_self x₁ tau hc.tau_x₁ h4
  calc tau * x₁ ^ 2 = (tau * x₁ ^ 2 * tau⁻¹) * tau := by
        rw [mul_assoc (tau * x₁ ^ 2) tau⁻¹ tau, inv_mul_cancel, mul_one]
    _ = x₁ ^ 2 * tau := by rw [hconj]

private lemma p12a_tau_comm_x1x2sq (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := by
  have h4 : (x₁ * x₂) ^ 4 = 1 := by
    rw [(show Commute x₁ x₂ from hc.wreath.comm).mul_pow]
    rw [show x₁ ^ 4 = 1 from by simpa [hc.wreath.ord_x₁] using pow_orderOf_eq_one x₁,
      show x₂ ^ 4 = 1 from by simpa [hc.wreath.ord_x₂] using pow_orderOf_eq_one x₂, mul_one]
  have hconj : tau * (x₁ * x₂) ^ 2 * tau⁻¹ = (x₁ * x₂) ^ 2 :=
    p12a_conj_sq_eq_self (x₁ * x₂) tau (p12a_tau_inv_x1x2 hc) h4
  calc tau * (x₁ * x₂) ^ 2 = (tau * (x₁ * x₂) ^ 2 * tau⁻¹) * tau := by
        rw [mul_assoc (tau * (x₁ * x₂) ^ 2) tau⁻¹ tau, inv_mul_cancel, mul_one]
    _ = (x₁ * x₂) ^ 2 * tau := by rw [hconj]

private lemma p12a_x1sq_comm_x1x2sq (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
  hc.m2_PT_attained.1.comm (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

private lemma p12a_ctxX_isElemAbelian (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) := by
  rw [ctxX]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    have hy : x₁ ^ 2 ∈ L := (p12a_y_z_mem_L hc.toCtx0).1
    have hz : (x₁ * x₂) ^ 2 ∈ L := (p12a_y_z_mem_L hc.toCtx0).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
        | rfl
        | exact p12a_t_comm_tau hc
        | exact (p12a_t_comm_tau hc).symm
        | exact p12a_t_comm_mem_L hc hy
        | exact (p12a_t_comm_mem_L hc hy).symm
        | exact p12a_t_comm_mem_L hc hz
        | exact (p12a_t_comm_mem_L hc hz).symm
        | exact p12a_tau_comm_x1sq hc
        | exact (p12a_tau_comm_x1sq hc).symm
        | exact p12a_tau_comm_x1x2sq hc
        | exact (p12a_tau_comm_x1x2sq hc).symm
        | exact p12a_x1sq_comm_x1x2sq hc
        | exact (p12a_x1sq_comm_x1x2sq hc).symm
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · simpa [pow_two] using p12a_hyp_t_sq hc.hyp
    · exact hc.l44.1
    · simpa [pow_two] using p12a_wreath_x1_sq hc.wreath
    · simpa [pow_two] using p12a_wreath_x1x2_sq hc.wreath

private lemma p12a_ctxN_isElemAbelian (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    CFSG.Open.IsElemAbelian 2 (ctxN tau x₁ x₂) :=
  (p12a_ctxX_isElemAbelian hc).mono (p12a_ctxN_le_ctxX t tau x₁ x₂)

theorem l12_X_cases (hc : Ctx4 t L S x₁ x₂ lam rho tau) {x : G} (hx : x ∈ ctxX t tau x₁ x₂) :
    x ∈ ctxN tau x₁ x₂ ∨ t * x ∈ ctxN tau x₁ x₂ := by
  have hE : CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) := p12a_ctxX_isElemAbelian hc
  have hcomm : ∀ a ∈ ctxX t tau x₁ x₂, ∀ b ∈ ctxX t tau x₁ x₂, a * b = b * a :=
    fun a ha b hb => hE.comm ha hb
  have hsq : ∀ a ∈ ctxX t tau x₁ x₂, a * a = 1 := fun a ha => hE.mul_self_eq_one ha
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have ht2 : t * t = 1 := p12a_hyp_t_sq hc.hyp
  rw [ctxX] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => x ∈ ctxN tau x₁ x₂ ∨ t * x ∈ ctxN tau x₁ x₂) ?_ ?_ ?_ ?_ hx
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · right; rw [ht2]; exact one_mem _
    · left; exact Subgroup.subset_closure (by simp)
    · left; exact Subgroup.subset_closure (by simp)
    · left; exact Subgroup.subset_closure (by simp)
  · left; exact one_mem _
  · intro a b ha hb pa pb
    have haX : a ∈ ctxX t tau x₁ x₂ := ha
    have hbX : b ∈ ctxX t tau x₁ x₂ := hb
    have hcomm_ta : t * a = a * t := hcomm t htX a haX
    rcases pa with haN | htaN <;> rcases pb with hbN | htbN
    · left; exact mul_mem haN hbN
    · right
      have h : t * (a * b) = a * (t * b) := p12a_mul_mul_comm t a b hcomm_ta
      rw [h]; exact mul_mem haN htbN
    · right
      have h : t * (a * b) = (t * a) * b := (mul_assoc t a b).symm
      rw [h]; exact mul_mem htaN hbN
    · left
      have h : (t * a) * (t * b) = a * b := p12a_mul_t_mul_t t a b ht2 hcomm_ta.symm
      rw [← h]; exact mul_mem htaN htbN
  · intro a ha pa
    have haX : a ∈ ctxX t tau x₁ x₂ := ha
    have hsq_a : a * a = 1 := hsq a haX
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq_a
    rw [hinv]; exact pa

theorem l12_N_cases (hc : Ctx4 t L S x₁ x₂ lam rho tau) {n : G} (hn : n ∈ ctxN tau x₁ x₂) :
    n ∈ fourGrp x₁ x₂ ∨ tau * n ∈ fourGrp x₁ x₂ := by
  have hX : CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) := p12a_ctxX_isElemAbelian hc
  have hN : CFSG.Open.IsElemAbelian 2 (ctxN tau x₁ x₂) := p12a_ctxN_isElemAbelian hc
  have hNleX : ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := p12a_ctxN_le_ctxX t tau x₁ x₂
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  rw [ctxN] at hn
  refine Subgroup.closure_induction
    (p := fun x _ => x ∈ fourGrp x₁ x₂ ∨ tau * x ∈ fourGrp x₁ x₂) ?_ ?_ ?_ ?_ hn
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · right; rw [htau2]; exact one_mem _
    · left; exact Subgroup.subset_closure (by simp)
    · left; exact Subgroup.subset_closure (by simp)
  · left; exact one_mem _
  · intro a b ha hb pa pb
    have haX : a ∈ ctxX t tau x₁ x₂ := hNleX ha
    have hbX : b ∈ ctxX t tau x₁ x₂ := hNleX hb
    have hcomm_ta : tau * a = a * tau := hX.comm htauX haX
    rcases pa with haV | htaV <;> rcases pb with hbV | htbV
    · left; exact mul_mem haV hbV
    · right
      have h : tau * (a * b) = a * (tau * b) := p12a_mul_mul_comm tau a b hcomm_ta
      rw [h]; exact mul_mem haV htbV
    · right
      have h : tau * (a * b) = (tau * a) * b := (mul_assoc tau a b).symm
      rw [h]; exact mul_mem htaV hbV
    · left
      have h : (tau * a) * (tau * b) = a * b :=
        p12a_mul_t_mul_t tau a b htau2 hcomm_ta.symm
      rw [← h]; exact mul_mem htaV htbV
  · intro a ha pa
    have haX : a ∈ ctxX t tau x₁ x₂ := hNleX ha
    have hsq_a : a * a = 1 := hN.mul_self_eq_one ha
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq_a
    rw [hinv]; exact pa

theorem l12_t_not_mem_N (hc : Ctx4 t L S x₁ x₂ lam rho tau) : t ∉ ctxN tau x₁ x₂ := by
  intro htN
  rcases l12_N_cases hc htN with htV | htauV
  · exact p12a_hyp_t_not_mem_L hc.hyp (p12a_fourGrp_le_L hc.toCtx0 htV)
  · apply hc.tau_not_mem
    have h1 : tau * t ∈ L := p12a_fourGrp_le_L hc.toCtx0 htauV
    have h2 : t⁻¹ ∈ twoCore t := inv_mem hc.hyp.mem_twoCore
    have hcalc : (tau * t) * t⁻¹ = tau := by group
    rw [← hcalc]
    exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)

theorem l12_tau_not_mem_V (hc : Ctx4 t L S x₁ x₂ lam rho tau) : tau ∉ fourGrp x₁ x₂ := by
  intro hV
  exact hc.tau_not_mem (Subgroup.mem_sup_right (p12a_fourGrp_le_L hc.toCtx0 hV))

theorem l12_sq_mem_N (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a : G} (ha : a ∈ ctxR t tau x₁ x₂) :
    a ^ 2 ∈ ctxN tau x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have ht2 : t * t = 1 := p12a_hyp_t_sq hc.hyp
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  by_cases hN : a ^ 2 ∈ ctxN tau x₁ x₂
  · exact hN
  · exfalso
    have haX : a ^ 2 ∈ ctxX t tau x₁ x₂ := hc.R_quot.1 a ha
    rcases l12_X_cases hc4 haX with h1 | h1
    · exact hN h1
    · rcases l12_N_cases hc4 h1 with hnV | htnV
      · have hmem : a ^ 2 ∈ conjIn (ctxM t tau x₁ x₂) t := by
          rw [hc.tM]
          left
          exact ⟨t * a ^ 2, hnV, by
            change t * (t * a ^ 2) = a ^ 2
            rw [← mul_assoc, ht2, one_mul]⟩
        rcases hmem with ⟨m, _, hm⟩
        have haa : a * a = m * t * m⁻¹ := by rw [← pow_two, hm]
        have hsq : (m⁻¹ * a * m) * (m⁻¹ * a * m) = t := by
          calc (m⁻¹ * a * m) * (m⁻¹ * a * m) = m⁻¹ * (a * a) * m := by group
            _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [haa]
            _ = t := by group
        exact (hc.l44.2 (m⁻¹ * a * m)) (by rw [pow_two]; exact hsq)
      · have hmem : a ^ 2 ∈ conjIn (ctxM t tau x₁ x₂) t := by
          rw [hc.tM]
          right
          exact ⟨tau * (t * a ^ 2), htnV, by
            change (t * tau) * (tau * (t * a ^ 2)) = a ^ 2
            rw [mul_assoc t tau (tau * (t * a ^ 2)),
              ← mul_assoc tau tau (t * a ^ 2), htau2, one_mul,
              ← mul_assoc t t (a ^ 2), ht2, one_mul]⟩
        rcases hmem with ⟨m, _, hm⟩
        have haa : a * a = m * t * m⁻¹ := by rw [← pow_two, hm]
        have hsq : (m⁻¹ * a * m) * (m⁻¹ * a * m) = t := by
          calc (m⁻¹ * a * m) * (m⁻¹ * a * m) = m⁻¹ * (a * a) * m := by group
            _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [haa]
            _ = t := by group
        exact (hc.l44.2 (m⁻¹ * a * m)) (by rw [pow_two]; exact hsq)

theorem l12_comm_mem_N (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxR t tau x₁ x₂) (hb : b ∈ ctxR t tau x₁ x₂) :
    a * b * a⁻¹ * b⁻¹ ∈ ctxN tau x₁ x₂ := by
  have ha2 : a * a ∈ ctxN tau x₁ x₂ := by simpa [pow_two] using l12_sq_mem_N hc ha
  have hb2 : b * b ∈ ctxN tau x₁ x₂ := by simpa [pow_two] using l12_sq_mem_N hc hb
  have hab2 : (a * b) * (a * b) ∈ ctxN tau x₁ x₂ := by
    simpa [pow_two] using l12_sq_mem_N hc (mul_mem ha hb)
  have ha2inv : (a * a)⁻¹ ∈ ctxN tau x₁ x₂ := inv_mem ha2
  have hb2inv : (b * b)⁻¹ ∈ ctxN tau x₁ x₂ := inv_mem hb2
  have hbM : b ∈ ctxM t tau x₁ x₂ := p12a_mem_of_mem_pCoreOf (hc.R_le_O hb)
  have hbMinv : b⁻¹ ∈ ctxM t tau x₁ x₂ := inv_mem hbM
  have hconj : b⁻¹ * (a * a)⁻¹ * b ∈ ctxN tau x₁ x₂ := by
    simpa only [inv_inv] using hc.normal_N.2 b⁻¹ hbMinv ((a * a)⁻¹) ha2inv
  have hprod : (a * b) * (a * b) * (b⁻¹ * (a * a)⁻¹ * b) * (b * b)⁻¹ ∈
      ctxN tau x₁ x₂ :=
    mul_mem (mul_mem hab2 hconj) hb2inv
  rw [show a * b * a⁻¹ * b⁻¹ =
      (a * b) * (a * b) * (b⁻¹ * (a * a)⁻¹ * b) * (b * b)⁻¹ by group]
  exact hprod

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
