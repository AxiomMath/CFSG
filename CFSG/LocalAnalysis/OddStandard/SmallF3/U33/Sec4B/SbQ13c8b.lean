module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c8a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13c_t_conj_f (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * (t * lam) * t⁻¹ = t * lam := by
  calc t * (t * lam) * t⁻¹ = (t * t) * lam * t⁻¹ := by group
    _ = lam * t⁻¹ := by rw [q13a_t_mul_self h, one_mul]
    _ = lam * t := by rw [inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)]
    _ = t * lam := (q13a_t_comm h).1.symm

private theorem q13c_t_comm_f (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * (t * lam) = (t * lam) * t := by
  have hconj := q13c_t_conj_f h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)
  rw [htinv] at hconj
  calc t * (t * lam) = t * (t * lam) * (t * t) := by rw [q13a_t_mul_self h, mul_one]
    _ = (t * (t * lam) * t) * t := by group
    _ = (t * lam) * t := by rw [hconj]

private theorem q13c_lam_conj_f (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * (t * lam) * lam⁻¹ = t * lam := by
  calc lam * (t * lam) * lam⁻¹ = (lam * t) * (lam * lam⁻¹) := by group
    _ = lam * t := by rw [mul_inv_cancel, mul_one]
    _ = t * lam := (q13a_t_comm h).1.symm

private theorem q13c_lam_comm_f (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * (t * lam) = (t * lam) * lam := by
  have hconj := q13c_lam_conj_f h
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (q13a_lam_mul_self h)
  rw [hlinv] at hconj
  calc lam * (t * lam) = lam * (t * lam) * (lam * lam) := by rw [q13a_lam_mul_self h, mul_one]
    _ = (lam * (t * lam) * lam) * lam := by group
    _ = (t * lam) * lam := by rw [hconj]

private theorem q13c_om_conj_f_I (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : lam * om * lam⁻¹ = om) :
    om * (t * lam) * om⁻¹ = (t * lam) * tau := by
  have hcomm : lam * om = om * lam := by
    calc lam * om = (lam * om * lam⁻¹) * lam := by group
      _ = om * lam := by rw [hI]
  have hconj_om_lam : om * lam * om⁻¹ = lam := by
    calc om * lam * om⁻¹ = (lam * om) * om⁻¹ := by rw [← hcomm]
      _ = lam := by group
  calc om * (t * lam) * om⁻¹ = (om * t * om⁻¹) * (om * lam * om⁻¹) := by group
    _ = (t * tau) * lam := by rw [h.t_om, hconj_om_lam]
    _ = (t * lam) * tau := by
          calc (t * tau) * lam = t * (tau * lam) := by group
            _ = t * (lam * tau) := by rw [← q13c_lam_cent_tau h]
            _ = (t * lam) * tau := by group

private theorem q13c_om_conj_f_II (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : lam * om * lam⁻¹ = om * tau) :
    om * (t * lam) * om⁻¹ = t * lam := by
  have hconj_om_lam : om * lam * om⁻¹ = tau * lam := by
    have h2 : lam * om = om * tau * lam := by
      calc lam * om = (lam * om * lam⁻¹) * lam := by group
        _ = (om * tau) * lam := by rw [hII]
    have h1 : om * lam * om = tau * lam := by
      calc om * lam * om = om * (lam * om) := by group
        _ = om * (om * tau * lam) := by rw [h2]
        _ = tau * lam := by
              calc om * (om * tau * lam) = (om * om) * tau * lam := by group
                _ = tau * lam := by rw [h.om_sq, one_mul]
    rw [inv_eq_of_mul_eq_one_right h.om_sq]; exact h1
  calc om * (t * lam) * om⁻¹ = (om * t * om⁻¹) * (om * lam * om⁻¹) := by group
    _ = (t * tau) * (tau * lam) := by rw [h.t_om, hconj_om_lam]
    _ = t * lam := by
          calc (t * tau) * (tau * lam) = t * (tau * tau) * lam := by group
            _ = t * lam := by rw [q13a_tau_mul_self h, mul_one]

private theorem q13c_om_conj_f (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * (t * lam) * om⁻¹ = t * lam ∨
      om * (t * lam) * om⁻¹ = (t * lam) * tau := by
  rcases q13a_lam_om h with hI | hII
  · exact Or.inr (q13c_om_conj_f_I h hI)
  · exact Or.inl (q13c_om_conj_f_II h hII)

private theorem q13c_mul_tau_comm {a b tau : G}
    (ha : a * tau = tau * a) (hb : b * tau = tau * b) :
    (a * b) * tau = tau * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

private theorem q13c_conj_mul_aux {a f tau : G} (ha : a * tau = tau * a) :
    a * (f * tau) * a⁻¹ = (a * f * a⁻¹) * tau := by
  have hconj : a * tau * a⁻¹ = tau := by rw [ha, mul_assoc, mul_inv_cancel, mul_one]
  calc a * (f * tau) * a⁻¹ = (a * f * a⁻¹) * (a * tau * a⁻¹) := by group
    _ = (a * f * a⁻¹) * tau := by rw [hconj]

private theorem q13c_inv_tau_comm {a tau : G} (ha : a * tau = tau * a)
    (htau2 : tau * tau = 1) : a⁻¹ * tau = tau * a⁻¹ := by
  have h1 : (a * tau)⁻¹ = (tau * a)⁻¹ := by rw [ha]
  rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right htau2] at h1
  exact h1.symm

private theorem q13c_E_conj_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ closure {t, om} ⊔ zpowers lam,
      n * tau = tau * n ∧
        (n * (t * lam) * n⁻¹ = t * lam ∨
          n * (t * lam) * n⁻¹ = (t * lam) * tau) := by
  have hE : closure {t, om} ⊔ zpowers lam = closure ({t, om} ∪ {lam} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  rw [hE]
  let P : G → Prop := fun n => n * tau = tau * n ∧
      (n * (t * lam) * n⁻¹ = t * lam ∨ n * (t * lam) * n⁻¹ = (t * lam) * tau)
  let K : Subgroup G :=
    { carrier := {n | P n}
      mul_mem' := by
        intro a b ha hb
        exact ⟨q13c_mul_tau_comm ha.1 hb.1, by
          have hconj : (a * b) * (t * lam) * (a * b)⁻¹ =
              a * (b * (t * lam) * b⁻¹) * a⁻¹ := by group
          rw [hconj]
          rcases hb.2 with hb' | hb'
          · rw [hb']; exact ha.2
          · rw [hb', q13c_conj_mul_aux ha.1]
            rcases ha.2 with ha' | ha'
            · right; rw [ha']
            · left; rw [ha']
              calc ((t * lam) * tau) * tau = (t * lam) * (tau * tau) := by group
                _ = t * lam := by rw [q13a_tau_mul_self h, mul_one]⟩
      one_mem' := ⟨by group, Or.inl (by group)⟩
      inv_mem' := by
        intro a ha
        exact ⟨q13c_inv_tau_comm ha.1 (q13a_tau_mul_self h), by
          rcases ha.2 with ha' | ha'
          · left
            calc a⁻¹ * (t * lam) * a⁻¹⁻¹ = a⁻¹ * (a * (t * lam) * a⁻¹) * a⁻¹⁻¹ := by
                  rw [ha']
              _ = t * lam := by group
          · right
            have hinv : a⁻¹ * tau = tau * a⁻¹ :=
              q13c_inv_tau_comm ha.1 (q13a_tau_mul_self h)
            have h2 : a⁻¹ * ((t * lam) * tau) * a⁻¹⁻¹ =
                (a⁻¹ * (t * lam) * a⁻¹⁻¹) * tau :=
              q13c_conj_mul_aux (a := a⁻¹) hinv
            have h1 : a⁻¹ * ((t * lam) * tau) * a⁻¹⁻¹ = t * lam := by
              calc a⁻¹ * ((t * lam) * tau) * a⁻¹⁻¹ =
                    a⁻¹ * (a * (t * lam) * a⁻¹) * a⁻¹⁻¹ := by rw [ha']
                _ = t * lam := by group
            have h3 : (a⁻¹ * (t * lam) * a⁻¹⁻¹) * tau = t * lam := h2.symm.trans h1
            calc a⁻¹ * (t * lam) * a⁻¹⁻¹ =
                  (a⁻¹ * (t * lam) * a⁻¹⁻¹) * (tau * tau) := by
                    rw [q13a_tau_mul_self h, mul_one]
              _ = ((a⁻¹ * (t * lam) * a⁻¹⁻¹) * tau) * tau := by group
              _ = (t * lam) * tau := by rw [h3]⟩ }
  have hgen : ({t, om} ∪ {lam} : Set G) ⊆ K := by
    intro x hx
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl) | rfl
    · exact ⟨(q13a_t_comm h).2.2, Or.inl (q13c_t_conj_f h)⟩
    · exact ⟨(q13a_om_comm h).1, q13c_om_conj_f h⟩
    · exact ⟨q13c_lam_cent_tau h, Or.inl (q13c_lam_conj_f h)⟩
  intro n hn
  exact (Subgroup.closure_le (K := K)).mpr hgen hn

theorem q13c_E_conj_tlam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ closure {t, om} ⊔ zpowers lam,
      n * (t * lam) * n⁻¹ = t * lam ∨ n * (t * lam) * n⁻¹ = (t * lam) * tau :=
  fun n hn => (q13c_E_conj_aux h n hn).2

theorem q13c_card_CE_ge (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    8 ≤ Nat.card ↥((closure {t, om} ⊔ zpowers lam) ⊓ centralizer ({t * lam} : Set G)) := by
  have h1 := q13b_card_le_two_mul (H := closure {t, om} ⊔ zpowers lam)
    (f := t * lam) (z := tau) (q13c_E_conj_tlam h)
  have h2 : Nat.card ↥(closure {t, om} ⊔ zpowers lam) = 16 := q13c_card_E h
  rw [h2] at h1
  omega

private theorem q13c_card_mul_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    8 * Nat.card ↥((closure {t, om} ⊔ zpowers lam) ⊓ centralizer ({t * lam} : Set G)) ≤
      Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) := by
  let C : Subgroup G := centralizer ({t * lam} : Set G)
  let A₀ : Subgroup G := ctxQ t tau x₁ x₂ rho ⊓ C
  let CE : Subgroup G := (closure {t, om} ⊔ zpowers lam) ⊓ C
  have hcardA : Nat.card ↥A₀ = 8 := q13a_card_CQ_tlam h
  have hnorm : ∀ k ∈ CE, ∀ a ∈ A₀, k * a * k⁻¹ ∈ A₀ := by
    intro k hk a ha
    obtain ⟨hkE, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨haQ, haC⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (q13b_Q_normal_U h).2 k (q13c_E_le_U h hkE) a haQ
    · exact C.mul_mem (C.mul_mem hkC haC) (C.inv_mem hkC)
  have hdis : A₀ ⊓ CE = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxCE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxQ, -⟩ := Subgroup.mem_inf.mp hxA
    obtain ⟨hxE, -⟩ := Subgroup.mem_inf.mp hxCE
    exact q13c_E_inf_Q h x hxQ hxE
  have hcard : Nat.card ↥(A₀ ⊔ CE) = Nat.card ↥A₀ * Nat.card ↥CE :=
    card_sup_eq_mul hnorm hdis
  have hle : A₀ ⊔ CE ≤ ctxU t tau x₁ x₂ lam ⊓ C := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(q13b_Q_normal_U h).1 hxQ, hxC⟩
    · intro x hx
      obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨q13c_E_le_U h hxE, hxC⟩
  have hcardle := Subgroup.card_le_of_le hle
  calc 8 * Nat.card ↥CE = Nat.card ↥A₀ * Nat.card ↥CE := by rw [hcardA]
    _ = Nat.card ↥(A₀ ⊔ CE) := hcard.symm
    _ ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ C) := hcardle

theorem q13c_card_CU_ge (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    64 ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) := by
  have h1 := q13c_card_CE_ge h
  have h2 := q13c_card_mul_le h
  have h3 : 8 * 8 ≤ 8 * Nat.card ↥((closure {t, om} ⊔ zpowers lam) ⊓
      centralizer ({t * lam} : Set G)) := Nat.mul_le_mul_left 8 h1
  calc 64 = 8 * 8 := by norm_num
    _ ≤ 8 * Nat.card ↥((closure {t, om} ⊔ zpowers lam) ⊓
          centralizer ({t * lam} : Set G)) := h3
    _ ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) := h2

theorem q13c_E_cent_II (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : lam * om * lam⁻¹ = om * tau) :
    closure {t, om} ⊔ zpowers lam ≤ centralizer ({t * lam} : Set G) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (q13c_t_comm_f h)
    · rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have hconj := q13c_om_conj_f_II h hII
        rw [inv_eq_of_mul_eq_one_right h.om_sq] at hconj
        calc om * (t * lam) = om * (t * lam) * (om * om) := by rw [h.om_sq, mul_one]
          _ = (om * (t * lam) * om) * om := by group
          _ = (t * lam) * om := by rw [hconj])
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (q13c_lam_comm_f h))

theorem q13c_card_CU_ge_II (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : lam * om * lam⁻¹ = om * tau) :
    128 ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) := by
  have hcent := q13c_E_cent_II h hII
  have hE : (closure {t, om} ⊔ zpowers lam) ⊓ centralizer ({t * lam} : Set G) =
      closure {t, om} ⊔ zpowers lam := inf_eq_left.mpr hcent
  have hcardE : Nat.card ↥((closure {t, om} ⊔ zpowers lam) ⊓
      centralizer ({t * lam} : Set G)) = 16 := by rw [hE, q13c_card_E h]
  have h2 := q13c_card_mul_le h
  rw [hcardE] at h2
  calc 128 = 8 * 16 := by norm_num
    _ ≤ Nat.card ↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)) := h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
