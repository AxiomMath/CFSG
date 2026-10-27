module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NTri
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NC

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem two_q_qd : ∀ p r : Fin 2, addV (lin (M2C 1) (p, 0, 0, r)) (0, p, 0, r) =
    addV (lin (M1C 1) (0, p, 0, r)) (p, 0, 0, r) := by decide

theorem two_qdd : ∀ p r e4 : Fin 2, addV (addV (lin (M2C 1) (p, 0, 0, r)) (0, p, 0, r))
    (0, 0, 0, p + e4 + r) = addV (0, 0, 0, e4) (lin dCols (0, p, 0, r)) := by decide

theorem dCols_p0r : ∀ p r : Fin 2, lin dCols (p, 0, 0, r) = (0, p, 0, r) := by decide

theorem sq_yi : ∀ e : V4, e.2.2.1 = 0 → addV (lin (M1C 1) e) e = (0, 0, 0, 0) → e.2.1 = 0 := by
  decide

theorem vC_ne_Q0 : ∀ ε a b : Fin 2, vC ≠ comp (pw (M2C ε) b) (pw (M1C ε) a) := by decide

theorem gC_col_two : ∀ ε a b c : Fin 2, gC ε a b c 2 = lin (gC ε a b c) (bas 2) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable {I : S.Inst} {H : S.Sec6Hyp T₁}

theorem controls (I : S.Inst) (H : S.Sec6Hyp T₁) : ∀ e ∈ S.E I.yi, ConjTo S.t e →
    ∃ n ∈ normalizer (S.E I.yi : Set X), n * S.t * n⁻¹ = e := by
  intro e he hc
  obtain ⟨w, rfl⟩ := I.eq_wV he
  rw [I.conjTo_wV_iff H.fus] at hc
  obtain ⟨p, q, c', r⟩ := w
  simp only at hc
  subst hc
  obtain ⟨ε, -, v₀, hv₀, w₀, hw₀, w₀', hw₀', hv₀c, hw₀c, hw₀'c⟩ := I.exists_vww H
  obtain ⟨a, b, c, habc⟩ := exists_gC ε p q r
  have hgM : I.Mat (v₀ ^ (c : ℕ) * (w₀ ^ (a : ℕ) * w₀' ^ (b : ℕ))) (gC ε a b c) :=
    (Mat.pw ⟨_, hv₀c⟩ c).mul ((Mat.pw ⟨_, hw₀c⟩ a).mul (Mat.pw ⟨_, hw₀'c⟩ b))
  refine ⟨_, hgM.mem, ?_⟩
  rw [hgM.conj_t, gC_col_two, habc]

theorem card_conj (I : S.Inst) (H : S.Sec6Hyp T₁) :
    Nat.card {e : S.E I.yi // ConjTo S.t e} = 8 := by
  let f : Fin 2 × Fin 2 × Fin 2 → {e : S.E I.yi // ConjTo S.t e} := fun p =>
    ⟨⟨I.wV (p.1, p.2.1, 1, p.2.2), I.wV_mem _⟩, (I.conjTo_wV_iff H.fus _).mpr rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · have := I.wV_injective (congrArg (fun y : {e : S.E I.yi // ConjTo S.t e} => (y : X)) h)
      simp only [Prod.mk.injEq] at this
      exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2.2)
    · obtain ⟨⟨e, he⟩, hc⟩ := x
      obtain ⟨w, rfl⟩ := I.eq_wV he
      have hw := (I.conjTo_wV_iff H.fus w).mp hc
      obtain ⟨p, q, c, r⟩ := w
      simp only at hw
      subst hw
      exact ⟨(p, q, r), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

namespace Data6

variable (D : I.Data6 H)

variable (R : D.Rel)

include R in
theorem no_conj_w₁ (hε : D.ε = 1) {e : X} (he : e ∈ S.E0 I.yi I.ki) :
    ¬ ConjTo S.t (D.w₁ * e) := by
  intro hq
  obtain ⟨hs1, hs4⟩ := R.h1 hε
  have hM1 : I.Mat D.w₁ (M1C 1) := hε ▸ R.rel.m1
  have hM2 : I.Mat D.w₂ (M2C 1) := hε ▸ R.rel.m2
  have hw1 : D.w₁ ^ 2 = 1 := by rw [R.rel.sq1, hs1, hs4, I.wV_zero]
  have hw2 : D.w₂ ^ 2 = 1 := by
    rw [R.rel.sq2, hs1, hs4, show lin dCols (0, 0, 0, 0) = (0, 0, 0, 0) by decide, I.wV_zero]
  have h12 : D.w₁ * D.w₂ = D.w₂ * D.w₁ := by
    have e1 := R.rel.comm
    rw [R.h0, hs4, I.wV_zero] at e1
    calc D.w₁ * D.w₂ = (D.w₁ * D.w₂ * D.w₁⁻¹ * D.w₂⁻¹) * D.w₂ * D.w₁ := by group
      _ = D.w₂ * D.w₁ := by rw [e1, one_mul]
  have hc1 : ∀ x : V4, I.wV x * D.w₁ = D.w₁ * I.wV (lin (M1C 1) x) := fun x => by
    have := (hM1.inv (M1C_sq 1)).conj x
    rw [inv_inv] at this
    rw [← this]; group
  have hc2 : ∀ x : V4, I.wV x * D.w₂ = D.w₂ * I.wV (lin (M2C 1) x) := fun x => by
    have := (hM2.inv (M2C_sq 1)).conj x
    rw [inv_inv] at this
    rw [← this]; group
  obtain ⟨p, y, r, rfl⟩ := (I.mem_E0_iff).mp he
  have hq2 : (D.w₁ * I.wV (p, y, 0, r)) ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := hq
    rw [← hg, conj_pow, S.t_sq]; group
  have hy : y = 0 := by
    have e1 : (D.w₁ * I.wV (p, y, 0, r)) ^ 2 =
        I.wV (addV (lin (M1C 1) (p, y, 0, r)) (p, y, 0, r)) := by
      calc (D.w₁ * I.wV (p, y, 0, r)) ^ 2 =
          D.w₁ * (I.wV (p, y, 0, r) * D.w₁) * I.wV (p, y, 0, r) := by
            rw [pow_two]; group
        _ = D.w₁ ^ 2 * I.wV (lin (M1C 1) (p, y, 0, r)) * I.wV (p, y, 0, r) := by
            rw [hc1, pow_two]; group
        _ = _ := by rw [hw1, one_mul, ← I.wV_add]
    rw [e1, ← I.wV_zero] at hq2
    exact sq_yi (p, y, 0, r) rfl (I.wV_injective hq2)
  subst hy
  have hdw₁ : D.d * D.w₁ * D.d⁻¹ = D.w₂ := rfl
  obtain ⟨e₀, he₀⟩ : ∃ e₄ : Fin 2, R.e = (0, 0, 0, e₄) := by
    refine ⟨R.e.2.2.2, Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))⟩
    · rw [R.e_z, hs1]
    · rw [R.e_y, hs1]
    · exact R.e_E0
  have hdw₂ : D.d * D.w₂ * D.d⁻¹ = D.w₁ * D.w₂ * I.wV (0, 0, 0, e₀) := by rw [R.w₃, he₀]
  set q := D.w₁ * I.wV (p, 0, 0, r) with hqdef
  have hqd : D.d * q * D.d⁻¹ = D.w₂ * I.wV (0, p, 0, r) := by
    have e1 : D.d * q * D.d⁻¹ = (D.d * D.w₁ * D.d⁻¹) * (D.d * I.wV (p, 0, 0, r) * D.d⁻¹) := by
      rw [hqdef]; group
    rw [e1, hdw₁, D.d_mat.conj, dCols_p0r]
  have hqdd : D.d * (D.d * q * D.d⁻¹) * D.d⁻¹ =
      D.w₁ * D.w₂ * I.wV (addV (0, 0, 0, e₀) (lin dCols (0, p, 0, r))) := by
    rw [hqd]
    have e1 : D.d * (D.w₂ * I.wV (0, p, 0, r)) * D.d⁻¹ =
        (D.d * D.w₂ * D.d⁻¹) * (D.d * I.wV (0, p, 0, r) * D.d⁻¹) := by group
    rw [e1, hdw₂, D.d_mat.conj, I.wV_add]; group
  have hqqd : q * (D.d * q * D.d⁻¹) = D.w₁ * D.w₂ *
      I.wV (addV (lin (M2C 1) (p, 0, 0, r)) (0, p, 0, r)) := by
    rw [hqd, hqdef]
    calc D.w₁ * I.wV (p, 0, 0, r) * (D.w₂ * I.wV (0, p, 0, r)) =
        D.w₁ * (I.wV (p, 0, 0, r) * D.w₂) * I.wV (0, p, 0, r) := by group
      _ = _ := by rw [hc2, ← mul_assoc, mul_assoc (D.w₁ * D.w₂), ← I.wV_add]
  have hqdq : (D.d * q * D.d⁻¹) * q = D.w₁ * D.w₂ *
      I.wV (addV (lin (M2C 1) (p, 0, 0, r)) (0, p, 0, r)) := by
    rw [hqd, hqdef, two_q_qd]
    calc D.w₂ * I.wV (0, p, 0, r) * (D.w₁ * I.wV (p, 0, 0, r)) =
        D.w₂ * (I.wV (0, p, 0, r) * D.w₁) * I.wV (p, 0, 0, r) := by group
      _ = _ := by rw [hc1, ← mul_assoc, ← h12, mul_assoc (D.w₁ * D.w₂), ← I.wV_add]
  set ζ := I.wV (0, 0, 0, p + e₀ + r) with hζ
  have hζQ : ∀ g ∈ S.Q0 I.yi I.ki D.w₁ D.w₂, ζ * g = g * ζ :=
    R.rel.central_of_gens (I.comm (I.wV_mem (0, 0, 0, p + e₀ + r)) I.z_mem_E)
      (I.comm (I.wV_mem (0, 0, 0, p + e₀ + r)) I.yi_mem_E)
      (I.comm (I.wV_mem (0, 0, 0, p + e₀ + r)) I.ki_mem_E)
      (commute_of_fix hM1 (M1C_ki 1 (p + e₀ + r))).symm
      (commute_of_fix hM2 (M2C_ki 1 (p + e₀ + r))).symm
  have hqQ : q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ :=
    mul_mem (I.w₁_mem_Q0 _ _) (I.E0_le_Q0 _ _ (I.wV_mem_E0 _ _ _))
  have hqdQ : D.d * q * D.d⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ := by
    rw [hqd]; exact mul_mem (I.w₂_mem_Q0 _ _) (I.E0_le_Q0 _ _ (I.wV_mem_E0 _ _ _))
  have hfin := conjTo_of_triple H.fus (a := q) (b := D.d * q * D.d⁻¹) (ζ := ζ)
    (by rw [hqqd, hqdq]) (hζQ q hqQ).symm (hζQ _ hqdQ).symm
    (by rw [conj_pow, show (D.w₁ * I.wV (p, 0, 0, r)) ^ 2 = q ^ 2 from rfl,
      show q ^ 2 = 1 from hq2]; group)
    (I.sq_eq_one (I.wV_mem _)) hq (by rw [conjTo_conj_iff]; exact hq)
    (by
      have e1 : q * (D.d * q * D.d⁻¹) * ζ = D.d * (D.d * q * D.d⁻¹) * D.d⁻¹ := by
        rw [hqqd, hqdd, hζ, mul_assoc (D.w₁ * D.w₂), ← I.wV_add, two_qdd]
      rw [e1, conjTo_conj_iff, conjTo_conj_iff]; exact hq)
  rw [hζ, I.conjTo_wV_iff H.fus] at hfin
  simp at hfin

theorem d_inv_w₁ : D.d⁻¹ * D.w₁ * D.d = D.d * D.w₂ * D.d⁻¹ := by
  have h := D.d_cube_commute D.w₁_Q₁
  calc D.d⁻¹ * D.w₁ * D.d = D.d⁻¹ * (D.d ^ 3 * D.w₁ * (D.d ^ 3)⁻¹) * D.d := by rw [h]; group
    _ = D.d * (D.d * D.w₁ * D.d⁻¹) * D.d⁻¹ := by simp only [pow_succ, pow_zero, one_mul]; group

theorem d_inv_E0 {f : X} (hf : f ∈ S.E0 I.yi I.ki) : D.d⁻¹ * f * D.d ∈ S.E0 I.yi I.ki := by
  have := (mem_normalizer_iff.mp (inv_mem (I.mem_normalizer_E0 D.d_mat dCols_E0')) _).mp hf
  simpa using this

include R in
theorem no_conj_w₂ (hε : D.ε = 1) {e : X} (he : e ∈ S.E0 I.yi I.ki) :
    ¬ ConjTo S.t (D.w₂ * e) := by
  intro hq
  apply D.no_conj_w₁ R hε (D.d_inv_E0 he)
  have e1 : D.w₁ * (D.d⁻¹ * e * D.d) = D.d⁻¹ * (D.w₂ * e) * D.d⁻¹⁻¹ := by
    rw [inv_inv, w₂]; group
  rw [e1, conjTo_conj_iff]; exact hq

include R in
theorem no_conj_two (hε : D.ε = 1) : ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂, ¬ ConjTo S.t q := by
  intro q hq hqt
  obtain ⟨a, b, e, he, rfl⟩ := R.rel.mem_Q0_iff.mp hq
  fin_cases a <;> fin_cases b
  · simp only [pow_zero, one_mul] at hqt
    obtain ⟨p, y, r, rfl⟩ := (I.mem_E0_iff).mp he
    rw [I.conjTo_wV_iff H.fus] at hqt
    simp at hqt
  · simp only [pow_zero, mul_one, pow_one] at hqt
    exact D.no_conj_w₂ R hε he hqt
  · simp only [pow_zero, one_mul, pow_one] at hqt
    exact D.no_conj_w₁ R hε he hqt
  ·
    simp only [pow_one] at hqt
    obtain ⟨hs1, hs4⟩ := R.h1 hε
    have hw1 : D.w₁ * D.w₁ = 1 := by
      rw [← pow_two, R.rel.sq1, hs1, hs4, I.wV_zero]
    have h1 : D.d⁻¹ * D.w₁ * D.d = D.w₁ * D.w₂ * I.wV R.e := by rw [D.d_inv_w₁, R.w₃]
    have h2 : D.d⁻¹ * D.w₂ * D.d = D.w₁ := by rw [w₂]; group
    have hf : I.wV R.e * (D.d⁻¹ * e * D.d) ∈ S.E0 I.yi I.ki :=
      mul_mem (I.wV_mem_E0' R.e_E0) (D.d_inv_E0 he)
    apply D.no_conj_w₂ R hε hf
    have e1 : D.w₂ * (I.wV R.e * (D.d⁻¹ * e * D.d)) = D.d⁻¹ * (D.w₂ * D.w₁ * e) * D.d⁻¹⁻¹ := by
      rw [inv_inv]
      calc D.w₂ * (I.wV R.e * (D.d⁻¹ * e * D.d)) =
          (D.w₁ * D.w₁) * D.w₂ * I.wV R.e * (D.d⁻¹ * e * D.d) := by rw [hw1]; group
        _ = (D.d⁻¹ * D.w₂ * D.d) * (D.d⁻¹ * D.w₁ * D.d) * (D.d⁻¹ * e * D.d) := by
            rw [h1, h2]; group
        _ = D.d⁻¹ * (D.w₂ * D.w₁ * e) * D.d := by group
    rw [e1, conjTo_conj_iff]; exact hqt

include R in
theorem no_conj_one (hε : D.ε = 0) (hs4 : R.s4 = 0) :
    ∀ q ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁, ¬ ConjTo S.t q := by
  have hγ : R.γ = (0, 0, 0, 0) := by rw [R.h0, hs4]
  have hQ := R.rel.comm_one hε hγ
  have hkc : I.ki * D.c₁ = D.c₁ * I.ki := by
    have h := D.c₁_mat.conj_ki
    rw [show I.wV (vC 3) = I.ki by simp [vC, wV]] at h
    calc I.ki * D.c₁ = D.c₁ * (D.c₁⁻¹ * I.ki * D.c₁) := by group
      _ = D.c₁ * I.ki := by
          congr 1
          calc D.c₁⁻¹ * I.ki * D.c₁ = D.c₁⁻¹ * (D.c₁ * I.ki * D.c₁⁻¹) * D.c₁ := by rw [h]
            _ = I.ki := by group
  have hC₁ : ∀ x ∈ D.C₁, ∀ y ∈ D.C₁, x * y = y * x := by
    intro x hx y hy
    refine comm_of_mem_closure (fun a ha b hb => ?_) hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hkc
    · exact hkc.symm
    · rfl
  have hcl : S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ =
      closure ((S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) ∪ D.C₁) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcomm : ∀ a ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁, ∀ b ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁,
      a * b = b * a := by
    intro a ha b hb
    rw [hcl] at ha hb
    refine comm_of_mem_closure (fun x hx y hy => ?_) ha hb
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hQ x hx y hy
    · exact (D.C₁_comm R y hy x hx).symm
    · exact D.C₁_comm R x hx y hy
    · exact hC₁ x hx y hy
  have hc₁C : D.c₁ ∈ D.C₁ := subset_closure (by simp)
  have hsup : S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ = S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ zpowers D.c₁ := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [C₁, closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact mem_sup_left (I.E0_le_Q0 _ _ (subset_closure (by simp)))
      · exact mem_sup_right (mem_zpowers _)
    · exact sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hc₁C))
  have hN : D.c₁ ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) :=
    mem_normalizer_of_conj_mem fun q hq => by
      rw [D.C₁_comm R _ hc₁C q hq, mul_inv_cancel_right]; exact hq
  have hc2 : D.c₁ ^ 2 ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ :=
    (zpowers_le.mpr (I.E0_le_Q0 _ _ (subset_closure (by simp)))) D.c₁_sq_mem
  have hcQ : D.c₁ ∉ S.Q0 I.yi I.ki D.w₁ D.w₂ := by
    intro h
    obtain ⟨a, b, e, he, he'⟩ := R.rel.mem_Q0_iff.mp h
    have hM : I.Mat D.c₁ (comp (pw (M2C D.ε) b) (pw (M1C D.ε) a)) := by
      rw [he']
      exact ((R.rel.m2.pw b).mul (R.rel.m1.pw a)).mul_central (I.E0_le_centralizer he)
    exact vC_ne_Q0 D.ε a b (D.c₁_mat.unique hM)
  have hcard : Nat.card (S.Q0 I.yi I.ki D.w₁ D.w₂ ⊔ D.C₁ : Subgroup X) = 64 := by
    rw [hsup, card_sup_zpowers hN hc2 hcQ, R.rel.card_Q0]
  intro q hq
  exact not_conjTo_of_comm hcomm hcard hq

end Data6

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
