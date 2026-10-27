module

public import CFSG.CGT.Stroth77.Section43
public import CFSG.CGT.Stroth77.Section47CoreIC

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth47

theorem pow_eq_of_sq_eq_inv {c e : G} {m : ℕ} (hm : 1 ≤ m) (hoc : orderOf c = 2 ^ m)
    (he : e * e = c⁻¹) : e ^ 2 ^ m = c ^ 2 ^ (m - 1) := by
  have h0 : e ^ 2 ^ m = (e * e) ^ 2 ^ (m - 1) := by
    rw [← sq, ← pow_mul, ← pow_succ', show m - 1 + 1 = m by omega]
  rw [h0, he, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, ← pow_succ',
    show m - 1 + 1 = m by omega, ← hoc, pow_orderOf_eq_one]

end Stroth47

theorem StrothFrame.IsD.false_of_t200_i {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G)) (he : e * e = (dD.c : G)⁻¹)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (h1 : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2)
    (h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (m + 1))
    (h4 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * y →
        y ^ 2 ^ m ≠ (dD.c : G) ^ 2 ^ (m - 1))
    (h5 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y * y ∈ D ∨ y * y * dD.uv ∈ D)
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    (h6' : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} → y * y ≠ 1)
    (h7 : ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16)
    (h8 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (m - 1) → y ^ 2 ^ m ≠ 1)
    (h9 : ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
        IsMulCommutative X → Nat.card X = Nat.card D → X = D) :
    False := by
  haveI := F.simple
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]
    exact sup_le (sup_le Subgroup.le_normalizer hPN) ((Subgroup.zpowers_le).2 heN)
  have hUS : D ⊔ P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_left
  have hPS : P ≤ (F.S : Subgroup G) := le_sup_right.trans hUS
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one hm hoc
  rw [← hz] at hz2 hz1
  have hxz : e ^ 2 ^ m = z := Stroth47.pow_eq_of_sq_eq_inv hm hoc he
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  rw [← hS] at h5 h6' h7 h8 h9
  have h6U : ∀ y ∈ D ⊔ P, y * dD.uv ∈ D → y * y = 1 → ¬ IsConj y z := fun y _ hy hy2 =>
    Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative h.le_S hSD hPS hzD h3' hz2 hz1 h7 h9
      (h6 y hy hy2)
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  exact Stroth42.false_of_harada (Stroth42.frame_exists_mul_ne F) F.S hUS (by rw [hS]; exact h1)
    le_sup_right heS h2 hxz hz2
    hz1 dD.uv_mem dD.uv_sq h3' h5 h6U (fun y hyS hyU hy2 => absurd hy2 (h6' y hyS hyU)) h8
    (Stroth42.conj_not_mem le_sup_right hm hxz hz2 hz1 dD.uv_mem dD.uv_sq h3' h4
      (fun y hy => h5 y (hUS hy)) h6U)

open Stroth47Core in
theorem StrothFrame.IsD.false_of_t200_case_i {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G)) (hrel : Rel34i dD e (2 ^ (m + 1)))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) :
    False :=
  h.false_of_t200_i hm hnc heN hrel.e_sq hS (t200_i_h1 dD hm hrel) (t200_i_h2 dD hm hrel)
    (dD.t200_h3 hm) (dD.t200_h4 hm) (dD.t200iAction hrel).mul_self_mem_or (dD.t200_h6 hm)
    (t200_i_h6' dD hm hrel)
    (t200_i_h7 dD (dD.t200iAction hrel) hm (dD.t200iAction_φe hrel) (dD.t200iAction_ve hrel))
    (t200_i_h8 dD hm hrel) (t200_i_h9 dD (dD.t200iAction hrel) hm (dD.t200iAction_φe hrel))

end CFSG.CGT.Stroth77
