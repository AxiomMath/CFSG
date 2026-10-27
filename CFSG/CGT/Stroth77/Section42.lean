module

public import CFSG.CGT.Stroth77.Section42Fusion
public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.CGT.Stroth77.StrothAmbient

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth42

theorem orderOf_c_coe {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData B τ) : orderOf (dD.c : S) = 2 ^ τ.k 0 := by
  rw [Subgroup.orderOf_coe, StrothWeakTypeData.c, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul,
    AddEquiv.addOrderOf_eq, addOrderOf_c]

theorem frame_exists_mul_ne (F : StrothFrame G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  exact F.uv_not_mem_centralizer_A (Subgroup.mem_centralizer_iff.mpr fun y _ => hc y F.dA.uv)

end Stroth42

theorem StrothFrame.IsD.not_isConj_of_omega {F : StrothFrame G} {D : Subgroup G}
    {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ} (h : F.IsD D dD) {z za : G}
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = z) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = za) :
    ¬ IsConj z za := by
  intro hzza
  obtain ⟨x, hx, y, hy, hox, hoy, hxy⟩ := hnc
  have key : ∀ w ∈ omegaIn 1 F.A, orderOf w = 2 → IsConj w za := by
    intro w hw how
    have hwD : w ∈ D := h.A_le (omegaIn_le 1 F.A hw)
    have hw2 : w * w = 1 := by rw [← sq, ← how]; exact pow_orderOf_eq_one w
    have hw1 : w ≠ 1 := by rintro rfl; simp at how
    rcases h3 w hwD hw2 hw1 with ⟨p, -, hp⟩ | ⟨g, -, hg⟩
    · exact (Stroth42.isConj_of_conj_eq hp).symm.trans hzza
    · exact (Stroth42.isConj_of_conj_eq hg).symm
  exact hxy ((key x hx hox).trans (key y hy hoy).symm)

theorem StrothFrame.IsD.false_of_split {F : StrothFrame G} {D : Subgroup G}
    {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ} (h : F.IsD D dD) {j : ℕ} (hj : 1 ≤ j)
    (hk : τ.k 0 = j + 1) {za : G}
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h1 : (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2)
    (h2 : (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ j) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = za)
    (h4 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ j = (dD.c : G) ^ 2 ^ j * y → y ^ 2 ^ j ≠ (dD.c : G) ^ 2 ^ j)
    (h5 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y ∈ D ∨ y * y * dD.uv ∈ D)
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    (h6' : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y = 1 → ∃ E : Subgroup G,
        E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    (h7 : ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ j} → (∀ e ∈ E, e * e = 1) → Nat.card E ≠ 16)
    (h8 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ j → y ^ 2 ^ j ≠ 1)
    (h9 : ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ j} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D) :
    False := by
  haveI := F.simple
  set U := Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} with hU
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ j with hz
  have hPN : P ≤ Subgroup.normalizer (D : Set G) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [dD.uv_mem, dD.t_mem, dD.u_mem]
  have hSD : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hS]; exact sup_le Subgroup.le_normalizer hPN
  have hPS : P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_right
  have hUS : U ≤ (F.S : Subgroup G) := by
    rw [hS, hU, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (D.pow_mem dD.c.2 2)
    · exact Subgroup.mem_sup_left dD.a.2
    · exact Subgroup.mem_sup_left dD.b.2
    all_goals exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hPU : P ≤ U := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  have hoc : orderOf (dD.c : G) = 2 ^ (j + 1) := by rw [Stroth42.orderOf_c_coe, hk]
  have hz2 : z * z = 1 := by
    rw [hz, ← sq, ← pow_mul, ← pow_succ, ← hoc, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hz]
    exact pow_ne_one_of_lt_orderOf (by positivity) (by
      rw [hoc]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hza := h.not_isConj_of_omega hnc h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  rw [← hS] at h7 h9
  have hE : ∀ y : G, (∃ E : Subgroup G, E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 16) → ¬ IsConj y z := fun y hy =>
    Stroth42.not_isConj_of_e16 F.S dD.isMulCommutative h.le_S hSD hPS hzD h3' hz2 hz1 h7 h9 hy
  have h6U : ∀ y ∈ U, y * dD.uv ∈ D → y * y = 1 → ¬ IsConj y z :=
    fun y _ hy hy2 => hE y (h6 y hy hy2)
  have h6S : ∀ y ∈ (F.S : Subgroup G), y ∉ U → y * y = 1 → ¬ IsConj y z :=
    fun y hyS hyU hy2 => hE y (h6' y (hS ▸ hyS) hyU hy2)
  rw [← hS] at h5 h8
  exact Stroth42.false_of_harada (Stroth42.frame_exists_mul_ne F) F.S hUS (by rw [hS]; exact h1)
    hPU (h.le_S dD.c.2) h2 rfl hz2 hz1 dD.uv_mem dD.uv_sq h3' h5 h6U h6S h8
    (Stroth42.conj_not_mem hPU hj rfl hz2 hz1 dD.uv_mem dD.uv_sq h3' h4
      (fun y hy => h5 y (hUS hy)) h6U)

theorem StrothFrame.IsD.stroth_4_2 {F : StrothFrame G} {D : Subgroup G} {n : ℕ}
    {dD : StrothWeakTypeData D (.t300 n)} (h : F.IsD D dD) (hn : 3 ≤ n)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    (h35 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (hSR : (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u})
    (h1 : (Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) = 2)
    (h2 : (dD.c : G) ∉
      Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (n - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ (n - 1))
    (h4 : ∀ y ∈ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u},
      y * (dD.c : G) ^ 2 ^ (n - 1) = (dD.c : G) ^ 2 ^ (n - 1) * y →
        y ^ 2 ^ (n - 1) ≠ (dD.c : G) ^ 2 ^ (n - 1))
    (h5 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y ∈ D ∨ y * y * dD.uv ∈ D)
    (h6 : ∀ y : G, y * dD.uv ∈ D → y * y = 1 → ∃ E : Subgroup G,
      E ≤ Subgroup.centralizer {y} ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16)
    (h6' : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      y * y ≠ 1)
    (h7 : ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)} → (∀ e ∈ E, e * e = 1) →
        Nat.card E ≠ 16)
    (h8 : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      y ∉ Subgroup.closure {(dD.c : G) ^ 2, (dD.a : G), (dD.b : G), dD.uv, dD.t, dD.u} →
      ∀ l : ℕ, 1 ≤ l → y ^ 2 ^ l = (dD.c : G) ^ 2 ^ (n - 1) → y ^ 2 ^ (n - 1) ≠ 1)
    (h9 : ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (n - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D) :
    False := by
  rw [h35] at hSR
  exact h.false_of_split (j := n - 1) (by omega) (by change n = n - 1 + 1; omega) hnc hSR h1 h2
    h3 h4 h5 h6 (fun y hy hyU hy2 => absurd hy2 (h6' y hy hyU)) h7 h8 h9

end CFSG.CGT.Stroth77
