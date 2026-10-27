module

public import CFSG.CGT.Stroth77.Section42

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace Stroth42

theorem pow_eq_of_sq_eq {c e : G} {m : ℕ} (hm : 2 ≤ m) (hoc : orderOf c = 2 ^ m)
    (he : e * e = c⁻¹ * c ^ 2 ^ (m - 1)) : e ^ 2 ^ m = c ^ 2 ^ (m - 1) := by
  have hc : c ^ 2 ^ m = 1 := by rw [← hoc]; exact pow_orderOf_eq_one c
  have h0 : e ^ 2 ^ m = (e * e) ^ 2 ^ (m - 1) := by
    rw [← sq, ← pow_mul, ← pow_succ', show m - 1 + 1 = m by omega]
  have h1 : c ^ (2 ^ (m - 1) * 2 ^ (m - 1)) = 1 := by
    rw [show 2 ^ (m - 1) * 2 ^ (m - 1) = 2 ^ m * 2 ^ (m - 2) by
      rw [← pow_add, ← pow_add]; congr 1; omega, pow_mul, hc, one_pow]
  have h2 : (c ^ 2 ^ (m - 1))⁻¹ = c ^ 2 ^ (m - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, ← pow_succ', show m - 1 + 1 = m by omega, hc]
  rw [h0, he, (Commute.inv_left ((Commute.refl c).pow_right _)).mul_pow, inv_pow, ← pow_mul, h1,
    mul_one, h2]

theorem pow_mul_self_eq_one {c : G} {m : ℕ} (hm : 1 ≤ m) (hoc : orderOf c = 2 ^ m) :
    c ^ 2 ^ (m - 1) * c ^ 2 ^ (m - 1) = 1 ∧ c ^ 2 ^ (m - 1) ≠ 1 := by
  refine ⟨?_, pow_ne_one_of_lt_orderOf (by positivity) (by
    rw [hoc]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))⟩
  rw [← sq, ← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, ← hoc, pow_orderOf_eq_one]

end Stroth42

theorem StrothFrame.IsD.false_of_t100_ii {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t100 m)} (h : F.IsD D dD) (hm : 2 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e : G} (heN : e ∈ Subgroup.normalizer (D : Set G))
    (he : e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (h1 : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2)
    (h2 : e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 →
      (∃ p ∈ Subgroup.closure {dD.uv, dD.t, dD.u}, p⁻¹ * y * p = (dD.c : G) ^ 2 ^ (m - 1)) ∨
        ∃ g ∈ dD.L, g⁻¹ * y * g = (dD.a : G) ^ 2 ^ m)
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
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one (by omega) hoc
  rw [← hz] at hz2 hz1
  have hxz : e ^ 2 ^ m = z := Stroth42.pow_eq_of_sq_eq hm hoc he
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
    (Stroth42.conj_not_mem le_sup_right (by omega) hxz hz2 hz1 dD.uv_mem dD.uv_sq h3' h4
      (fun y hy => h5 y (hUS hy)) h6U)

theorem StrothFrame.IsD.stroth_4_3 {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ}
    (h228 : (∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
      (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n)
    (h42 : ∀ n, τ ≠ .t300 n)
    (hSR : (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u})
    (h33 : ∀ s, τ = .t101 s → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (h32 : ∀ m, τ = .t100 m → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))))
    (hA : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} →
      ((∃ m, τ = .t100 m) ∨ ∃ s, τ = .t101 s) → False)
    (he : ∀ m e, τ = .t100 m → e ∈ Subgroup.normalizer (D : Set G) →
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv →
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t → e⁻¹ * dD.u * e = dD.u →
      ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) → False) :
    (∃ m, τ = .t200 m) ∨ ∃ m, τ = .t201 m := by
  rcases h228 with h | h | ⟨m, rfl⟩ | ⟨s, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rcases h32 m rfl with hR | ⟨e, heR, hRe, huv, ht, hu, hcases⟩
    · rw [hR] at hSR
      exact hA hSR (Or.inl ⟨m, rfl⟩)
    · refine he m e rfl heR.1.2 ?_ huv ht hu hcases
      rw [hSR, hRe, sup_right_comm]
  · exfalso
    rw [h33 s rfl] at hSR
    exact hA hSR (Or.inr ⟨s, rfl⟩)
  · exact absurd rfl (h42 n)

end CFSG.CGT.Stroth77
