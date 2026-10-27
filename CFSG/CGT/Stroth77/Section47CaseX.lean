module

public import CFSG.CGT.Stroth77.Section47Cases
public import CFSG.CGT.Stroth77.Section47CoreXH

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

open Stroth47Core in
theorem StrothFrame.IsD.false_of_t200_case_x {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 2 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {f : G} (hfN : f ∈ Subgroup.normalizer (D : Set G)) {p : ℕ} (hp : p % 2 = 1)
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f) :
    False := by
  haveI := F.simple
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set U := D ⊔ P ⊔ Subgroup.zpowers (f * f) with hU
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hZ : Subgroup.zpowers (f * f) ≤ Subgroup.zpowers f :=
    (Subgroup.zpowers_le).mpr (mul_mem (Subgroup.mem_zpowers f) (Subgroup.mem_zpowers f))
  have hSU : (F.S : Subgroup G) = U ⊔ Subgroup.zpowers f := by
    rw [hS, hU, sup_assoc (D ⊔ P), sup_eq_right.mpr hZ]
  have heU : f * f ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hfU : f ∉ U := dD.t200x_not_mem (by omega) hrel
  have hUS : U ≤ (F.S : Subgroup G) := by rw [hSU]; exact le_sup_left
  have hUidx : U.relIndex (F.S : Subgroup G) = 2 := by
    rw [hSU]
    exact Stroth47.relIndex_sup_zpowers_of_mul_self_mem (dD.t200x_mem_normalizer hfN hrel) heU hfU
  have hfS : f ∈ (F.S : Subgroup G) := by
    rw [hSU]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one (by omega : 1 ≤ m) hoc
  rw [← hz] at hz2 hz1
  have hza := h.not_isConj_of_omega hnc (dD.t200_h3 (by omega))
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases dD.t200_h3 (by omega) y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  exact Stroth47.false_of_harada_four (Stroth42.frame_exists_mul_ne F) F.S hUS hUidx
    (le_sup_right.trans le_sup_left) hfS hfU (by omega) (t200x_pow_eq dD hm hp hrel) hz2 hz1 h3'
    (t200x_h4 dD (by omega) hrel)
    (fun y hy => t200x_h5 dD hfN hrel y (hSU ▸ hy))
    (fun y hy hyU => t200x_h6 dD hm hp hfN hrel y (hSU ▸ hy) hyU)
    (fun y hy hyU => t200x_h8 dD hm hp hfN hrel y (hSU ▸ hy) hyU)

theorem stroth_4_7_hcyc :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
      2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f →
      (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3) → False := by
  intro G _ _ F D m hm dD h _ hncD f hfR hS hrel
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  rcases hrel with hrel | hrel
  · exact h.false_of_t200_case_x hm hnc hfR.1.2 (by norm_num) hrel hS
  · exact h.false_of_t200_case_x hm hnc hfR.1.2 (by norm_num) hrel hS

theorem stroth_4_7R_of_hinv_hKlein
    (hinv : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
      1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
      (Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
        Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False)
    (hKlein : ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
      1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
      (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
      (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
        ¬ IsConj x y) →
      ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.closure {e, f} →
      Rel34i dD e (2 ^ (m + 1)) → (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) →
      f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) → False) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    1 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u} →
    ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
    (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
      (Rel34i dD e (2 ^ (m + 1)) ∨
        Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
        Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
    (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
      Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
      f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
    (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
      (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3))) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} :=
  stroth_4_7R_of_cases hinv hKlein stroth_4_7_hcyc

end CFSG.CGT.Stroth77
