module

public import CFSG.CGT.Stroth77.Section47CaseX
public import CFSG.CGT.Stroth77.Section47CoreKC
public import CFSG.CGT.Stroth77.Section47Fus
public import CFSG.CGT.Stroth77.Section47CoreKS
public import CFSG.CGT.Stroth77.Section47HaradaCount

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200

variable {G : Type} [Group G] [Finite G]

open Stroth47Core StrothWeakTypeData in
theorem StrothFrame.IsD.false_of_t200_klein {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y)
    {e f : G} (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) {p : ℕ} (hp : p % 2 = 1)
    (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.closure {e, f}) :
    False := by
  haveI := F.simple
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set U := D ⊔ P ⊔ Subgroup.zpowers f with hU
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hSU : (F.S : Subgroup G) = U ⊔ Subgroup.zpowers e := by
    rw [hS, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hU, sup_comm (Subgroup.zpowers e), ← sup_assoc]
  have heU : e * e ∈ U := t200k_e_mul_self_mem dD hrel_e
  have heUn : e ∉ U := t200k_e_not_mem dD hm hrel_e hrel_f
  have heNU := t200k_mem_normalizer dD heN hfN hrel_e hrel_f hconj
  have hUS : U ≤ (F.S : Subgroup G) := by rw [hSU]; exact le_sup_left
  have hUidx : U.relIndex (F.S : Subgroup G) = 2 := by
    rw [hSU]; exact Stroth47.relIndex_sup_zpowers_of_mul_self_mem heNU heU heUn
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hSU]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hoc : orderOf (dD.c : G) = 2 ^ m := by rw [Stroth42.orderOf_c_coe]; rfl
  obtain ⟨hz2, hz1⟩ := Stroth42.pow_mul_self_eq_one hm hoc
  rw [← hz] at hz2 hz1
  have hxz : e ^ 2 ^ m = z := Stroth47.pow_eq_of_sq_eq_inv hm hoc hrel_e.e_sq
  have he1 : e ^ 2 ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, hxz, sq, hz2]
  have hza := h.not_isConj_of_omega hnc (dD.t200_h3 hm)
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases dD.t200_h3 hm y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have huv1 : dD.uv ≠ 1 := fun h1 => dD.d8_not_mem (t200_faithful hm) (i := true) (j := false)
    (l := false) (by decide) 0 (by rw [dD.ofTorus_zero, one_mul, d8_tff, h1]; exact one_mem _)
  have huva : IsConj dD.uv ((dD.a : G) ^ 2 ^ (m + 1)) :=
    h.t200_fusion.1 _ (Subgroup.subset_closure (by simp)) huv1
  have h6 : ∀ y ∈ U, y * dD.uv ∈ D → y * y = 1 → ¬ IsConj y z := fun y _ hy hyy hyz =>
    hza (hyz.symm.trans ((t200k_isConj_uv dD hp hrel_f y hy hyy).trans huva))
  have hSp : IsPGroup 2 ↥(U ⊔ Subgroup.zpowers e) := hSU ▸ F.S.isPGroup'
  refine Stroth47.false_of_harada_count (Stroth42.frame_exists_mul_ne F) F.S hUS hUidx
    (le_sup_right.trans le_sup_left) heS heUn hxz hz2 hz1 dD.uv_mem dD.uv_sq h3'
    (fun y hy => t200k_h5 dD heN hfN hrel_e hrel_f hconj y (hSU ▸ hy)) h6
    (fun y hy hyU hy2 _ => t200k_h6' dD hm hp heN hfN hrel_e hrel_f hconj y (hSU ▸ hy) hyU hy2)
    ?_ (fun y hy hyU hyy g k hk hyg => by
      rw [hSU]
      exact t200k_h8c dD hm heN hfN hrel_e hrel_f hconj he1 hz1 hSp y (hSU ▸ hy) hyU hyy g k hk
        hyg)
    (Stroth42.conj_not_mem (le_sup_right.trans le_sup_left) hm hxz hz2 hz1 dD.uv_mem
      dD.uv_sq h3' (t200k_h4 dD hm hrel_f)
      (fun y hy => t200k_h5 dD heN hfN hrel_e hrel_f hconj y (Subgroup.mem_sup_left hy)) h6)
  intro y hyS hyU l hl hyl g k hy
  have hyS' := hyS
  rw [hSU] at hyS'
  obtain ⟨w, hw, kk, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem heNU heU).mp hyS'
  cases kk
  · exact hyU (by simpa [bpow] using hw)
  simp only [bpow, ↓reduceIte] at hyU hyl hy hyS
  obtain ⟨v, i, j, l', k', rfl⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp hw
  cases k'
  ·
    simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyl hy hyU
    refine t200_i_h8 dD hm hrel_e _ ?_ ?_ l (by omega) hyl ?_
    · exact mul_mem (Subgroup.mem_sup_left (dD.nf_mem v i j l'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · intro hmem
      apply t200_i_h2 dD hm hrel_e
      have := (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).mul_mem
        ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).inv_mem (dD.nf_mem v i j l')) hmem
      rwa [inv_mul_cancel_left] at this
    · rw [hy, Stroth42.conj_pow', ← pow_mul, show 2 * k * 2 ^ m = 2 ^ (m + 1) * k by ring,
        pow_mul, he1, one_pow]
      group
  ·
    simp only [bpow, ↓reduceIte] at hyl hy hyU hyS
    set X := dD.ofTorus v * dD.d8 i j l' with hXdef
    have hy' : X * f * e = X * (f * e) := by group
    rw [hy'] at hyl hy hyS hyU
    have hfc := t200k_f_comm_c₁ dD hm hrel_f
    have hec := t200k_e_comm_c₁ dD hrel_e
    rw [← hz] at hfc hec
    have hgz : f * e * z = z * (f * e) := by
      rw [mul_assoc, hec, ← mul_assoc, hfc, mul_assoc]
    have hyz : X * (f * e) * z = z * (X * (f * e)) := by
      rw [← hyl]; exact ((Commute.refl _).pow_right _).eq
    have hX : X * z = z * X := by
      have h1 : X * z * (f * e) = z * X * (f * e) := by
        rw [mul_assoc X z, ← hgz, ← mul_assoc, hyz, ← mul_assoc]
      exact mul_right_cancel h1
    obtain ⟨rfl, rfl⟩ := dD.t200_comm_z hm hX
    exact t200k_pow_ne dD hm hrel_e hrel_f hconj v l' hl hyl

theorem stroth_4_7_hKlein :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
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
      f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) → False := by
  intro G _ _ F D m hm dD h _ hncD e he f hf hS hrel_e hrel_f hconj
  have hnc : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hncD
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  rcases hrel_f with hrel_f | hrel_f
  · exact h.false_of_t200_klein hm hnc he.1.2 hf.1.2 (by norm_num) hrel_e hrel_f hconj hS
  · exact h.false_of_t200_klein hm hnc he.1.2 hf.1.2 (by norm_num) hrel_e hrel_f hconj hS

theorem stroth_4_7R_of_hinv
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
        Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False) :
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
  stroth_4_7R_of_hinv_hKlein hinv stroth_4_7_hKlein

end CFSG.CGT.Stroth77
