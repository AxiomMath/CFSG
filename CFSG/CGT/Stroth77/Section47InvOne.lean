module

public import CFSG.CGT.Stroth77.Section47InvOneE32
public import CFSG.CGT.Stroth77.Section47InvOneFacts
public import CFSG.CGT.Stroth77.Section47InvOneS1
public import CFSG.CGT.Stroth77.Section47InvOneSwap

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200 Stroth47Core

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200inv1_h1 {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) = 2 :=
  (dD.t200inv1EAction hrel).relIndex_S (t200inv1_not_word dD hm hj hrel)

theorem t200inv1_h2 {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    e ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
  (dD.t200inv1EAction hrel).e_not_mem (t200inv1_not_word dD hm hj hrel)

end Stroth47Core

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t200 m)}

theorem t200inv1_card_le_sixteen_S {e : G} {j p : ℕ} (hm : 1 ≤ m)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) {A : Subgroup G}
    (hA : A ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hA2 : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 16 := by
  have hA' := hA
  rw [hS] at hA'
  exact t200inv1_card_le_sixteen dD hm hj hrel hA' hA2

theorem t200inv1_hR {e : G} {j : ℕ} (hm : 1 ≤ m)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2)
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
      ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G)) :
    ∀ y : G, IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) → ∀ A : Subgroup G,
      A ≤ Subgroup.centralizer {y} → (∀ x ∈ A, x * x = 1) → Nat.card A ≠ 32 := by
  intro y hy A hA hA2 hA32
  exact (Stroth47Inv1.not_isConj_of_card (S := (F.S : Subgroup G))
    (z := (dD.c : G) ^ 2 ^ (m - 1)) (y := y) (n := 32) hsyl
    (fun B hB hB2 hB32 => by
      have h16 := t200inv1_card_le_sixteen_S (dD := dD) hm hS hj hrel hB hB2
      omega) hA hA2 hA32) hy

omit [Finite G] in
theorem t200inv1_cabuv_ne_one (hm : 1 ≤ m) : dD.cab * dD.uv ≠ 1 := by
  intro h1
  have hcab : dD.cab = dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) := by
    rw [StrothWeakTypeData.cab, dD.c_eq, dD.a_eq, dD.b_eq, c_eq_ofInt, a_eq_ofInt,
      b_eq_ofInt, ← dD.ofTorus_add, ← dD.ofTorus_add, ← Torus.ofInt_add, ← Torus.ofInt_add]
    congr 1
    funext i
    fin_cases i <;> simp
  have h2 : dD.ofTorus (Torus.ofInt _ ![1, 1, 1]) * dD.d8 true false false =
      dD.ofTorus 0 * dD.d8 false false false := by
    rw [← hcab, dD.d8_tff, h1, dD.ofTorus_zero, dD.d8_fff, one_mul]
  have hinj := dD.nf_inj (t200_faithful (m := m) hm) h2
  exact Bool.noConfusion hinj.2.1

theorem t200inv1_cabuv_hx32 {e : G} {j : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer {dD.cab * dD.uv} ∧
      (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32 := by
  rcases hj with rfl | rfl
  · let A : Subgroup G := Subgroup.closure
      ({(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.cab * dD.uv,
        (dD.a : G)⁻¹ * dD.t, e} : Set G)
    have hEl := t200inv1_elab_e dD hm hrel
    have hExp : ∀ x ∈ A, x * x = 1 := hEl.1
    have hxA : dD.cab * dD.uv ∈ A := Subgroup.subset_closure (by simp)
    refine ⟨A, ?_, hExp, hEl.2⟩
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (by
      have hy2 : y * y = 1 := hExp y hy
      have hx2 : (dD.cab * dD.uv) * (dD.cab * dD.uv) = 1 := hExp _ hxA
      have hyx2 : (y * (dD.cab * dD.uv)) * (y * (dD.cab * dD.uv)) = 1 :=
        hExp _ (A.mul_mem hy hxA)
      have h1 : (y * (dD.cab * dD.uv))⁻¹ = y * (dD.cab * dD.uv) :=
        inv_eq_of_mul_eq_one_right hyx2
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy2,
        inv_eq_of_mul_eq_one_right hx2] at h1
      exact h1.symm)
  · let A : Subgroup G := Subgroup.closure
      ({(dD.a : G) ^ 2 ^ (m + 1), (dD.b : G) ^ 2 ^ (m + 1), dD.cab * dD.uv,
        (dD.a : G)⁻¹ * dD.t, (dD.c : G) ^ 2 ^ (m - 1) * e} : Set G)
    have hEl := t200inv1_elab_c₁e dD hm hrel
    have hExp : ∀ x ∈ A, x * x = 1 := hEl.1
    have hxA : dD.cab * dD.uv ∈ A := Subgroup.subset_closure (by simp)
    refine ⟨A, ?_, hExp, hEl.2⟩
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (by
      have hy2 : y * y = 1 := hExp y hy
      have hx2 : (dD.cab * dD.uv) * (dD.cab * dD.uv) = 1 := hExp _ hxA
      have hyx2 : (y * (dD.cab * dD.uv)) * (y * (dD.cab * dD.uv)) = 1 :=
        hExp _ (A.mul_mem hy hxA)
      have h1 : (y * (dD.cab * dD.uv))⁻¹ = y * (dD.cab * dD.uv) :=
        inv_eq_of_mul_eq_one_right hyx2
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy2,
        inv_eq_of_mul_eq_one_right hx2] at h1
      exact h1.symm)

theorem t200inv1_hU4 {e : G} {j : ℕ} (hm : 1 ≤ m)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2) :
    ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      (∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))) ∨
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {y} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32 := by
  intro y hyS hy2 hy1 hyw
  by_cases hte : ∃ (v : Torus (StrothTypeIndex.t200 m).k) (i : Bool),
      y = dD.ofTorus v * dD.d8 i true false * e
  · right
    obtain ⟨v, i, rfl⟩ := hte
    exact t200inv1_te_elab32 dD hm hj hrel v i hy2
  · left
    have hyX : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
      rw [hS] at hyS
      exact hyS
    obtain ⟨q, hqX, hq⟩ := t200inv1_conj_mul_w₀ dD hm hj hrel y hyX hy2 hy1 hyw
      (fun v i h => hte ⟨v, i, h⟩)
    exact ⟨q, hS.symm ▸ hqX, hq⟩

theorem t200inv1_hfact (hm : 1 ≤ m)
    (hU4 : ∀ y ∈ (F.S : Subgroup G), y * y = 1 → y ≠ 1 →
      y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      (∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1))) ∨
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {y} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32)
    (hR : ∀ y : G, IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) → ∀ A : Subgroup G,
      A ≤ Subgroup.centralizer {y} → (∀ x ∈ A, x * x = 1) → Nat.card A ≠ 32) :
    ∀ x ∈ (F.S : Subgroup G), IsConj ((dD.c : G) ^ 2 ^ (m - 1)) x →
      x ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
      ∃ q ∈ (F.S : Subgroup G),
        q⁻¹ * x * q = x * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  intro x hxS hcx hxw
  have hx2 : x * x = 1 :=
    Stroth42.mul_self_eq_one_of_isConj hcx.symm (Stroth47Fus.t200_c₁_mul_self dD hm)
  have hx1 : x ≠ 1 :=
    Stroth42.ne_one_of_isConj hcx.symm (Stroth47Fus.t200_c₁_ne_one dD hm)
  rcases hU4 x hxS hx2 hx1 hxw with ⟨q, hq, hq'⟩ | ⟨A, hA, hA2, hA32⟩
  · exact ⟨q, hq, hq'⟩
  · exact absurd hA32 (hR x hcx.symm A hA hA2)

theorem t200inv1_cabuv_beta {e : G} {j : ℕ} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2)
    (hR : ∀ y : G, IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) → ∀ A : Subgroup G,
      A ≤ Subgroup.centralizer {y} → (∀ x ∈ A, x * x = 1) → Nat.card A ≠ 32)
    (hU1 : (∃ A : Subgroup G, A ≤ Subgroup.centralizer {e} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32) ∧
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * e} ∧
        (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32) :
    ¬ IsConj (dD.u * e) ((dD.c : G) ^ 2 ^ (m - 1)) ∧
      ¬ IsConj ((dD.c : G) ^ 2 ^ (m - 1) * (dD.u * e))
        ((dD.c : G) ^ 2 ^ (m - 1)) := by
  let c₁ : G := (dD.c : G) ^ 2 ^ (m - 1)
  let a₁ : G := (dD.a : G) ^ 2 ^ (m + 1)
  let b₁ : G := (dD.b : G) ^ 2 ^ (m + 1)
  let w₀ : G := a₁ * b₁
  have hf : Even j := by
    rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2 ^ m, by rw [← two_mul, pow_succ']⟩
  have hU4 := t200inv1_hU4 (dD := dD) hm hS hj hrel
  have hfact := t200inv1_hfact (dD := dD) hm hU4 hR
  have hwFS : ∀ x ∈ (F.S : Subgroup G), x * w₀ = w₀ * x := by
    intro x hx
    have hx' := hx
    rw [hS] at hx'
    exact t200inv1_comm_w₀ dD hm hf hrel x hx'
  have hvw : IsConj (c₁ * dD.u) w₀ :=
    (h.t200_fusion).2.2.trans h.t200_isConj_w₀_a₁.symm
  have hc₁2 : c₁ * c₁ = 1 := Stroth47Fus.t200_c₁_mul_self dD hm
  have hc₁1 : c₁ ≠ 1 := Stroth47Fus.t200_c₁_ne_one dD hm
  have he1 : e ≠ 1 := fun h1 =>
    t200inv1_h2 dD hm hj hrel (by rw [h1]; exact Subgroup.one_mem _)
  have hue : dD.u * e = e * dD.u := (t200inv1_e_comm_u dD hrel).symm
  have huc₁ : dD.u * c₁ = c₁ * dD.u := t200inv1_u_comm_c₁ dD
  have hec₁ : c₁ * e = e * c₁ := (t200inv1_e_comm_c₁ dD hm hrel).symm
  have huS : dD.u ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hc₁S : c₁ ∈ (F.S : Subgroup G) := h.le_S (D.pow_mem dD.c.2 _)
  have hr1S : dD.u * e ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem huS heS
  have hr2S : c₁ * (dD.u * e) ∈ (F.S : Subgroup G) :=
    (F.S : Subgroup G).mul_mem hc₁S hr1S
  have hprod1 : (dD.u * e) * (c₁ * dD.u) = c₁ * e := by
    calc (dD.u * e) * (c₁ * dD.u)
        = (dD.u * e) * (dD.u * c₁) := by rw [← huc₁]
      _ = dD.u * (e * dD.u) * c₁ := by group
      _ = dD.u * (dD.u * e) * c₁ := by rw [← hue]
      _ = e * c₁ := by rw [← mul_assoc, dD.u_sq, one_mul]
      _ = c₁ * e := by rw [hec₁]
  have hprod1' : (c₁ * dD.u) * (dD.u * e) = c₁ * e := by
    calc (c₁ * dD.u) * (dD.u * e)
        = c₁ * (dD.u * dD.u) * e := by group
      _ = c₁ * e := by rw [dD.u_sq, mul_one]
  have hrv1 : (dD.u * e) * (c₁ * dD.u) = (c₁ * dD.u) * (dD.u * e) :=
    hprod1.trans hprod1'.symm
  have huS₁ : dD.u ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hc₁S₁ : c₁ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_left (D.pow_mem dD.c.2 _)
  have hcuS₁ : c₁ * dD.u ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    mul_mem hc₁S₁ huS₁
  have hne1 : dD.u * e ≠ c₁ * dD.u := by
    intro h1
    have heq : e = dD.u * (c₁ * dD.u) := by
      calc e = dD.u * (dD.u * e) := by rw [← mul_assoc, dD.u_sq, one_mul]
        _ = dD.u * (c₁ * dD.u) := by rw [h1]
    exact t200inv1_h2 dD hm hj hrel (by
      rw [heq]
      exact mul_mem huS₁ hcuS₁)
  have hnot1 : ¬ IsConj ((dD.u * e) * (c₁ * dD.u)) c₁ := by
    rw [hprod1]
    intro hc
    obtain ⟨A, hA, hA2, hA32⟩ := hU1.2
    exact hR (c₁ * e) hc A hA hA2 hA32
  have hβ1 : ¬ IsConj (dD.u * e) c₁ :=
    Stroth47Inv1.not_isConj_of_isConj_mul (S := F.S) (c₁ := c₁) (w₀ := w₀)
      (r := dD.u * e) (v := c₁ * dD.u) hwFS hfact hvw hr1S hrv1 hne1 hnot1
  have hprod2 : (c₁ * (dD.u * e)) * (c₁ * dD.u) = e := by
    calc (c₁ * (dD.u * e)) * (c₁ * dD.u)
        = c₁ * (dD.u * e) * c₁ * dD.u := by group
      _ = c₁ * (dD.u * (e * c₁)) * dD.u := by group
      _ = c₁ * (dD.u * (c₁ * e)) * dD.u := by rw [← hec₁]
      _ = c₁ * (dD.u * c₁) * e * dD.u := by group
      _ = c₁ * (c₁ * dD.u) * e * dD.u := by rw [huc₁]
      _ = c₁ * (c₁ * dD.u) * (e * dD.u) := by group
      _ = c₁ * (c₁ * dD.u) * (dD.u * e) := by rw [← hue]
      _ = (c₁ * c₁) * (dD.u * dD.u) * e := by group
      _ = e := by rw [hc₁2, dD.u_sq]; group
  have hprod2' : (c₁ * dD.u) * (c₁ * (dD.u * e)) = e := by
    calc (c₁ * dD.u) * (c₁ * (dD.u * e))
        = c₁ * (dD.u * c₁) * (dD.u * e) := by group
      _ = c₁ * (c₁ * dD.u) * (dD.u * e) := by rw [huc₁]
      _ = (c₁ * c₁) * (dD.u * dD.u) * e := by group
      _ = e := by rw [hc₁2, dD.u_sq]; group
  have hrv2 : (c₁ * (dD.u * e)) * (c₁ * dD.u) = (c₁ * dD.u) * (c₁ * (dD.u * e)) :=
    hprod2.trans hprod2'.symm
  have hne2 : c₁ * (dD.u * e) ≠ c₁ * dD.u := by
    intro h1
    have h2 : dD.u * e = dD.u := mul_left_cancel h1
    have h3 : e = 1 := by
      calc e = dD.u * (dD.u * e) := by rw [← mul_assoc, dD.u_sq, one_mul]
        _ = dD.u * dD.u := by rw [h2]
        _ = 1 := dD.u_sq
    exact he1 h3
  have hnot2 : ¬ IsConj ((c₁ * (dD.u * e)) * (c₁ * dD.u)) c₁ := by
    rw [hprod2]
    intro hc
    obtain ⟨A, hA, hA2, hA32⟩ := hU1.1
    exact hR e hc A hA hA2 hA32
  have hβ2 : ¬ IsConj (c₁ * (dD.u * e)) c₁ :=
    Stroth47Inv1.not_isConj_of_isConj_mul (S := F.S) (c₁ := c₁) (w₀ := w₀)
      (r := c₁ * (dD.u * e)) (v := c₁ * dD.u) hwFS hfact hvw hr2S hrv2 hne2 hnot2
  exact ⟨hβ1, hβ2⟩

theorem t200inv1_cabuv_isConj_a₁ {e : G} {j : ℕ} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2) :
    IsConj (dD.cab * dD.uv) ((dD.a : G) ^ 2 ^ (m + 1)) := by
  let c₁ : G := (dD.c : G) ^ 2 ^ (m - 1)
  let a₁ : G := (dD.a : G) ^ 2 ^ (m + 1)
  have hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
      ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G) :=
    fun Q hQ hQz => h.t200_inv1_conj_le_S hm hSN hnc hS hj hrel hQ hQz
  have hR := t200inv1_hR (dD := dD) hm hS hj hrel hsyl
  have hU1 := t200inv1_elab32_e dD hm hj hrel
  have hDu := h.t200_isConj_of_mem_Du hm
  have hu : IsConj dD.u c₁ := (h.t200_fusion).2.1
  have hx2 : dD.cab * dD.uv * (dD.cab * dD.uv) = 1  := dD.t200_cab_uv_mul_self
  have hx1 : dD.cab * dD.uv ≠ 1 := t200inv1_cabuv_ne_one (dD := dD) hm
  have hux : dD.u * (dD.cab * dD.uv) = (dD.cab * dD.uv) * dD.u :=
    dD.t200_u_comm_cab_uv
  have hxuu : IsConj (dD.u * (dD.cab * dD.uv)) dD.u := dD.t200_isConj_u_mul_cab_uv
  have hx32 := t200inv1_cabuv_hx32 (dD := dD) hm hj hrel
  have hS32 : ∀ A : Subgroup G,
      A ≤ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁} →
        (∀ y ∈ A, y * y = 1) → Nat.card A ≠ 32 := by
    intro A hA hA2 hA32
    have h16 := t200inv1_card_le_sixteen_S (dD := dD) hm hS hj hrel hA hA2
    omega
  by_cases hm2 : 2 ≤ m
  · have hc₂ : ∀ k ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁},
        k ∉ D ⊔ Subgroup.zpowers dD.u →
          ((dD.c : G) ^ 2 ^ (m - 2))⁻¹ * k * ((dD.c : G) ^ 2 ^ (m - 2)) = c₁ * k := by
      intro k hk hkDu
      have hk' := hk
      rw [hS] at hk'
      exact t200inv1_conj_c₂ dD hm2 hrel k hk' hkDu
    exact Stroth47Inv1.cabuv_isConj_of_two_le (S := (F.S : Subgroup G))
      (T := (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁})
      (Du := D ⊔ Subgroup.zpowers dD.u) (c₁ := c₁)
      (c₂ := (dD.c : G) ^ 2 ^ (m - 2)) (a₁ := a₁) (u := dD.u)
      (x := dD.cab * dD.uv) rfl hsyl hS32 hDu hc₂ hu hux hx2 hx1 hxuu hx32
  · have hm1 : m = 1 := by omega
    have hβ := t200inv1_cabuv_beta (dD := dD) h hm hS hj hrel hR hU1
    have hT1 := t200inv1_isConj_of_mul_one (dD := dD) hm1 hj hrel hR hU1 hβ
    have hT1' : ∀ k ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁},
        k ∉ D ⊔ Subgroup.zpowers dD.u → k * k = 1 →
          IsConj (c₁ * k) c₁ → IsConj k c₁ := by
      intro k hk hkDu hk2 hkconj
      have hk' := hk
      rw [hS] at hk'
      exact hT1 k hk' hkDu hk2 hkconj
    exact Stroth47Inv1.cabuv_isConj_of_isConj_mul (S := (F.S : Subgroup G))
      (T := (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁})
      (Du := D ⊔ Subgroup.zpowers dD.u) (c₁ := c₁) (a₁ := a₁) (u := dD.u)
      (x := dD.cab * dD.uv) rfl hsyl hS32 hDu hT1' hu hux hx2 hx1 hxuu hx32

theorem t200inv1_isConj_of_mem_S₁_a₁ {e : G} {j : ℕ} (h : F.IsD D dD) (hm : 1 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 → y ≠ 1 →
      IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) ∨
        IsConj y ((dD.a : G) ^ 2 ^ (m + 1)) := by
  intro y hy hy2 hy1
  rcases h.t200_isConj_of_mem_S₁ hm y hy hy2 hy1 with hc | ha | hcab
  · exact Or.inl hc
  · exact Or.inr ha
  · exact Or.inr (hcab.trans (t200inv1_cabuv_isConj_a₁ (dD := dD) h hm hSN hnc hS hj hrel))

theorem false_of_t200_inv1_p_two (h : F.IsD D dD) (hm : 1 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    {e : G}
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    {j : ℕ} (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 2) :
    False := by
  have hf : Even j := by
    rcases hj with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨2 ^ m, by rw [← two_mul, pow_succ']⟩
  have hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
      ∃ k ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G) :=
    fun Q hQ hQz => h.t200_inv1_conj_le_S hm hSN hnc hS hj hrel hQ hQz
  have hR := t200inv1_hR (dD := dD) hm hS hj hrel hsyl
  have hU1 := t200inv1_elab32_e dD hm hj hrel
  have hU4 := t200inv1_hU4 (dD := dD) hm hS hj hrel
  have hI1 := t200inv1_isConj_of_mem_S₁_a₁ (dD := dD) h hm hSN hnc hS hj hrel
  have hw : ∀ y ∈ (F.S : Subgroup G),
      y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
        (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
    intro y hy
    have hy' := hy
    rw [hS] at hy'
    exact t200inv1_comm_w₀ dD hm hf hrel y hy'
  have hc₁e : (dD.c : G) ^ 2 ^ (m - 1) * e =
      e * (dD.c : G) ^ 2 ^ (m - 1) := (t200inv1_e_comm_c₁ dD hm hrel).symm
  have h1S : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (F.S : Subgroup G) = 2 := by
    rw [hS]
    exact t200inv1_h1 dD hm hj hrel
  exact h.false_of_t200_inv1_ii_v hm hS hrel.e_sq hc₁e
    h1S (t200inv1_h2 dD hm hj hrel)
    hw h.t200_isConj_w₀_a₁ hI1 hR hU1 hU4

theorem false_of_t200_inv1_p_odd (h : F.IsD D dD) (hm : 1 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    {e : G}
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    {p : ℕ} (hp : Odd p) (hrel : Rel34inv dD e 0 1 p) :
    False := by
  let c₁ : G := (dD.c : G) ^ 2 ^ (m - 1)
  let a₁ : G := (dD.a : G) ^ 2 ^ (m + 1)
  let b₁ : G := (dD.b : G) ^ 2 ^ (m + 1)
  let w₀ : G := a₁ * b₁
  let k : G := dD.u * e
  have hj0 : (0 : ℕ) = 0 ∨ (0 : ℕ) = 2 ^ (m + 1) := Or.inl rfl
  have hf : Even (0 : ℕ) := ⟨0, rfl⟩
  have hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} →
      ∃ x ∈ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
        ∀ q ∈ Q, x⁻¹ * q * x ∈ (F.S : Subgroup G) :=
    fun Q hQ hQz => h.t200_inv1_conj_le_S hm hSN hnc hS hj0 hrel hQ hQz
  have huS : dD.u ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have heS : e ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have huS₁ : dD.u ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hc₁S₁ : c₁ ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    Subgroup.mem_sup_left (D.pow_mem dD.c.2 _)
  have hc₁S : c₁ ∈ (F.S : Subgroup G) := h.le_S (D.pow_mem dD.c.2 _)
  have hw₀S : w₀ ∈ (F.S : Subgroup G) :=
    h.le_S (D.mul_mem (D.pow_mem dD.a.2 _) (D.pow_mem dD.b.2 _))
  have hw : ∀ y ∈ (F.S : Subgroup G), y * w₀ = w₀ * y := by
    intro y hy
    have hy' := hy
    rw [hS] at hy'
    exact t200inv1_comm_w₀ dD hm hf hrel y hy'
  have hw₀2 : w₀ * w₀ = 1 := by
    rw [show w₀ = dD.ofTorus (om200 m ![0, 1, 1]) from (t200inv1_w0_eq dD).symm,
      dD.ofTorus_mul_self, om200_add_self hm, dD.ofTorus_zero]
  have hw₀1 : w₀ ≠ 1 :=
    Stroth42.ne_one_of_isConj h.t200_isConj_w₀_a₁ (Stroth47Fus.t200_a₁_ne_one dD)
  have hc₁w₀ : ¬ IsConj c₁ w₀ :=
    fun hc => h.t200_not_isConj_c₁_a₁ hm hnc (hc.trans h.t200_isConj_w₀_a₁)
  have huvS : dD.uv ∈ (F.S : Subgroup G) := by
    rw [hS]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hx₀c₁ : dD.uv⁻¹ * c₁ * dD.uv = c₁ * w₀ := dD.t200_uv_conj_c₁ hm
  have hue : dD.u * e = e * dD.u := (t200inv1_e_comm_u dD hrel).symm
  have huc₁ : dD.u * c₁ = c₁ * dD.u := t200inv1_u_comm_c₁ dD
  have hec₁ : c₁ * e = e * c₁ := (t200inv1_e_comm_c₁ dD hm hrel).symm
  have hc₁2 : c₁ * c₁ = 1 := Stroth47Fus.t200_c₁_mul_self dD hm
  have hc₁1 : c₁ ≠ 1 := Stroth47Fus.t200_c₁_ne_one dD hm
  have hkS : k ∈ (F.S : Subgroup G) := (F.S : Subgroup G).mul_mem huS heS
  have hkc₁comm : k * c₁ = c₁ * k := by
    calc (dD.u * e) * c₁ = dD.u * (e * c₁) := by group
      _ = dD.u * (c₁ * e) := by rw [← hec₁]
      _ = dD.u * c₁ * e := by group
      _ = c₁ * dD.u * e := by rw [huc₁]
      _ = c₁ * (dD.u * e) := by group
  have hkT : k ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁} :=
    Subgroup.mem_inf.2 ⟨hkS, Subgroup.mem_centralizer_singleton_iff.2 hkc₁comm⟩
  have hkDk : k ∈ D ⊔ Subgroup.zpowers k :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
  have hkS₁ : k ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
    intro hk'
    apply t200inv1_h2 dD hm hj0 hrel
    have heq : e = dD.u * k := by
      change e = dD.u * (dD.u * e)
      rw [← mul_assoc, dD.u_sq, one_mul]
    rw [heq]
    exact mul_mem huS₁ hk'
  have hDuS₁ : D ⊔ Subgroup.zpowers dD.u ≤
      D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
    refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hkDu : k ∉ D ⊔ Subgroup.zpowers dD.u := fun hk' => hkS₁ (hDuS₁ hk')
  have hk2 : k * k = 1 := by
    calc (dD.u * e) * (dD.u * e) = dD.u * (e * dD.u) * e := by group
      _ = dD.u * (dD.u * e) * e := by rw [← hue]
      _ = (dD.u * dD.u) * (e * e) := by group
      _ = 1 := by rw [dD.u_sq, hrel.e_sq, mul_one]
  have hkc₁ : k ≠ c₁ := by
    intro h1
    apply t200inv1_h2 dD hm hj0 hrel
    have heq : e = dD.u * c₁ := by
      calc e = dD.u * (dD.u * e) := by rw [← mul_assoc, dD.u_sq, one_mul]
        _ = dD.u * k := rfl
        _ = dD.u * c₁ := by rw [h1]
    rw [heq]
    exact mul_mem huS₁ hc₁S₁
  have hK4 : ∀ l ∈ (F.S : Subgroup G), l * l = 1 → l ≠ 1 → l ≠ w₀ →
      ∃ q ∈ (F.S : Subgroup G), q⁻¹ * l * q = l * w₀ := by
    intro l hlS hl2 hl1 hlw
    have hl' := hlS
    rw [hS] at hl'
    obtain ⟨q, hqX, hq⟩ := t200inv1_conj_mul_w₀ dD hm hj0 hrel l hl' hl2 hl1 hlw
      (fun v i h => t200inv1_te_mul_self_ne dD hm hp hrel v i (h ▸ hl2))
    exact ⟨q, hS.symm ▸ hqX, hq⟩
  have hq : IsConj k (c₁ * k) := by
    obtain ⟨q, -, hq⟩ := t200inv1_conj_ue dD hm hp hrel
    exact isConj_iff.2 ⟨q⁻¹, by simpa using hq⟩
  have hnonab := Stroth42.frame_exists_mul_ne F
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁_le : D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ≤ (F.S : Subgroup G) := by
    rw [hS]
    exact le_sup_left
  have h1S : (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).relIndex
      (F.S : Subgroup G) = 2 := by
    rw [hS]
    exact t200inv1_h1 dD hm hj0 hrel
  have hk1 : k ≠ 1 := fun h1 => hkDu (h1 ▸ Subgroup.one_mem _)
  have hkord : orderOf k = 2 :=
    @orderOf_eq_prime G _ k 2 hFact (by rw [pow_two]; exact hk2) hk1
  obtain ⟨g, hg⟩ := @EvenSporadicStandard.exists_conj_mem_complement G _ _ F.simple hnonab
    (S := (F.S : Subgroup G)) (U := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u})
    F.S.isPGroup' F.S.not_dvd_index hS₁_le h1S (t := k) hkS hkS₁ hkord
  let y : G := g⁻¹ * k * g
  have hyS₁ : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := hg
  have hy2 : y * y = 1 := by
    rw [show y = g⁻¹ * k * g from rfl]
    calc g⁻¹ * k * g * (g⁻¹ * k * g) = g⁻¹ * (k * k) * g := by group
      _ = 1 := by rw [hk2]; group
  have hy1 : y ≠ 1 := by
    intro h1
    apply hk1
    have hyk : g * y * g⁻¹ = k := by
      change g * (g⁻¹ * k * g) * g⁻¹ = k
      group
    rw [h1] at hyk
    simpa using hyk.symm
  have hky : IsConj k y := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    rw [inv_inv]
  have htype : IsConj k c₁ ∨ IsConj k w₀ := by
    rcases h.t200_isConj_of_mem_S₁ hm y hyS₁ hy2 hy1 with hyc | hya | hycab
    · exact Or.inl (hky.trans hyc)
    · exact Or.inr (hky.trans (hya.trans h.t200_isConj_w₀_a₁.symm))
    · refine Or.inr (hky.trans (hycab.trans ?_))
      have huv1 : dD.uv ≠ 1 := fun h1 => F.uv_not_mem_centralizer_A (by
        rw [← h.uv_eq, h1]; exact Subgroup.one_mem _)
      have huv_a₁ : IsConj dD.uv ((dD.a : G) ^ 2 ^ (m + 1)) :=
        (h.t200_fusion).1 dD.uv (Subgroup.subset_closure (by simp)) huv1
      have hcabuv_uv : IsConj (dD.cab * dD.uv) dD.uv := by
        obtain ⟨q, -, hq⟩ := t200inv1_conj_cab_uv dD hm hp hrel
        exact isConj_iff.2 ⟨q⁻¹, by simpa using hq⟩
      exact (hcabuv_uv.trans huv_a₁).trans h.t200_isConj_w₀_a₁.symm
  have hk : IsConj k c₁ :=
    Stroth47Inv1.isConj_of_isConj_mul (S := F.S) hc₁S hc₁2 hc₁1 hw hK4 hc₁w₀
      hkc₁comm (fun h1 => hkc₁ h1.symm) hq htype
  have hc₁k : IsConj (c₁ * k) c₁ := hq.symm.trans hk
  have hDu := h.t200_not_isConj_c₁_mul_of_mem_Du hm hnc
  have hT4 : ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁},
      y ∉ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
      Nat.card ((((F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁}) ⊓
          Subgroup.centralizer {y}) : Subgroup G) ≤
        Nat.card ((((F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁}) ⊓
          Subgroup.centralizer {k}) : Subgroup G) := by
    intro y hy hyDu hy2
    have hy' := hy
    rw [hS] at hy'
    have hc := t200inv1_card_centralizer_le dD hm hj0 hrel y hy' hyDu hy2
    simpa [hS] using hc
  have hDk : ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁},
      y ∉ D ⊔ Subgroup.zpowers dD.u → y * y = 1 → y ∉ D ⊔ Subgroup.zpowers k →
      Nat.card ((((F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁}) ⊓
          Subgroup.centralizer {y}) : Subgroup G) <
        Nat.card ((((F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁}) ⊓
          Subgroup.centralizer {k}) : Subgroup G) := by
    intro y hy hyDu hy2 hyDk
    have hy' := hy
    rw [hS] at hy'
    have hc := t200inv1_card_centralizer_lt dD hm hj0 hrel y hy' hyDu hy2 hyDk
    simpa [hS] using hc
  have hZ : ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁} ⊓
        Subgroup.centralizer {k},
      (∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁} ⊓
          Subgroup.centralizer {k}, z * y = y * z) →
        z = 1 ∨ z = c₁ ∨ z = w₀ ∨ z = c₁ * w₀ ∨ z = k ∨ z = c₁ * k ∨ z = w₀ * k ∨
          z = c₁ * w₀ * k := by
    intro z hz hzc
    have hz' := hz
    rw [hS] at hz'
    have hzc' : ∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
          Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
          Subgroup.centralizer {dD.u * e}, z * y = y * z := by
      intro y hy
      exact hzc y (by simpa [hS] using hy)
    have hz2 := t200inv1_center_ue dD hm hj0 hrel z hz' hzc'
    simpa only [k] using hz2
  have ha₁ : a₁ ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁} := by
    have ha₁D : a₁ ∈ D := D.pow_mem dD.a.2 _
    have hc₁D : c₁ ∈ D := D.pow_mem dD.c.2 _
    have hcomm : a₁ * c₁ = c₁ * a₁ :=
      congrArg Subtype.val
        (dD.isMulCommutative.is_comm.comm ⟨a₁, ha₁D⟩ ⟨c₁, hc₁D⟩)
    exact Subgroup.mem_inf.2 ⟨h.le_S ha₁D,
      Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  have hT6 := t200inv1_conj_a₁ dD hm hj0 hrel
  have hT78 : ∀ y ∈ D ⊔ Subgroup.zpowers k, y ∉ D ⊔ Subgroup.zpowers dD.u →
      y * y = 1 → ∀ x ∈ (F.S : Subgroup G), x * y = y * x → x * c₁ = c₁ * x := by
    intro y hy hyDu hy2 x hxS hxy
    have hx' := hxS
    rw [hS] at hx'
    exact t200inv1_comm_c₁_of_comm dD hm hp hrel y hy hyDu hy2 x hx' hxy
  exact Stroth47Inv1.false_of_swap (S := (F.S : Subgroup G))
    (T := (F.S : Subgroup G) ⊓ Subgroup.centralizer {c₁})
    (Du := D ⊔ Subgroup.zpowers dD.u) (Dk := D ⊔ Subgroup.zpowers k)
    (c₁ := c₁) (w₀ := w₀) (x₀ := dD.uv) (a₁ := a₁) (k := k)
    F.S.isPGroup' rfl hsyl hc₁S hw₀S hw hw₀2 hw₀1 hc₁w₀ huvS hx₀c₁
    hkT hkDk hkDu hk2 hkc₁ hk hc₁k hDu hT4 hDk ha₁ hT6 hZ hT78

end StrothFrame.IsD

theorem stroth_4_7_inv1 {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G}
    {m : ℕ} (hm : 1 ≤ m) (dD : StrothWeakTypeData D (.t200 m)) (h : F.IsD D dD)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    (e : G)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hrel : Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
      Rel34inv dD e (2 ^ (m + 1)) 1 2) :
    False := by
  rcases hrel with h2 | h1 | h3 | h5
  · exact h.false_of_t200_inv1_p_two hm hSN hnc hS (Or.inl rfl) h2
  · exact h.false_of_t200_inv1_p_odd hm hSN hnc hS (p := 1) ⟨0, by norm_num⟩ h1
  · exact h.false_of_t200_inv1_p_odd hm hSN hnc hS (p := 3) ⟨1, by norm_num⟩ h3
  · exact h.false_of_t200_inv1_p_two hm hSN hnc hS (Or.inr rfl) h5

end CFSG.CGT.Stroth77
