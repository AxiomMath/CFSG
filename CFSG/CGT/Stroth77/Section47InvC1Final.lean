module

public import CFSG.CGT.Stroth77.Section47Inv
public import CFSG.CGT.Stroth77.Section47InvE16
public import CFSG.CGT.Stroth77.Section47Harada

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core StrothWeakTypeData

variable {G : Type} [Group G] [Finite G]

namespace Stroth47Core

variable {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m)) {e : G}

theorem t200inv_sqE_ne_zero (hm : 2 ≤ m) {p : ℕ} (hp : p % 2 = 1)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    (x : Fin 3 → ℤ) (i j l : Bool) (hlj : (l && j) = false) :
    (dD.t200invEAction hrel).sqE (Torus.ofInt _ x) i j l ≠ 0 := by
  intro h0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hQ : (0 : ℤ) < 2 ^ m' := by positivity
  have e0 : m' + 2 - 1 = m' + 1 := rfl
  have e1 : (2 : ℤ) ^ (m' + 2) = 4 * 2 ^ m' := by
    rw [pow_add]; norm_num; ring
  have e4 : (2 : ℤ) ^ (m' + 1) = 2 * 2 ^ m' := by
    rw [pow_add]; norm_num; ring
  have e5 : (2 : ℤ) ^ (m' * 2) = (2 ^ m') ^ 2 := by
    rw [pow_mul]
  have e2 : (2 : ℤ) ^ (m' + 2 + 1) = 8 * 2 ^ m' := by
    rw [pow_add]; norm_num; ring
  have e3 : (2 : ℤ) ^ (m' + 2 + 2) = 16 * 2 ^ m' := by
    rw [pow_add]; norm_num; ring
  have hwuv : (dD.t200invEAction hrel).wuv =
      Torus.ofInt _ ![(p : ℤ), (p : ℤ), (p : ℤ)] := rfl
  have hwt : (dD.t200invEAction hrel).wt = Torus.ofInt _ ![0, -(p : ℤ), 0] := rfl
  obtain hi | hi := Bool.eq_false_or_eq_true i <;>
  obtain hj | hj := Bool.eq_false_or_eq_true j <;>
  obtain hl | hl := Bool.eq_false_or_eq_true l <;>
  simp only [hi, hj, hl, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at * <;>
  (try exact absurd hlj (by decide)) <;>
    simp only [EAction.sqE, EAction.twist, hwuv, hwt, t200invEAction_ve, e0,
      SigmaFourAction.d8Act, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      Bool.false_eq_true, Bool.true_eq_false, Bool.and_false, Bool.and_true, ↓reduceIte,
      map_zero, e4, t200_φuv, t200_φt, t200_φu, t200inv_φe dD hrel, ← Torus.ofInt_add, ← Torus.ofInt_sub,
      add_zero, zero_add] at h0 <;>
    (first
      | rw [t200_ofInt_eq_zero_iff] at h0
      | rw [eq_comm] at h0; rw [t200_ofInt_eq_zero_iff] at h0) <;>
    obtain ⟨d0, d1, d2⟩ := h0 <;>
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, e1, e2, e3, e5] at d0 d1 d2 <;>
    ring_nf at d0 d1 d2 <;>
    set Q : ℤ := 2 ^ m' with hQdef <;>
    have hQ2 : (2 : ℤ) ^ (m' * 2) = Q ^ 2 := by rw [hQdef]; exact e5 <;>
    simp only [hQ2] at d0 d1 d2
  ·
    obtain ⟨k0, hk0⟩ := d0
    obtain ⟨k1, hk1⟩ := d1
    have h : (4 * Q) * (1 - 2 * x 1) = (4 * Q) * (2 * (k0 - 2 * k1)) := by
      linear_combination 2 * hk0 - hk1
    have h1 : (1 : ℤ) = 2 * (k0 - 2 * k1 + x 1) := by
      have h2 := mul_left_cancel₀ (by positivity : (4 * Q : ℤ) ≠ 0) h
      linarith
    omega

  ·
    obtain ⟨k1, hk1⟩ := d1
    obtain ⟨k2, hk2⟩ := d2
    have hdiff : 8 * Q * (x 1 - x 2) = 16 * Q * (k1 - k2) := by
      linear_combination hk1 - hk2
    have hx : x 1 - x 2 = 2 * (k1 - k2) := by
      have h := hdiff
      rw [show (16 : ℤ) * Q * (k1 - k2) = 8 * Q * (2 * (k1 - k2)) by ring] at h
      exact mul_left_cancel₀ (by positivity : (8 * Q : ℤ) ≠ 0) h
    have hx' : x 1 = x 2 + 2 * (k1 - k2) := by linarith
    rw [hx'] at hk1
    have h2p : (2 : ℤ) ∣ (p : ℤ) := by
      refine ⟨4 * Q + 96 * Q ^ 2 + 2 * x 0 + (-1 + 12 * Q) * x 2 +
        (k1 - k2) * (-1 + 16 * Q) - 8 * Q * k1, ?_⟩
      linear_combination -hk1
    obtain ⟨c, hc⟩ := h2p
    have hpodd : Odd p := Nat.odd_iff.mpr hp
    obtain ⟨q, hq⟩ := hpodd
    rw [hq] at hc
    push_cast at hc
    omega
  ·
    obtain ⟨k1, hk1⟩ := d1
    have h2p : (2 : ℤ) ∣ (p : ℤ) := by
      refine ⟨2 * x 0 + 4 * Q * x 1 + (-1 + 8 * Q) * x 2 + 4 * Q + 96 * Q ^ 2 - 8 * Q * k1,
        ?_⟩
      linear_combination -hk1
    obtain ⟨c, hc⟩ := h2p
    have hpodd : Odd p := Nat.odd_iff.mpr hp
    obtain ⟨q, hq⟩ := hpodd
    rw [hq] at hc
    push_cast at hc
    omega
  ·
    obtain ⟨k0, hk0⟩ := d0
    obtain ⟨k2, hk2⟩ := d2
    have h : (4 * Q) * (1 - 2 * x 2) = (4 * Q) * (2 * (k0 - 2 * k2)) := by
      linear_combination 2 * hk0 - hk2
    have h1 : (1 : ℤ) = 2 * (k0 - 2 * k2 + x 2) := by
      have h2 := mul_left_cancel₀ (by positivity : (4 * Q : ℤ) ≠ 0) h
      linarith
    omega
  ·
    obtain ⟨k, hk⟩ := d0
    have h1 : (1 : ℤ) = 2 * k := by
      have h : (2 * Q) * 1 = (2 * Q) * (2 * k) := by linear_combination hk
      exact mul_left_cancel₀ (by positivity : (2 * Q : ℤ) ≠ 0) h
    omega
  ·
    obtain ⟨k, hk⟩ := d0
    have h1 : (1 : ℤ) = 2 * k := by
      have h : (2 * Q) * 1 = (2 * Q) * (2 * k) := by linear_combination hk
      exact mul_left_cancel₀ (by positivity : (2 * Q : ℤ) ≠ 0) h
    omega

theorem t200inv_mem_of_mul_self (hm : 2 ≤ m) {p : ℕ} (hp : p % 2 = 1)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p)
    {y : G}
    (hy : y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hyy : y * y = 1) :
    y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  have hm1 : 1 ≤ m := by omega
  let hE := dD.t200invEAction hrel
  obtain ⟨v, i, j, l, k, rfl⟩ := hE.mem_sup_zpowers_iff.mp hy
  cases k
  · simpa [bpow] using dD.nf_mem v i j l
  · simp only [bpow, ↓reduceIte] at hyy
    rw [hE.nfe_e_mul_self] at hyy
    by_cases hlj : (l && j) = true
    · exfalso
      rw [hlj, dD.d8_tff] at hyy
      have huvD : dD.uv ∈ D := by
        have h1 : dD.uv = (dD.ofTorus (hE.sqE v i j l))⁻¹ :=
          eq_inv_of_mul_eq_one_right hyy
        rw [h1]
        exact D.inv_mem (dD.ofTorus_mem _)
      exact (dD.d8_not_mem (t200_faithful hm1) (i := true) (j := false) (l := false)
        (by decide) (0 : Torus (StrothTypeIndex.t200 m).k))
        (by simpa [dD.d8_tff, dD.ofTorus_zero, one_mul] using huvD)
    · exfalso
      have hlj' : (l && j) = false := by
        cases l <;> cases j <;> simp_all
      rw [hlj', d8_fff, mul_one] at hyy
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      exact absurd (dD.ofTorus_eq_one_iff.mp hyy)
        (t200inv_sqE_ne_zero dD hm hp hrel x i j l hlj')

end Stroth47Core

theorem stroth_4_7_hinv_c1 :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧ ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) → False := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel
  haveI := F.simple
  have hm1 : 1 ≤ m := by omega
  obtain ⟨p, hp, hrelp⟩ : ∃ p : ℕ, p % 2 = 1 ∧
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) p :=
    hrel.elim (fun h' => ⟨1, by norm_num, h'⟩) (fun h' => ⟨3, by norm_num, h'⟩)
  set U : Subgroup G := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} with hUdef
  have heN : e ∈ Subgroup.normalizer (U : Set G) := by
    rw [hUdef]
    exact (dD.t200invEAction hrelp).mem_normalizer
  have he2U : e * e ∈ U := by
    rw [hrelp.e_sq]
    exact Subgroup.mem_sup_left (D.pow_mem dD.c.2 _)
  have heU : e ∉ U := by
    have h1 := stroth_4_7_inv_conj_notMem_all F hm dD h hSN hnc e he hS hrel 1
    simpa [hUdef] using h1
  have hUidx : U.relIndex (F.S : Subgroup G) = 2 := by
    rw [hS]
    exact Stroth47.relIndex_sup_zpowers_of_mul_self_mem heN he2U heU
  have hc₁ : ∀ g : G, g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈ (F.S : Subgroup G) →
      g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈ U := by
    intro g hg
    have hyy : (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) *
        (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) = 1 := by
      rw [show g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g *
          (g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g) =
          g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * (dD.c : G) ^ 2 ^ (m - 1)) * g by group,
        Stroth47Fus.t200_c₁_mul_self dD hm1]
      group
    have hg' : g⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) * g ∈
        D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
      rw [← hUdef]
      rw [← hS]
      exact hg
    exact Stroth47Core.t200inv_mem_of_mul_self dD hm hp hrelp hg' hyy
  refine false_of_t200_inv_of_noConj (Stroth42.frame_exists_mul_ne F) F.S ?_ hUidx ?_ heU ?_
    (stroth_4_7_inv_conj_notMem_all F hm dD h hSN hnc e he hS hrel)
  · rw [hS]
    exact le_sup_left
  · rw [hS]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  · intro g k hmem
    have h1 : e ^ (2 * k) = ((dD.c : G) ^ 2 ^ (m - 1)) ^ k := by
      rw [pow_mul, pow_two, hrelp.e_sq]
    rcases H47Inv_c₁_pow dD hm1 k with hk | hk
    · rw [h1, hk]
      simpa using U.one_mem
    · rw [h1, hk] at hmem ⊢
      exact hc₁ g hmem

end CFSG.CGT.Stroth77
