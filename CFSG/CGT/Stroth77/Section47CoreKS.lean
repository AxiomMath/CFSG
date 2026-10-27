module

public import CFSG.CGT.Stroth77.Section47CoreKH

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 StrothWeakTypeData

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {e f : G} {p : ℕ}

theorem t200k_sqE_ne_zero (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) (hm : 1 ≤ m) (hp : p % 2 = 1)
    (x0 x1 x2 : ℤ) {i j l : Bool} (hlj : (l && j) = false) :
    (dD.t200gEAction hrel_e hrel_f hconj).sqE (Torus.ofInt _ ![x0, x1, x2]) i j l ≠ 0 := by
  intro h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
  simp only [EAction.sqE, EAction.twist, t200gEAction_ve, t200gEAction_wuv, t200gEAction_wt,
    Nat.add_sub_cancel] at h
  cases i <;> cases j <;> cases l <;> simp only [Bool.and_true, Bool.and_false] at hlj <;>
  (try exact absurd hlj (by decide)) <;>
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, Bool.and_false, Bool.and_true, map_add, map_sub, map_zero,
    t200gEAction_φe_apply, t200_φuv, t200_φt, t200_φu, ← Torus.ofInt_add, ← Torus.ofInt_sub,
    add_zero, zero_add, t200_ofInt_eq_zero_iff, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h <;>
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h <;>
  push_cast at hk0 hk1 hk2
  ·
    have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * k0) := by linear_combination hk0
    have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
    omega
  ·
    have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * k0) := by linear_combination hk0
    have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
    omega
  ·
    have : 2 * (2 * x1 * 2 ^ m' + 4 * x2 * 2 ^ m' - 8 * 2 ^ m' * 2 ^ m' + 4 * 2 ^ m' * r -
        4 * 2 ^ m' * k1 - 2 * x0 + x1 + x2 + r + 1) + 1 = (0 : ℤ) := by
      linear_combination hk1
    omega
  ·
    have : 2 * (-2 * x1 * 2 ^ m' - 4 * x2 * 2 ^ m' - 24 * 2 ^ m' * 2 ^ m' + 12 * 2 ^ m' * r -
        4 * 2 ^ m' * k1 + 2 * x0 - x2 + 8 * 2 ^ m' - r - 2) + 1 = (0 : ℤ) := by
      linear_combination hk1
    omega
  ·
    have h' : (4 * 2 ^ m' : ℤ) * (x1 - x2) = 4 * 2 ^ m' * (-2 * (k1 - k2)) := by
      linear_combination hk2 - hk1
    have h'' := mul_left_cancel₀ (by positivity : (4 * 2 ^ m' : ℤ) ≠ 0) h'
    have hd : x1 = x2 - 2 * (k1 - k2) := by linarith
    have : 2 * (-6 * x2 * 2 ^ m' - 24 * 2 ^ m' * 2 ^ m' + 12 * 2 ^ m' * r + 4 * 2 ^ m' * k1 -
        8 * 2 ^ m' * k2 + 2 * x0 - x2 + 8 * 2 ^ m' - r + k1 - k2 - 2) + 1 = (0 : ℤ) := by
      linear_combination hk1 + (8 * 2 ^ m' + 1) * hd
    omega
  ·
    have hx1 : x1 = 2 * 2 ^ m' * (2 * k1 - x1) :=
      mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
        (show (2 : ℤ) * x1 = 2 * (2 * 2 ^ m' * (2 * k1 - x1)) by linear_combination hk1)
    have h3 : (2 : ℤ) ^ m' * (8 * 2 ^ m' * (2 * k1 - x1) + 2 * (2 * k1 - x1) - 8 * r - 3) =
        2 ^ m' * (2 * k0) := by
      linear_combination hk0 - (4 * 2 ^ m' + 1) * hx1
    have h4 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h3
    have : 2 * (4 * 2 ^ m' * (2 * k1 - x1) + (2 * k1 - x1) - 4 * r - 2 - k0) + 1 = (0 : ℤ) := by
      linear_combination h4
    omega

theorem t200k_h6' (hm : 1 ≤ m) (hp : p % 2 = 1) (heN : e ∈ Subgroup.normalizer (D : Set G))
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f ⊔ Subgroup.zpowers e,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers f → y * y ≠ 1 := by
  intro y hy hyU hyy
  obtain ⟨w, hw, k, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem
    (t200k_mem_normalizer dD heN hfN hrel_e hrel_f hconj) (t200k_e_mul_self_mem dD hrel_e)).mp hy
  cases k
  · exact hyU (by simpa [bpow] using hw)
  simp only [bpow, ↓reduceIte] at hyy hyU
  obtain ⟨v, i, j, l, k', rfl⟩ := (dD.t200fEAction hrel_f).mem_sup_zpowers_iff.mp hw
  cases k'
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hyy hyU
    refine t200_i_h6' dD hm hrel_e _ ?_ ?_ hyy
    · exact mul_mem (Subgroup.mem_sup_left (dD.nf_mem v i j l))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · intro hmem
      apply t200_i_h2 dD hm hrel_e
      have := (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).mul_mem
        ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}).inv_mem (dD.nf_mem v i j l)) hmem
      rwa [inv_mul_cancel_left] at this
  · simp only [bpow, ↓reduceIte] at hyy
    rw [show dD.ofTorus v * dD.d8 i j l * f * e * (dD.ofTorus v * dD.d8 i j l * f * e) =
        dD.ofTorus v * dD.d8 i j l * (f * e) * (dD.ofTorus v * dD.d8 i j l * (f * e)) by group,
      (dD.t200gEAction hrel_e hrel_f hconj).nfe_e_mul_self] at hyy
    obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
    cases hlj : l && j
    · rw [hlj, d8_fff, mul_one, ofTorus_eq_one_iff] at hyy
      exact t200k_sqE_ne_zero dD hrel_e hrel_f hconj hm hp x0 x1 x2 hlj hyy
    · rw [hlj] at hyy
      exact dD.d8_not_mem (t200_faithful hm) (i := true) (j := false) (l := false) (by decide) _
        (by rw [hyy]; exact one_mem _)

theorem t200k_sqE_c (hrel_e : Rel34i dD e (2 ^ (m + 1))) (hrel_f : Rel34inv dD f 0 1 p)
    (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) (x0 x1 x2 : ℤ) (l : Bool) :
    ∃ s1 s2 : ℤ, (dD.t200gEAction hrel_e hrel_f hconj).sqE (Torus.ofInt _ ![x0, x1, x2])
      false false l = Torus.ofInt _ ![2 ^ (m - 1), s1, s2] := by
  simp only [EAction.sqE, EAction.twist, t200gEAction_ve, t200gEAction_wuv, t200gEAction_wt]
  cases l <;>
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, Bool.and_false, map_add, map_sub, map_zero, t200gEAction_φe_apply,
    t200_φu, ← Torus.ofInt_add, ← Torus.ofInt_sub, add_zero, zero_add]
  · refine ⟨-(2 ^ (m + 1) * x1), -(2 ^ (m + 1) * x2), ?_⟩
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  · refine ⟨x1 - (1 + 2 ^ (m + 1)) * x2, x2 - (1 + 2 ^ (m + 1)) * x1, ?_⟩
    congr 1
    funext i
    fin_cases i <;> simp <;> ring

theorem t200k_pow_ne (hm : 1 ≤ m) (hrel_e : Rel34i dD e (2 ^ (m + 1)))
    (hrel_f : Rel34inv dD f 0 1 p) (hconj : f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1))
    (v : Torus (StrothTypeIndex.t200 m).k) (l' : Bool) {l : ℕ} (hl : 2 ≤ l) :
    (dD.ofTorus v * dD.d8 false false l' * (f * e)) ^ 2 ^ l ≠ (dD.c : G) ^ 2 ^ (m - 1) := by
  intro h
  rw [pow_two_pow_eq_mul_self _ (by omega : 1 ≤ l),
    (dD.t200gEAction hrel_e hrel_f hconj).nfe_e_mul_self, Bool.and_false, d8_fff, mul_one,
    ← dD.ofTorus_nsmul, dD.t200_c_pow] at h
  have h' := dD.ofTorus_inj h
  obtain ⟨x0, x1, x2, rfl⟩ := t200_exists_vec v
  obtain ⟨s1, s2, hs⟩ := t200k_sqE_c dD hrel_e hrel_f hconj x0 x1 x2 l'
  rw [hs, ← natCast_zsmul, t200_zsmul_vec, om200_apply, t200_ofInt_eq_iff] at h'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h'
  obtain ⟨⟨k, hk⟩, -, -⟩ := h'
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨l'', rfl⟩ : ∃ l'', l = l'' + 2 := ⟨l - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show l'' + 2 - 1 = l'' + 1 by omega] at hk
  push_cast at hk
  have h2 : (2 : ℤ) ^ m' * 1 = 2 ^ m' * (2 * (k + 2 ^ l'')) := by
    linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero m' (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

end Stroth47Core

end CFSG.CGT.Stroth77
