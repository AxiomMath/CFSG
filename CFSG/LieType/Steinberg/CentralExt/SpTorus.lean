module

public import CFSG.LieType.Steinberg.Classical.Symplectic.Basic

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem

namespace CFSG.LieType.Steinberg.CentralExt.SpTorus

variable {n : ℕ} {F : Type} [Field F]

@[expose] def chi (v : Fin n → ℤ) (t : Fin n → Fˣ) : Fˣ := ∏ a, t a ^ v a

theorem chi_add (v w : Fin n → ℤ) (t : Fin n → Fˣ) : chi (v + w) t = chi v t * chi w t := by
  simp only [chi, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem chi_neg (v : Fin n → ℤ) (t : Fin n → Fˣ) : chi (-v) t = (chi v t)⁻¹ := by
  simp only [chi, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem chi_sub (v w : Fin n → ℤ) (t : Fin n → Fˣ) : chi (v - w) t = chi v t * (chi w t)⁻¹ := by
  rw [sub_eq_add_neg, chi_add, chi_neg]

theorem chi_single (i : Fin n) (t : Fin n → Fˣ) : chi (Pi.single i 1) t = t i := by
  classical
  simp only [chi]
  rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem chi_two_single (i : Fin n) (t : Fin n → Fˣ) :
    chi (2 • Pi.single i 1) t = t i * t i := by
  rw [two_nsmul, chi_add, chi_single]

theorem chi_update (v : Fin n → ℤ) (a : Fin n) (w : Fˣ) :
    chi v (Function.update 1 a w) = w ^ v a := by
  classical
  simp only [chi]
  rw [Finset.prod_eq_single a (fun b _ hb => by simp [Function.update_of_ne hb])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp

theorem chi_update₂ (v : Fin n → ℤ) {i j : Fin n} (hij : i ≠ j) (w w' : Fˣ) :
    chi v (Function.update (Function.update 1 i w) j w') = w ^ v i * w' ^ v j := by
  classical
  simp only [chi]
  rw [← Finset.prod_subset (Finset.subset_univ {i, j}) (fun b _ hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [Function.update_of_ne hb.1, Function.update_of_ne hb.2]), Finset.prod_pair hij]
  simp [Function.update_of_ne hij]

theorem character_eq_chi (r : RootSubgroupIndex n) (t : Fin n → Fˣ) :
    r.character t = chi (stdVec r) t := by
  cases r with
  | positiveLong i => rw [RootSubgroupIndex.character_positiveLong, stdVec, chi_two_single]
  | negativeLong i =>
    rw [RootSubgroupIndex.character_negativeLong, stdVec, chi_neg, chi_two_single]
  | difference i j hij =>
    rw [RootSubgroupIndex.character_difference, stdVec, chi_sub, chi_single, chi_single]
  | positiveSum i j hij =>
    rw [RootSubgroupIndex.character_positiveSum, stdVec, chi_add, chi_single, chi_single]
  | negativeSum i j hij =>
    rw [RootSubgroupIndex.character_negativeSum, stdVec, chi_neg, chi_add, chi_single,
      chi_single]

variable (F) in
@[expose] noncomputable def tor (t : Fin n → Fˣ) : StatedSp n F :=
  equivStatedSp n F (diagonal t)

theorem tor_mul (t t' : Fin n → Fˣ) : tor F (t * t') = tor F t * tor F t' := by
  rw [tor, tor, tor, map_mul, map_mul]

theorem tor_mul_comm (t t' : Fin n → Fˣ) : tor F t' * tor F t * (tor F t')⁻¹ = tor F t := by
  rw [← tor_mul, mul_comm t' t, tor_mul, mul_inv_cancel_right]

theorem tor_conj_x {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅)
    (t : Fin n → Fˣ) (c : F) :
    tor F t * Sp.x n F γ c * (tor F t)⁻¹ = Sp.x n F γ ((chi (toStd n γ) t : F) * c) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  rw [Sp.x_eq hr, Sp.x_eq hr, elt, elt, tor, ← map_inv, ← map_mul, ← map_mul,
    diagonal_mul_rootSubgroup_mul_inv, character_eq_chi, hr, toAdd_ofAdd]

theorem abs_stdVec_le (r : RootSubgroupIndex n) (a : Fin n) : |stdVec r a| ≤ 2 := by
  cases r <;> simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.single_apply] <;> (try split_ifs) <;> norm_num

theorem abs_stdVec_add_le (r : RootSubgroupIndex n) {i j : Fin n} (hij : i ≠ j) :
    |stdVec r i| + |stdVec r j| ≤ 2 := by
  cases r <;> simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    Pi.single_apply] <;> (try split_ifs) <;> simp_all

theorem exists_stdVec_ne_zero (r : RootSubgroupIndex n) : ∃ a, stdVec r a ≠ 0 := by
  cases r with
  | positiveLong i => exact ⟨i, by simp [stdVec]⟩
  | negativeLong i => exact ⟨i, by simp [stdVec]⟩
  | difference i j hij => exact ⟨i, by simp [stdVec, hij]⟩
  | positiveSum i j hij => exact ⟨i, by simp [stdVec, hij.ne]⟩
  | negativeSum i j hij => exact ⟨i, by simp [stdVec, hij.ne]⟩

theorem zpow_ne_one {w : Fˣ} (hw : w ^ 2 ≠ 1) {e : ℤ} (he : e ≠ 0) (he2 : |e| ≤ 2) :
    w ^ e ≠ 1 := by
  have hw1 : w ≠ 1 := fun h => hw (by rw [h, one_pow])
  rcases (show e = -2 ∨ e = -1 ∨ e = 1 ∨ e = 2 by
    rw [abs_le] at he2
    omega) with rfl | rfl | rfl | rfl
  · rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, inv_ne_one]
    exact hw
  · rw [zpow_neg_one, inv_ne_one]
    exact hw1
  · rw [zpow_one]
    exact hw1
  · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hw

theorem sep_short {u v : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s s' : ℤ}
    (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1)
    (hu : ∀ a, u a = if a = i then s else if a = j then s' else 0)
    (hv : ∀ a, a ≠ i → a ≠ j → v a = 0) (hv2 : |v i| + |v j| ≤ 2)
    (hli : LinIndepPair u v) {w : Fˣ} (hw : w ^ 2 ≠ 1) :
    ∃ t : Fin n → Fˣ, chi u t = 1 ∧ chi v t ≠ 1 := by
  refine ⟨Function.update (Function.update 1 i w) j (w ^ (-(s * s'))), ?_, ?_⟩
  · rw [chi_update₂ u hij]
    simp only [hu, ite_true, hij.symm, ite_false]
    rw [← zpow_mul, ← zpow_add]
    convert zpow_zero w using 2
    rcases hs' with rfl | rfl <;> ring
  · rw [chi_update₂ v hij, ← zpow_mul, ← zpow_add]
    refine zpow_ne_one hw (fun h0 => ?_) ?_
    ·
      have := (hli (s' * v j) (-1) (funext fun a => ?_)).2
      · exact absurd this (by norm_num)
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [hu a]
        by_cases hai : a = i
        · subst hai
          rw [ite_eq_left rfl]
          rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> linarith
        · by_cases haj : a = j
          · subst haj
            rw [ite_eq_right hai, ite_eq_left rfl]
            rcases hs' with rfl | rfl <;> ring
          · rw [ite_eq_right hai, ite_eq_right haj, hv a hai haj]
            ring
    · have hss : |-(s * s')| = 1 := by
        rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> norm_num
      calc |v i + -(s * s') * v j| ≤ |v i| + |-(s * s') * v j| := abs_add_le _ _
        _ = |v i| + |v j| := by rw [abs_mul, hss, one_mul]
        _ ≤ 2 := hv2

theorem toStd_zsmul (a : ℤ) (v : Fin n → ℤ) : toStd n (a • v) = a • toStd n v := by
  funext b
  simp only [toStd, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem linIndepPair_toStd {γ δ : Fin n → ℤ} (h : LinIndepPair γ δ) :
    LinIndepPair (toStd n γ) (toStd n δ) := fun a b hab =>
  h a b (toStd_inj (by
    rw [toStd_add', toStd_zsmul, toStd_zsmul, hab]
    funext c
    simp [toStd]))

theorem exists_tor_sep {γ δ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanC n) ∅) (hli : LinIndepPair γ δ) {w : Fˣ}
    (hw : w ^ 2 ≠ 1) : ∃ t : Fin n → Fˣ, chi (toStd n γ) t = 1 ∧ chi (toStd n δ) t ≠ 1 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨r', hr'⟩ := exists_stdVec_of_mem_roots hδ
  have hli' := linIndepPair_toStd hli
  rw [← hr, ← hr'] at hli' ⊢
  by_cases h : ∃ a, stdVec r a = 0 ∧ stdVec r' a ≠ 0
  · obtain ⟨a, hua, hva⟩ := h
    refine ⟨Function.update 1 a w, ?_, ?_⟩
    · rw [chi_update, hua, zpow_zero]
    · rw [chi_update]
      exact zpow_ne_one hw hva (abs_stdVec_le r' a)
  push Not at h
  have hlong : ∀ i : Fin n, ∀ c : ℤ, c ≠ 0 → (∀ a, stdVec r a = if a = i then c else 0) →
      False := fun i c hc hu => by
    have := (hli' (stdVec r' i) (-c) (funext fun a => ?_)).2
    · exact hc (neg_eq_zero.1 this)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases hai : a = i
      · subst hai
        rw [hu a, ite_eq_left rfl]
        ring
      · rw [hu a, ite_eq_right hai, h a (by rw [hu a, ite_eq_right hai])]
        ring
  have hshort : ∀ i j : Fin n, i ≠ j → ∀ s s' : ℤ, (s = 1 ∨ s = -1) → (s' = 1 ∨ s' = -1) →
      (∀ a, stdVec r a = if a = i then s else if a = j then s' else 0) →
      ∃ t : Fin n → Fˣ, chi (stdVec r) t = 1 ∧ chi (stdVec r') t ≠ 1 :=
    fun i j hij s s' hs hs' hu => sep_short hij hs hs' hu
      (fun a hai haj => h a (by rw [hu a, ite_eq_right hai, ite_eq_right haj]))
      (abs_stdVec_add_le r' hij) hli' hw
  cases r with
  | positiveLong i =>
    exact (hlong i 2 (by norm_num) fun a => by
      simp only [stdVec, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp).elim
  | negativeLong i =>
    exact (hlong i (-2) (by norm_num) fun a => by
      simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp).elim
  | difference i j hij =>
    exact hshort i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl) fun a => by
      simp only [stdVec, Pi.sub_apply, Pi.single_apply]
      by_cases hai : a = i
      · simp [hai, hij]
      · by_cases haj : a = j
        · simp [haj, hij.symm]
        · simp [hai, haj]
  | positiveSum i j hij =>
    exact hshort i j hij.ne 1 1 (Or.inl rfl) (Or.inl rfl) fun a => by
      simp only [stdVec, Pi.add_apply, Pi.single_apply]
      by_cases hai : a = i
      · simp [hai, hij.ne]
      · by_cases haj : a = j
        · simp [haj, hij.ne']
        · simp [hai, haj]
  | negativeSum i j hij =>
    exact hshort i j hij.ne (-1) (-1) (Or.inr rfl) (Or.inr rfl) fun a => by
      simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply]
      by_cases hai : a = i
      · simp [hai, hij.ne]
      · by_cases haj : a = j
        · simp [haj, hij.ne']
        · simp [hai, haj]

theorem exists_tor_ne_one {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) {w : Fˣ}
    (hw : w ^ 2 ≠ 1) : ∃ t : Fin n → Fˣ, chi (toStd n γ) t ≠ 1 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨a, ha⟩ := exists_stdVec_ne_zero r
  refine ⟨Function.update 1 a w, ?_⟩
  rw [← hr, chi_update]
  exact zpow_ne_one hw ha (abs_stdVec_le r a)

theorem exists_tor_sq {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (U : Fˣ) :
    ∃ t : Fin n → Fˣ, chi (toStd n γ) t = U ^ 2 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨a, ha⟩ := exists_stdVec_ne_zero r
  have hdvd : stdVec r a ∣ 2 := by
    have := abs_stdVec_le r a
    rw [abs_le] at this
    rcases (show stdVec r a = -2 ∨ stdVec r a = -1 ∨ stdVec r a = 1 ∨ stdVec r a = 2 by omega)
      with h | h | h | h <;> rw [h] <;> norm_num
  refine ⟨Function.update 1 a (U ^ (2 / stdVec r a)), ?_⟩
  rw [← hr, chi_update, ← zpow_mul, Int.ediv_mul_cancel hdvd]
  norm_num

end CFSG.LieType.Steinberg.CentralExt.SpTorus
