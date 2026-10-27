module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46L45

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

namespace KD46

theorem card_filter_k : ((Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).filter fun v =>
    (v.2.1 = 1 ∧ v.2.2 = 0) ∨ (v.2.1 = 0 ∧ v.2.2 = 1)).card = 4 := by decide

theorem card_filter_tk : ((Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).filter fun v =>
    (v.2.1 = 1 ∧ v.2.2 = 0) ∨ (v.2.1 = 1 ∧ v.2.2 = 1)).card = 4 := by decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

omit [Finite X] in
theorem tk_mem_T : t * C.k ∈ A.T := mul_mem A.t_mem_T C.k_mem

omit [Finite X] in
theorem tk_sq : (t * C.k) ^ 2 = 1 := by
  rw [Commute.mul_pow (SD.commute_t_of_mem_C (A.T_le_centralizer C.k_mem)).symm,
    t_sq' (A := A), C.k_sq, one_mul]

@[expose] def caseTk (C : A.CaseKD) : A.CaseKD where
  k := t * C.k
  k_mem := tk_mem_T
  k_sq := tk_sq
  ψ_k := by
    rw [← ψX_of_mem tk_mem_T, ψX_mul A.t_mem_T C.k_mem, ψX_t, one_mul, ψX_of_mem C.k_mem, C.ψ_k]
  d := C.d
  d_mem := C.d_mem
  ψ_d := C.ψ_d
  card_K := C.card_K

omit [Finite X] in
theorem caseTk_k : (caseTk C).k = t * C.k := rfl

omit [Finite X] in
theorem conj_tk_of {g : X} (hg : g ∈ centralizer ({t} : Set X)) {c : X}
    (h : g * c * g⁻¹ = c) : g * (t * c) * g⁻¹ = t * c := by
  calc g * (t * c) * g⁻¹ = (g * t * g⁻¹) * (g * c * g⁻¹) := by group
    _ = t * c := by rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right, h]

omit [Finite X] in
theorem closure_tk' (a b : X) :
    closure ({a, b, t, t * C.k} : Set X) = closure ({a, b, t, C.k} : Set X) :=
  A7Facts.closure_tk a b

@[expose] def withTk : KDBase A (caseTk C) where
  x := S.x
  y := S.y
  x_mem := S.x_mem
  y_mem := S.y_mem
  orderOf_x := S.orderOf_x
  y_sq := S.y_sq
  y_inv := S.y_inv
  d_y := by
    obtain ⟨g, hgC, hgN, h1, h2, h3⟩ := S.d_y
    refine ⟨g, hgC, ?_, h1, h2, conj_tk_of hgC h3⟩
    rw [caseTk_k, closure_tk']
    exact hgN
  d_xy := by
    obtain ⟨g, hgC, hgN, h1, h2, h3⟩ := S.d_xy
    refine ⟨g, hgC, ?_, h1, h2, ?_⟩
    · rw [caseTk_k, closure_tk']
      exact hgN
    · rw [caseTk_k]
      have e : S.x ^ 2 * (t * C.k) = t * (S.x ^ 2 * C.k) := by
        rw [← mul_assoc, show S.x ^ 2 * t = t * S.x ^ 2 from comm_t (z_mem_T S), mul_assoc]
      rw [e]
      exact conj_tk_of hgC h3
  k_fixed := by
    intro n hn
    rw [caseTk_k, closure_tk'] at hn
    exact conj_tk_of hn.2 (S.k_fixed n hn)
  zk_fixed := by
    intro n hn
    rw [caseTk_k, closure_tk'] at hn
    rw [caseTk_k]
    have e : S.x ^ 2 * (t * C.k) = t * (S.x ^ 2 * C.k) := by
      rw [← mul_assoc, show S.x ^ 2 * t = t * S.x ^ 2 from comm_t (z_mem_T S), mul_assoc]
    rw [e]
    exact conj_tk_of hn.2 (S.zk_fixed n hn)
  card_conj_z := S.card_conj_z
  card_conj_k := ncard_cls_tk S
  not_conj_k_tk := by
    intro g hg h
    have e : t * (t * C.k) = C.k := by rw [← mul_assoc, ← pow_two, t_sq' (A := A), one_mul]
    apply S.not_conj_k_tk g hg
    have h' : g * (t * C.k) * g⁻¹ = C.k := by
      have h2 : g * (t * C.k) * g⁻¹ = t * (t * C.k) := h
      rw [h2, e]
    calc g * C.k * g⁻¹ = g * (t * (t * C.k)) * g⁻¹ := by rw [e]
      _ = (g * t * g⁻¹) * (g * (t * C.k) * g⁻¹) := by group
      _ = t * C.k := by rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right, h']
  inv_classes := by
    intro i hi hi2 hi1
    obtain ⟨g, hg, h⟩ := S.inv_classes i hi hi2 hi1
    refine ⟨g, hg, ?_⟩
    have e : t * (t * C.k) = C.k := by rw [← mul_assoc, ← pow_two, t_sq' (A := A), one_mul]
    rw [caseTk_k, e]
    tauto

theorem withTk_z : (withTk S).z = S.z := rfl

theorem withTk_k : (withTk S).k = t * S.k := rfl

theorem withTk_B : (withTk S).B = S.B := by
  change closure {S.z, t, t * C.k} = closure {S.z, t, C.k}
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have h := mul_mem (inv_mem (subset_closure (show t ∈ ({S.z, t, t * C.k} : Set X) by simp)))
        (subset_closure (show t * C.k ∈ ({S.z, t, t * C.k} : Set X) by simp))
      rwa [inv_mul_cancel_left] at h

theorem withTk_TE : (withTk S).TE = S.TE := by
  rw [KDBase.TE, KDBase.TE, withTk_B]

theorem fusion_cases [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hnot : ¬ SectRank4 X) :
    ConjTo t (t * S.z) ∧ ((ConjTo t S.k ∧ ¬ ConjTo t (t * S.k)) ∨
      (¬ ConjTo t S.k ∧ ConjTo t (t * S.k))) := by
  classical
  have hmod := (card_Om_modEq_index hnab (t_sq' (A := A))).symm.trans (card_Om_modEq S)
  have h4 := four_dvd_index S hnab hnot
  have h0 : (centralizer ({t} : Set X)).index ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4
  have h := h0.symm.trans hmod
  unfold Nat.ModEq at h
  by_cases h1 : ConjTo t (t * S.z) <;> by_cases h2 : ConjTo t S.k <;>
    by_cases h3 : ConjTo t (t * S.k) <;> simp only [h1, h2, h3, ↓reduceIte] at h <;>
    first
      | (exfalso; omega)
      | exact ⟨h1, Or.inl ⟨h2, h3⟩⟩
      | exact ⟨h1, Or.inr ⟨h2, h3⟩⟩

@[expose] noncomputable def wB (v : Fin 2 × Fin 2 × Fin 2) : X :=
  S.z ^ (v.1 : ℕ) * t ^ (v.2.1 : ℕ) * S.k ^ (v.2.2 : ℕ)

theorem wB_injective : Function.Injective (wB S) := by
  rintro ⟨i, j, l⟩ ⟨i', j', l'⟩ h
  obtain ⟨h1, h2, h3⟩ := B_word_inj S i.2 j.2 l.2 i'.2 j'.2 l'.2 h
  exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem exists_wB {b : X} (hb : b ∈ S.B) : ∃ v, b = wB S v := by
  obtain ⟨i, j, l, hi, hj, hl, rfl⟩ := eq_of_mem_B S hb
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩), rfl⟩

theorem wB_mem (v : Fin 2 × Fin 2 × Fin 2) : wB S v ∈ S.B :=
  mul_mem (mul_mem (pow_mem (mem_B_z S) _) (pow_mem (mem_B_t S) _)) (pow_mem (mem_B_k S) _)

theorem conjTo_wB_iff (htz : ConjTo t (t * S.z)) (v : Fin 2 × Fin 2 × Fin 2) :
    ConjTo t (wB S v) ↔ (v.2.1 = 1 ∧ v.2.2 = 0) ∨ (v.2.1 = 0 ∧ v.2.2 = 1 ∧ ConjTo t S.k) ∨
      (v.2.1 = 1 ∧ v.2.2 = 1 ∧ ConjTo t (t * S.k)) := by
  obtain ⟨i, j, l⟩ := v
  have hz : ∀ (j l : Fin 2), wB S (1, j, l) = S.z * wB S (0, j, l) := fun j l => by
    simp [wB, mul_assoc]
  have h0 : ∀ (j l : Fin 2), ConjTo t (wB S (i, j, l)) ↔ ConjTo t (wB S (0, j, l)) := by
    intro j l
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · rfl
    · rw [hz]
      exact conjTo_mul_z_iff S htz (wB_mem S _)
  rw [h0]
  rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl <;> simp only [wB] <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · simp only [Fin.isValue, zero_ne_one, false_and, and_false, or_self, iff_false]
    exact not_conjTo_one (A := A)
  · simp
  · simp only [Fin.isValue, and_self, true_or, iff_true]
    exact ⟨1, by group⟩
  · simp

end KD46

open KD46 in
theorem fritzKDSection4 : FritzKDSection4 := by
  intro _ X _ _ _ hnab hnot t L A C S
  classical
  obtain ⟨htz, hcase⟩ := fusion_cases S hnab hnot
  obtain ⟨T₁, hT₁p, hTT₁, hT₁N, hmax, hcard, -, -⟩ := exists_T₁ S hnot
  have horb : orbT S = wB S '' {v | ConjTo t (wB S v)} := by
    ext b
    rw [mem_orbT_iff]
    constructor
    · rintro ⟨hb, hc⟩
      obtain ⟨v, rfl⟩ := exists_wB S hb
      exact ⟨v, hc, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨wB_mem S v, hv⟩
  have hO4 : (orbT S).ncard = 4 := by
    rw [horb, Set.ncard_image_of_injective _ (wB_injective S)]
    rcases hcase with ⟨hk, htk⟩ | ⟨hk, htk⟩
    · rw [← card_filter_k, ← Set.ncard_coe_finset]
      congr 1
      ext v
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and,
        conjTo_wB_iff S htz v, hk, htk]
      tauto
    · rw [← card_filter_tk, ← Set.ncard_coe_finset]
      congr 1
      ext v
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and,
        conjTo_wB_iff S htz v, hk, htk]
      tauto
  have hcard4 : Nat.card T₁ = 4 * Nat.card A.T := by
    rw [hcard, hO4, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
    simp [mul_comm]
  have hfus : ∀ b ∈ S.B, ConjTo t b ↔ (ConjTo t S.k →
      (b = t ∨ b = t * S.z ∨ b = S.k ∨ b = S.z * S.k)) ∧ (ConjTo t (t * S.k) →
      (b = t ∨ b = t * S.z ∨ b = t * S.k ∨ b = t * S.z * S.k)) := by
    intro b hb
    obtain ⟨v, rfl⟩ := exists_wB S hb
    have hw : ∀ w : Fin 2 × Fin 2 × Fin 2, wB S v = wB S w ↔ v = w :=
      fun w => (wB_injective S).eq_iff
    have e1 : t = wB S (0, 1, 0) := by simp [wB]
    have e2 : t * S.z = wB S (1, 1, 0) := by simp [wB, z_comm_t S]
    have e3 : S.k = wB S (0, 0, 1) := by simp [wB]
    have e4 : S.z * S.k = wB S (1, 0, 1) := by simp [wB]
    have e5 : t * S.k = wB S (0, 1, 1) := by simp [wB]
    have e6 : t * S.z * S.k = wB S (1, 1, 1) := by simp [wB, z_comm_t S]
    have f : ∀ {u : X} {w : Fin 2 × Fin 2 × Fin 2}, u = wB S w → (wB S v = u ↔ v = w) :=
      fun {u w} he => ⟨fun h => wB_injective S (h.trans he), fun h => h ▸ he.symm⟩
    rw [conjTo_wB_iff S htz v, f e1, f e2, f e3, f e4, f e5, f e6]
    clear f hw hb e1 e2 e3 e4 e5 e6
    obtain ⟨i, j, l⟩ := v
    rcases hcase with ⟨hk, htk⟩ | ⟨hk, htk⟩ <;> simp only [hk, htk, true_implies,
      false_implies, and_true, true_and, and_false, or_false, Prod.mk.injEq] <;>
      revert i j l <;> decide
  rcases hcase with ⟨hk, htk⟩ | ⟨hk, htk⟩
  ·
    refine ⟨caseTk C, withTk S, T₁, ⟨hT₁p, hTT₁, by rw [withTk_TE]; exact hT₁N,
      fun Q hQ hle hQN => hmax Q hQ hle (by rw [withTk_TE] at hQN; exact hQN), hcard4, ?_⟩⟩
    intro b hb
    rw [withTk_B] at hb
    refine (hfus b hb).trans ?_
    rw [withTk_z, withTk_k]
    have e1 : t * (t * S.k) = S.k := by rw [← mul_assoc, ← pow_two, t_sq' (A := A), one_mul]
    have e2 : t * S.z * (t * S.k) = S.z * S.k := by
      calc t * S.z * (t * S.k) = t * (S.z * t) * S.k := by group
        _ = t * (t * S.z) * S.k := by rw [z_comm_t S]
        _ = t * t * S.z * S.k := by group
        _ = S.z * S.k := by rw [← pow_two, t_sq' (A := A), one_mul]
    rw [e1, e2]
    tauto
  · refine ⟨C, S, T₁, ⟨hT₁p, hTT₁, hT₁N, hmax, hcard4, ?_⟩⟩
    intro b hb
    rw [hfus b hb]
    tauto

end CFSG.OddStandard.SmallF3.L33.KD
