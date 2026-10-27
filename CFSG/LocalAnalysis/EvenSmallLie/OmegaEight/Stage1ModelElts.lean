module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelPerm

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage2 (urRows)

variable {ε : Eps}

@[expose] noncomputable def psiM (ε : Eps) (v : V6) : Equiv.Perm (Fin (deg ε)) :=
  permOfArr (deg ε) (psiArr ε (vecBits v))

@[expose] noncomputable def pM (ε : Eps) (i : Fin 6) : Equiv.Perm (Fin (deg ε)) :=
  permOfArr (deg ε) (pArr ε i)

@[expose] noncomputable def uM (ε : Eps) (k : Fin 6) : Equiv.Perm (Fin (deg ε)) :=
  permOfArr (deg ε) (uArr ε k)

theorem rep_psiM (v : V6) : Rep (deg ε) (psiArr ε (vecBits v)) (psiM ε v) ∧
    Rep (deg ε) (invCand (deg ε) (psiArr ε (vecBits v))) (psiM ε v)⁻¹ :=
  rep_permOfArr ((basic_parts ε).1 _ (vecBits_lt v)).1

theorem rep_pM (i : Fin 6) : Rep (deg ε) (pArr ε i) (pM ε i) ∧
    Rep (deg ε) (invCand (deg ε) (pArr ε i)) (pM ε i)⁻¹ :=
  rep_permOfArr ((basic_parts ε).2.2.1 i i.2).1

theorem rep_uM (k : Fin 6) : Rep (deg ε) (uArr ε k) (uM ε k) ∧
    Rep (deg ε) (invCand (deg ε) (uArr ε k)) (uM ε k)⁻¹ :=
  rep_permOfArr ((basic_parts ε).2.2.2.1 k k.2).1

theorem psiM_add (v w : V6) : psiM ε (v + w) = psiM ε v * psiM ε w := by
  have h := ((basic_parts ε).2.1 (vecBits v) (vecBits_lt v) (vecBits w) (vecBits_lt w)).1
  rw [← vecBits_add] at h
  exact eq_of_eqA (rep_psiM (v + w)).1 (rep_compA (rep_psiM v).1 (rep_psiM w).1) h

theorem psiM_zero : psiM ε 0 = 1 := by
  have h := psiM_add (ε := ε) 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem psiM_injective : Function.Injective (psiM ε) := by
  intro v w e
  rcases ((basic_parts ε).2.1 (vecBits v) (vecBits_lt v) (vecBits w) (vecBits_lt w)).2 with h | h
  · rw [← toVec_vecBits v, ← toVec_vecBits w, h]
  · rw [(eqA_iff (rep_psiM v).1 (rep_psiM w).1).2 e] at h
    exact absurd h (by decide)

theorem vecBits_single (j : Fin 6) : vecBits (Pi.single j 1) = 2 ^ (j : ℕ) := by
  rw [← toVec_two_pow' j, vecBits_toVec (by have := j.2; interval_cases (j : ℕ) <;> norm_num)]

theorem psiM_mem_L (v : V6) : psiM ε v ∈ Lm ε :=
  (memL_iff (rep_psiM v).1).1 ((basic_parts ε).1 _ (vecBits_lt v)).2.1

theorem psiM_mem_P (v : V6) : psiM ε v ∈ PQm ε :=
  (memP_iff (rep_psiM v).1).1 ((basic_parts ε).1 _ (vecBits_lt v)).2.2.1

theorem psiM_mem_U (v : V6) : psiM ε v ∈ UQm ε :=
  (memU_iff (rep_psiM v).1).1 ((basic_parts ε).1 _ (vecBits_lt v)).2.2.2

theorem pM_mem_L (i : Fin 6) : pM ε i ∈ Lm ε :=
  (memL_iff (rep_pM i).1).1 ((basic_parts ε).2.2.1 i i.2).2.1

theorem uM_mem_L (k : Fin 6) : uM ε k ∈ Lm ε :=
  (memL_iff (rep_uM k).1).1 ((basic_parts ε).2.2.2.1 k k.2).2.1

theorem pM_act (i : Fin 6) (v : V6) :
    pM ε i * psiM ε v * (pM ε i)⁻¹ = psiM ε (genMat ε i *ᵥ v) := by
  have h := ((basic_parts ε).2.2.1 i i.2).2.2 (vecBits v) (vecBits_lt v)
  rw [← vecBits_mulVec] at h
  exact eq_of_eqA (rep_compA (rep_compA (rep_pM i).1 (rep_psiM v).1) (rep_pM i).2)
    (rep_psiM _).1 h

theorem uM_act (k : Fin 6) (v : V6) :
    uM ε k * psiM ε v * (uM ε k)⁻¹ = psiM ε (toMat 6 6 (urRows ε k) *ᵥ v) := by
  have h := ((basic_parts ε).2.2.2.1 k k.2).2.2 (vecBits v) (vecBits_lt v)
  rw [← vecBits_mulVec] at h
  exact eq_of_eqA (rep_compA (rep_compA (rep_uM k).1 (rep_psiM v).1) (rep_uM k).2)
    (rep_psiM _).1 h

theorem eq_of_urRows_fixed {v : V6} (hv : ∀ k : Fin 6, toMat 6 6 (urRows ε k) *ᵥ v = v) :
    v = 0 ∨ v = Pi.single 0 1 := by
  have h := (basic_parts ε).2.2.2.2 (vecBits v) (vecBits_lt v) fun k hk => by
    rw [← vecBits_mulVec, hv ⟨k, hk⟩]
  rcases h with h | h
  · left
    rw [← toVec_vecBits v, h]
    ext i
    simp [toVec, bz]
  · right
    rw [← toVec_vecBits v, h, show (1 : ℕ) = 2 ^ ((0 : Fin 6) : ℕ) from rfl, toVec_two_pow']

@[expose] noncomputable def psiHomM (ε : Eps) : Multiplicative V6 →* Equiv.Perm (Fin (deg ε)) where
  toFun v := psiM ε (Multiplicative.toAdd v)
  map_one' := psiM_zero
  map_mul' _ _ := psiM_add _ _

@[expose] noncomputable def QMm (ε : Eps) : Subgroup (Equiv.Perm (Fin (deg ε))) := (psiHomM ε).range

theorem mem_QMm {x : Equiv.Perm (Fin (deg ε))} : x ∈ QMm ε ↔ ∃ v, psiM ε v = x :=
  ⟨fun ⟨v, hv⟩ => ⟨Multiplicative.toAdd v, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem psiM_mem_Q (v : V6) : psiM ε v ∈ QMm ε := mem_QMm.2 ⟨v, rfl⟩

theorem QMm_le_L : QMm ε ≤ Lm ε := fun _ hx => by
  obtain ⟨v, rfl⟩ := mem_QMm.1 hx
  exact psiM_mem_L v

theorem QMm_le_U : QMm ε ≤ UQm ε := fun _ hx => by
  obtain ⟨v, rfl⟩ := mem_QMm.1 hx
  exact psiM_mem_U v

theorem orig_get {A B : Fin 6 → Array ℕ} {i : ℕ} (hi : i < 12) :
    ((Array.ofFn A) ++ Array.ofFn B)[i]! = if h : i < 6 then A ⟨i, h⟩ else B ⟨i - 6, by omega⟩ := by
  rw [getElem!_pos _ i (by simp; omega)]
  split_ifs with h
  · rw [Array.getElem_append_left (by simpa using h), Array.getElem_ofFn]
  · rw [Array.getElem_append_right (by simp; omega), Array.getElem_ofFn]
    simp

theorem pS_get {i : ℕ} (hi : i < 12) :
    (pS ε)[i]! = if _h : i < 6 then psiArr ε (2 ^ i) else pArr ε (i - 6) := by
  have h1 : (pS ε)[i]! = (pOrig ε)[i]! := by
    cases ε
    · exact OmegaEight.pushWords_getElem! _ _ (by simp [pOrig]; omega)
    · exact OmegaEight.pushWords_getElem! _ _ (by simp [pOrig]; omega)
  rw [h1, pOrig, orig_get hi]

theorem uS_get {i : ℕ} (hi : i < 12) :
    (uS ε)[i]! = if _h : i < 6 then psiArr ε (2 ^ i) else uArr ε (i - 6) := by
  cases ε <;> rw [uS] <;> simp only [uSPlus, uSMinus, uOrig] <;> rw [orig_get hi]

theorem PQm_eq : PQm ε =
    closure (Set.range (fun j : Fin 6 => psiM ε (Pi.single j 1)) ∪ Set.range (pM ε)) := by
  rw [PQm, pQ, ofArrays_originalSubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [pS_get hi]
    split_ifs with h
    · exact Or.inl ⟨⟨i, h⟩, by simp [psiM, vecBits_single]⟩
    · exact Or.inr ⟨⟨i - 6, by omega⟩, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨j, by omega, by simp [pS_get (show (j : ℕ) < 12 by omega), j.2, psiM, vecBits_single]⟩
    · refine ⟨j + 6, by omega, ?_⟩
      simp [pS_get (show (j : ℕ) + 6 < 12 by omega), pM]

theorem UQm_eq : UQm ε =
    closure (Set.range (fun j : Fin 6 => psiM ε (Pi.single j 1)) ∪ Set.range (uM ε)) := by
  rw [UQm, uQ, ofArrays_originalSubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [uS_get hi]
    split_ifs with h
    · exact Or.inl ⟨⟨i, h⟩, by simp [psiM, vecBits_single]⟩
    · exact Or.inr ⟨⟨i - 6, by omega⟩, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨j, by omega, by simp [uS_get (show (j : ℕ) < 12 by omega), j.2, psiM, vecBits_single]⟩
    · refine ⟨j + 6, by omega, ?_⟩
      simp [uS_get (show (j : ℕ) + 6 < 12 by omega), uM]

theorem uM_mem_U (k : Fin 6) : uM ε k ∈ UQm ε := by
  rw [UQm_eq]
  exact subset_closure (Or.inr ⟨k, rfl⟩)

theorem pM_mem_P (i : Fin 6) : pM ε i ∈ PQm ε := by
  rw [PQm_eq]
  exact subset_closure (Or.inr ⟨i, rfl⟩)

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
