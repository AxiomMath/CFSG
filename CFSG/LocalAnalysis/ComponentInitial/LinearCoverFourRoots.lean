module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag
open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def rootElt (i j : Fin n) (a : K) : SpecialLinearGroup (Fin n) K :=
  if h : i = j then 1 else SpecialLinearGroup.transvection h a

theorem rootElt_self (i : Fin n) (a : K) : rootElt i i a = 1 :=
  dite_eq_left rfl

theorem rootElt_of_ne {i j : Fin n} (h : i ≠ j) (a : K) :
    rootElt i j a = SpecialLinearGroup.transvection h a :=
  dite_eq_right h

theorem coe_rootElt_of_ne {i j : Fin n} (h : i ≠ j) (a : K) :
    (rootElt i j a : Matrix (Fin n) (Fin n) K) = transvection i j a := by
  rw [rootElt_of_ne h]
  rfl

theorem rootElt_add (i j : Fin n) (a b : K) :
    rootElt i j (a + b) = rootElt i j a * rootElt i j b := by
  by_cases h : i = j
  · rw [h, rootElt_self, rootElt_self, rootElt_self, mul_one]
  · rw [rootElt_of_ne h, rootElt_of_ne h, rootElt_of_ne h, SpecialLinearGroup.transvection_add]

theorem rootElt_zero (i j : Fin n) : rootElt i j (0 : K) = 1 := by
  by_cases h : i = j
  · rw [h, rootElt_self]
  · rw [rootElt_of_ne h, SpecialLinearGroup.transvection_coeff_zero]

theorem rootElt_mul_comm {i j k l : Fin n} (hjk : j ≠ k) (hli : l ≠ i) (a b : K) :
    rootElt i j a * rootElt k l b = rootElt k l b * rootElt i j a := by
  by_cases hij : i = j
  · rw [hij, rootElt_self, one_mul, mul_one]
  by_cases hkl : k = l
  · rw [hkl, rootElt_self, one_mul, mul_one]
  rw [rootElt_of_ne hij, rootElt_of_ne hkl]
  exact (SpecialLinearGroup.commute_transvection hij hkl hjk hli a b).eq

theorem commutatorElement_rootElt {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a b : K) : ⁅rootElt i j a, rootElt j l b⁆ = rootElt i l (a * b) := by
  rw [rootElt_of_ne hij, rootElt_of_ne hjl, rootElt_of_ne hil,
    SpecialLinearGroup.commutatorElement_transvection hij hjl hil]

theorem rootElt_mem_unitriangular {i j : Fin n} (h : i < j) (a : K) :
    rootElt i j a ∈ unitriangular n K := by
  rw [mem_unitriangular, coe_rootElt_of_ne h.ne]
  refine ⟨fun r c hrc => ?_, fun r => ?_⟩
  · rw [transvection, Matrix.add_apply, one_apply_ne hrc.ne', single_apply, ite_eq_right,
      add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd (h.trans hrc) (lt_irrefl _)
  · rw [transvection, Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ h

theorem unitriangular_le_closure_rootElt :
    unitriangular n K ≤ closure {g | ∃ i j : Fin n, ∃ a : K, i < j ∧ rootElt i j a = g} := by
  classical
  set X := {g | ∃ i j : Fin n, ∃ a : K, i < j ∧ rootElt i j a = g}
  let supp : SpecialLinearGroup (Fin n) K → Finset (Fin n × Fin n) := fun u =>
    Finset.univ.filter fun p => p.1 < p.2 ∧ (u : Matrix (Fin n) (Fin n) K) p.1 p.2 ≠ 0
  have hsupp : ∀ u p, p ∈ supp u ↔ p.1 < p.2 ∧ (u : Matrix (Fin n) (Fin n) K) p.1 p.2 ≠ 0 :=
    fun u p => by simp [supp]
  suffices h : ∀ (m : ℕ) (u : SpecialLinearGroup (Fin n) K), u ∈ unitriangular n K →
      (supp u).card ≤ m → u ∈ closure X from fun u hu => h _ u hu le_rfl
  intro m
  induction m with
  | zero =>
    intro u hu hm
    have hempty : supp u = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hm)
    have hu1 : u = 1 := by
      ext a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [SpecialLinearGroup.coe_one, one_apply_ne hab.ne]
        by_contra hne
        have hmem : (a, b) ∈ supp u := (hsupp u (a, b)).mpr ⟨hab, hne⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty _ hmem
      · rw [hu.2 a, SpecialLinearGroup.coe_one, one_apply_eq]
      · rw [hu.1 a b hab, SpecialLinearGroup.coe_one, one_apply_ne hab.ne']
    rw [hu1]
    exact one_mem _
  | succ m ih =>
    intro u hu hm
    rcases (supp u).eq_empty_or_nonempty with hempty | hne
    · exact ih u hu (by rw [hempty]; exact Nat.zero_le _)
    obtain ⟨⟨i, j⟩, hij, hmin⟩ := Finset.exists_min_image (supp u) (fun p => p.2) hne
    replace hmin : ∀ p ∈ supp u, j ≤ p.2 := hmin
    obtain ⟨hij', -⟩ : i < j ∧ (u : Matrix (Fin n) (Fin n) K) i j ≠ 0 := (hsupp u (i, j)).mp hij
    set c := (u : Matrix (Fin n) (Fin n) K) i j with hc
    have hcol : ∀ a, (u : Matrix (Fin n) (Fin n) K) a i = if a = i then 1 else 0 := by
      intro a
      rcases lt_trichotomy a i with hai | rfl | hai
      · rw [ite_eq_right hai.ne]
        by_contra hne
        have hji : j ≤ i := hmin (a, i) ((hsupp u (a, i)).mpr ⟨hai, hne⟩)
        exact absurd (hji.trans_lt hij') (lt_irrefl _)
      · rw [ite_eq_left rfl, hu.2]
      · rw [ite_eq_right hai.ne', hu.1 a i hai]
    set u' := u * rootElt i j (-c) with hu'def
    have hu' : u' ∈ unitriangular n K := mul_mem hu (rootElt_mem_unitriangular hij' _)
    have hentry : ∀ a b, (u' : Matrix (Fin n) (Fin n) K) a b = if b = j then
        (u : Matrix (Fin n) (Fin n) K) a j + -c * (if a = i then 1 else 0)
        else (u : Matrix (Fin n) (Fin n) K) a b := by
      intro a b
      rw [hu'def, SpecialLinearGroup.coe_mul, coe_rootElt_of_ne hij'.ne]
      by_cases hb : b = j
      · rw [ite_eq_left hb, hb, mul_transvection_apply_same, hcol]
      · rw [ite_eq_right hb, mul_transvection_apply_of_ne _ _ _ _ hb]
    have hsub : supp u' ⊆ (supp u).erase (i, j) := by
      rintro ⟨a, b⟩ hab
      obtain ⟨hab', hne⟩ := (hsupp u' (a, b)).mp hab
      rw [hentry] at hne
      rw [Finset.mem_erase, hsupp]
      by_cases hb : b = j
      · rw [ite_eq_left hb] at hne
        rw [hb] at hab' ⊢
        by_cases ha : a = i
        · rw [ite_eq_left ha, ha, ← hc, mul_one, add_neg_cancel] at hne
          exact absurd rfl hne
        · rw [ite_eq_right ha, mul_zero, add_zero] at hne
          exact ⟨fun h => ha (Prod.mk.inj h).1, hab', hne⟩
      · rw [ite_eq_right hb] at hne
        exact ⟨fun h => hb (Prod.mk.inj h).2, hab', hne⟩
    have hcard : (supp u').card ≤ m := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hij] at h1
      omega
    have hu_eq : u = u' * rootElt i j c := by
      rw [hu'def, mul_assoc, ← rootElt_add, neg_add_cancel, rootElt_zero, mul_one]
    rw [hu_eq]
    exact mul_mem (ih u' hu' hcard) (subset_closure ⟨i, j, c, hij', rfl⟩)

@[expose] def diagElt (s : Fin n → K) (hs : ∏ i, s i = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨diagonal s, by rw [det_diagonal, hs]⟩

theorem coe_diagElt (s : Fin n → K) (hs : ∏ i, s i = 1) :
    (diagElt s hs : Matrix (Fin n) (Fin n) K) = diagonal s :=
  rfl

theorem ne_zero_of_prod_eq_one {s : Fin n → K} (hs : ∏ i, s i = 1) (i : Fin n) : s i ≠ 0 :=
  fun h => one_ne_zero (hs ▸ Finset.prod_eq_zero (Finset.mem_univ i) h)

theorem diagElt_mul_comm (s s' : Fin n → K) (hs : ∏ i, s i = 1) (hs' : ∏ i, s' i = 1) :
    diagElt s hs * diagElt s' hs' = diagElt s' hs' * diagElt s hs := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, coe_diagElt, diagonal_mul_diagonal, mul_comm]

theorem diagElt_conj_rootElt (s : Fin n → K) (hs : ∏ i, s i = 1) (i j : Fin n) (a : K) :
    diagElt s hs * rootElt i j a * (diagElt s hs)⁻¹ = rootElt i j (s i * (s j)⁻¹ * a) := by
  by_cases hij : i = j
  · rw [hij, rootElt_self, rootElt_self, mul_one, mul_inv_cancel]
  have hs0 := ne_zero_of_prod_eq_one hs
  have hinv : ∏ i, (s i)⁻¹ = 1 := by rw [Finset.prod_inv_distrib, hs, inv_one]
  have hdinv : (diagElt s hs)⁻¹ = diagElt (fun i => (s i)⁻¹) hinv := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    rw [SpecialLinearGroup.coe_mul, coe_diagElt, coe_diagElt, diagonal_mul_diagonal,
      SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hs0 k)
  rw [hdinv]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_diagElt, coe_diagElt,
    coe_rootElt_of_ne hij, coe_rootElt_of_ne hij,
    TauCeti.diagonal_mul_transvection_mul_diagonal (fun k => mul_inv_cancel₀ (hs0 k))]
  congr 1
  ring

@[expose] def corootVec (p q : Fin n) (c : K) : Fin n → K :=
  Pi.mulSingle p c * Pi.mulSingle q c⁻¹

theorem prod_corootVec (p q : Fin n) {c : K} (hc : c ≠ 0) : ∏ i, corootVec p q c i = 1 := by
  simp only [corootVec, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
  exact mul_inv_cancel₀ hc

theorem corootVec_apply_left {p q : Fin n} (h : p ≠ q) (c : K) : corootVec p q c p = c := by
  simp [corootVec, Pi.mulSingle_eq_of_ne h]

theorem corootVec_apply_right {p q : Fin n} (h : p ≠ q) (c : K) : corootVec p q c q = c⁻¹ := by
  simp [corootVec, Pi.mulSingle_eq_of_ne h.symm]

theorem corootVec_apply_of_ne {p q r : Fin n} (hp : r ≠ p) (hq : r ≠ q) (c : K) :
    corootVec p q c r = 1 := by
  simp [corootVec, Pi.mulSingle_eq_of_ne hp, Pi.mulSingle_eq_of_ne hq]

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
