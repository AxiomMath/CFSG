module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatHexa

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open Equiv

@[expose] def pairVec (a b : Fin 6) : Fin 6 → ZMod 2 := Pi.single a 1 + Pi.single b 1

@[expose] def evenize (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => if i = 0 then ∑ s : Fin 5, v s.succ else v i

theorem sum_evenize (v : Fin 6 → ZMod 2) : ∑ i, evenize v i = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [evenize, Fin.succ_ne_zero, ↓reduceIte]
  rw [← two_mul]
  exact mul_eq_zero_of_left (by decide) _

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem decide_add_eq_one : ∀ a b : ZMod 2,
    decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  decide

section Mod

variable {M : Type*} [CommGroup M]

@[expose] def natTheta (t : Fin 6 → Fin 6 → M) (v : Fin 6 → ZMod 2) : M :=
  ∏ s : Fin 5, boolPow (decide (v s.succ = 1)) (t 0 s.succ)

theorem natTheta_zero (t : Fin 6 → Fin 6 → M) : natTheta t 0 = 1 := by
  simp [natTheta, boolPow]

theorem natTheta_evenize (t : Fin 6 → Fin 6 → M) (v : Fin 6 → ZMod 2) :
    natTheta t (evenize v) = natTheta t v := by
  simp only [natTheta, evenize, Fin.succ_ne_zero, ↓reduceIte]

theorem boolPow_map {N : Type*} [CommGroup N] (f : M →* N) (c : Bool) (x : M) :
    f (boolPow c x) = boolPow c (f x) := by
  cases c <;> simp [boolPow]

variable (hsq : ∀ x : M, x * x = 1)
include hsq

theorem natTheta_add (t : Fin 6 → Fin 6 → M) (v w : Fin 6 → ZMod 2) :
    natTheta t (v + w) = natTheta t v * natTheta t w := by
  simp only [natTheta, Pi.add_apply, decide_add_eq_one, boolPow_xor hsq, Finset.prod_mul_distrib]

@[expose] def natThetaHom (t : Fin 6 → Fin 6 → M) : Multiplicative (Fin 6 → ZMod 2) →* M where
  toFun v := natTheta t (Multiplicative.toAdd v)
  map_one' := natTheta_zero t
  map_mul' _ _ := natTheta_add hsq t _ _

omit hsq in
theorem natTheta_smul (t : Fin 6 → Fin 6 → M) (c : ZMod 2) (v : Fin 6 → ZMod 2) :
    natTheta t (c • v) = boolPow (decide (c = 1)) (natTheta t v) := by
  rcases zmod2_cases c with rfl | rfl
  · simp [natTheta_zero, boolPow]
  · simp [boolPow]

theorem natTheta_sum (t : Fin 6 → Fin 6 → M) (w : Fin 5 → Fin 6 → ZMod 2) :
    natTheta t (∑ s, w s) = ∏ s, natTheta t (w s) := by
  have h := map_prod (natThetaHom hsq t) (fun s => Multiplicative.ofAdd (w s)) Finset.univ
  rw [← ofAdd_sum] at h
  exact h

variable {t : Fin 6 → Fin 6 → M} (hsymm : ∀ a b, t a b = t b a)
  (htri : ∀ j j' : Fin 6, j ≠ 0 → j' ≠ 0 → j ≠ j' → t 0 j * t 0 j' * t j j' = 1)

omit hsq in
theorem prod_boolPow_eq (a : Fin 6) :
    ∏ s : Fin 5, boolPow (decide (s.succ = a)) (t 0 s.succ) = if a = 0 then 1 else t 0 a := by
  have h := Fin.prod_univ_succ (fun i : Fin 6 => boolPow (decide (i = a)) (t 0 i))
  simp only [boolPow, decide_eq_true_eq, Finset.prod_ite_eq', Finset.mem_univ, ite_true] at h
  split_ifs with ha
  · subst ha
    simp only [boolPow, decide_eq_true_eq, Fin.succ_ne_zero, ite_false, Finset.prod_const_one]
  · rw [h, ite_eq_right (Ne.symm ha), one_mul]
    simp only [boolPow, decide_eq_true_eq]

include hsymm htri

theorem natTheta_pairVec {a b : Fin 6} (hab : a ≠ b) : natTheta t (pairVec a b) = t a b := by
  have hsplit : natTheta t (pairVec a b) =
      (∏ s : Fin 5, boolPow (decide (s.succ = a)) (t 0 s.succ)) *
        ∏ s : Fin 5, boolPow (decide (s.succ = b)) (t 0 s.succ) := by
    unfold pairVec
    rw [natTheta_add hsq]
    congr 1 <;> refine Finset.prod_congr rfl fun s _ => ?_ <;> congr 1 <;>
      simp [Pi.single_apply]
  rw [hsplit, prod_boolPow_eq, prod_boolPow_eq]
  by_cases ha : a = 0
  · subst ha
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab), one_mul]
  · by_cases hb : b = 0
    · subst hb
      rw [ite_eq_right ha, ite_eq_left rfl, mul_one, hsymm]
    · rw [ite_eq_right ha, ite_eq_right hb]
      have h := htri a b ha hb hab
      calc t 0 a * t 0 b = t 0 a * t 0 b * t a b * t a b := by rw [mul_assoc _ (t a b), hsq,
            mul_one]
        _ = t a b := by rw [h, one_mul]

omit hsq hsymm htri in
theorem eq_sum_pairVec {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    v = ∑ s : Fin 5, v s.succ • pairVec 0 s.succ := by
  have hv0 : v 0 = ∑ s : Fin 5, v s.succ := by
    rw [Fin.sum_univ_succ] at hv
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc v 0 = v 0 + (v 0 + ∑ s : Fin 5, v s.succ) := by rw [hv, add_zero]
      _ = 2 * v 0 + ∑ s : Fin 5, v s.succ := by ring
      _ = ∑ s : Fin 5, v s.succ := by rw [h2, zero_mul, zero_add]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, pairVec, Pi.add_apply, smul_eq_mul]
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [hv0]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Fin.succ_ne_zero s).symm, add_zero, mul_one]
  · rw [Finset.sum_eq_single i']
    · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i'), Pi.single_eq_same, zero_add, mul_one]
    · intro s _ hs
      rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i'), Pi.single_eq_of_ne
        (fun h => hs (Fin.succ_injective _ h).symm), add_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i') h

omit hsq hsymm htri in
theorem pairVec_comp (π : Perm (Fin 6)) (a b : Fin 6) :
    (fun i => pairVec a b (π⁻¹ i)) = pairVec (π a) (π b) := by
  funext i
  simp only [pairVec, Pi.add_apply, Pi.single_apply, Perm.inv_eq_iff_eq]

theorem natTheta_comp (f : M →* M) (π : Perm (Fin 6))
    (hf : ∀ a b, a ≠ b → f (t a b) = t (π a) (π b)) {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    f (natTheta t v) = natTheta t (fun i => v (π⁻¹ i)) := by
  have hvπ : (fun i => v (π⁻¹ i)) = ∑ s : Fin 5, v s.succ • pairVec (π 0) (π s.succ) := by
    conv_lhs => rw [eq_sum_pairVec hv]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact congrArg _ (congrFun (pairVec_comp π 0 s.succ) i)
  have hne : ∀ s : Fin 5, π 0 ≠ π s.succ := fun s h => Fin.succ_ne_zero s (π.injective h).symm
  rw [hvπ, natTheta_sum hsq]
  conv_lhs => rw [eq_sum_pairVec hv, natTheta_sum hsq]
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [natTheta_smul, natTheta_smul, boolPow_map, natTheta_pairVec hsq hsymm htri (hne s),
    natTheta_pairVec hsq hsymm htri (Fin.succ_ne_zero s).symm, hf 0 s.succ
      (Fin.succ_ne_zero s).symm]

omit hsymm htri in
theorem natTheta_eq_one_iff (hone : ∏ s : Fin 5, t 0 s.succ = 1)
    (hsurj : ∀ m : M, ∃ v, natTheta t v = m) (h16 : Nat.card M = 16) {v : Fin 6 → ZMod 2}
    (hv : ∑ i, v i = 0) : natTheta t v = 1 ↔ v = 0 ∨ v = fun _ => 1 := by
  constructor
  · intro h1
    let f₅ : Multiplicative (Fin 5 → ZMod 2) →* M :=
      { toFun := fun w => ∏ s : Fin 5, boolPow (decide (Multiplicative.toAdd w s = 1)) (t 0 s.succ)
        map_one' := by simp [boolPow]
        map_mul' := fun w w' => by
          simp only [toAdd_mul, Pi.add_apply, decide_add_eq_one, boolPow_xor hsq,
            Finset.prod_mul_distrib] }
    have hf₅ : ∀ w : Fin 6 → ZMod 2, f₅ (Multiplicative.ofAdd (fun s => w s.succ)) =
        natTheta t w := fun w => rfl
    have hsurj₅ : Function.Surjective f₅ := fun m => by
      obtain ⟨w, hw⟩ := hsurj m
      exact ⟨_, (hf₅ w).trans hw⟩
    have hcard : Nat.card f₅.ker = 2 := by
      have h := Subgroup.card_ker_mul_card_range f₅
      rw [MonoidHom.range_eq_top.mpr hsurj₅, Subgroup.card_top, h16] at h
      have h32 : Nat.card (Multiplicative (Fin 5 → ZMod 2)) = 32 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      omega
    have hall : f₅ (Multiplicative.ofAdd fun _ => 1) = 1 := by
      simp only [f₅, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, decide_true, boolPow,
        ite_true]
      exact hone
    have hw : f₅ (Multiplicative.ofAdd fun s => v s.succ) = 1 := (hf₅ v).trans h1
    obtain ⟨a, b, hab, hset⟩ := Nat.card_eq_two_iff.mp hcard
    have hmem : ∀ c : ↥f₅.ker, c = a ∨ c = b := fun c => by
      have : c ∈ ({a, b} : Set ↥f₅.ker) := hset ▸ Set.mem_univ c
      simpa using this
    let c₀ : ↥f₅.ker := ⟨1, one_mem _⟩
    let c₁ : ↥f₅.ker := ⟨Multiplicative.ofAdd fun _ => 1, hall⟩
    let cv : ↥f₅.ker := ⟨Multiplicative.ofAdd fun s => v s.succ, hw⟩
    have h01 : c₀ ≠ c₁ := fun h => by
      have h' := congrArg (fun c : ↥f₅.ker =>
        (Multiplicative.toAdd (c : Multiplicative (Fin 5 → ZMod 2)) : Fin 5 → ZMod 2) 0) h
      change (0 : ZMod 2) = 1 at h'
      exact absurd h' (by decide)
    have hcv : cv = c₀ ∨ cv = c₁ := by
      rcases hmem c₀ with h0 | h0 <;> rcases hmem c₁ with h1' | h1' <;>
        rcases hmem cv with h2 | h2
      all_goals first
        | exact absurd (h0.trans h1'.symm) h01
        | exact Or.inl (h2.trans h0.symm)
        | exact Or.inr (h2.trans h1'.symm)
    have hv0 : v 0 = ∑ s : Fin 5, v s.succ := by
      rw [Fin.sum_univ_succ] at hv
      have h2 : (2 : ZMod 2) = 0 := by decide
      calc v 0 = v 0 + (v 0 + ∑ s : Fin 5, v s.succ) := by rw [hv, add_zero]
        _ = 2 * v 0 + ∑ s : Fin 5, v s.succ := by ring
        _ = ∑ s : Fin 5, v s.succ := by rw [h2, zero_mul, zero_add]
    rcases hcv with h | h
    · have hs : ∀ s : Fin 5, v s.succ = 0 := fun s =>
        congrArg (fun c : ↥f₅.ker =>
          (Multiplicative.toAdd (c : Multiplicative (Fin 5 → ZMod 2)) : Fin 5 → ZMod 2) s) h
      left
      funext i
      refine Fin.cases ?_ (fun s => hs s) i
      rw [hv0]
      simp [hs]
    · have hs : ∀ s : Fin 5, v s.succ = 1 := fun s =>
        congrArg (fun c : ↥f₅.ker =>
          (Multiplicative.toAdd (c : Multiplicative (Fin 5 → ZMod 2)) : Fin 5 → ZMod 2) s) h
      right
      funext i
      refine Fin.cases ?_ (fun s => hs s) i
      rw [hv0]
      simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      decide
  · rintro (rfl | rfl)
    · exact natTheta_zero t
    · simp only [natTheta, decide_true, boolPow, ite_true]
      exact hone

end Mod

end CFSG.ComponentClassification.AS81.Hexa
