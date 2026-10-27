module

public import CFSG.CGT.Stroth77.L4Sylow.Std
public import CFSG.CGT.Stroth77.L4Sylow.Model

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv Matrix CFSG.GH74.GLS.Stage1.Thm3.Sec8

theorem two_pow_type200_k_dvd (m : ℕ) (i : Fin 3) : 2 ^ Type200.k m i ∣ 2 ^ (m + 2) := by
  refine pow_dvd_pow 2 ?_
  fin_cases i <;> simp [Type200.k]

@[expose] def cZ (m : ℕ) : (Fin 4 → ZMod (2 ^ (m + 2))) →+ Torus (Type200.k m) :=
  AddMonoidHom.mk' (fun d i => ZMod.castHom (two_pow_type200_k_dvd m i)
    (ZMod (2 ^ Type200.k m i)) (![d 1, d 1 - d 2, d 1 - d 3] i)) fun d e => by
      funext i
      simp only [Pi.add_apply]
      rw [← map_add]
      congr 1
      fin_cases i <;> simp [add_sub_add_comm]

variable {m : ℕ}

theorem cZ_apply (d : Fin 4 → ZMod (2 ^ (m + 2))) (i : Fin 3) :
    cZ m d i = ZMod.castHom (two_pow_type200_k_dvd m i) (ZMod (2 ^ Type200.k m i))
      (![d 1, d 1 - d 2, d 1 - d 3] i) := rfl

theorem cZ_intCast (v : Fin 4 → ℤ) :
    cZ m (fun i => (v i : ZMod (2 ^ (m + 2)))) = Torus.ofInt _ (cVec v) := by
  funext i
  fin_cases i <;> simp [cZ_apply, cVec, -ZMod.castHom_apply]

theorem cZ_const_intCast (z : ℤ) :
    cZ m (fun _ => (z : ZMod (2 ^ (m + 2)))) = Torus.ofInt _ ![z, 0, 0] := by
  rw [cZ_intCast (fun _ => z)]
  congr 1
  funext i
  fin_cases i <;> simp [cVec]

theorem exists_intCast_eq_of_sum_eq_zero {N : ℕ} {e : Fin 4 → ZMod N} (he : ∑ i, e i = 0) :
    ∃ v : Fin 4 → ℤ, ∑ i, v i = 0 ∧ (fun i => (v i : ZMod N)) = e := by
  choose w hw using fun i => ZMod.intCast_surjective (e i)
  rw [Fin.sum_univ_four] at he
  refine ⟨![-(w 1 + w 2 + w 3), w 1, w 2, w 3], ?_, ?_⟩
  · rw [Fin.sum_univ_four]
    change -(w 1 + w 2 + w 3) + w 1 + w 2 + w 3 = 0
    ring
  · funext i
    fin_cases i
    · change ((-(w 1 + w 2 + w 3) : ℤ) : ZMod N) = e 0
      push_cast
      rw [hw 1, hw 2, hw 3]
      linear_combination -he
    · exact hw 1
    · exact hw 2
    · exact hw 3

theorem cZ_perm (π : Perm (Fin 4)) {e : Fin 4 → ZMod (2 ^ (m + 2))} (he : ∑ i, e i = 0) :
    cZ m (fun i => e (π⁻¹ i)) = matAct _ (wM π) (compat_wM m π) (cZ m e) := by
  obtain ⟨v, hv0, rfl⟩ := exists_intCast_eq_of_sum_eq_zero he
  rw [cZ_intCast, cZ_intCast, matAct_wM_ofInt, wVec, bVec_cVec hv0]

@[expose] def sZ (m : ℕ) (π : Perm (Fin 4)) : ZMod (2 ^ (m + 2)) :=
  ((if Perm.sign π = 1 then 0 else 2 ^ (m - 1) : ℤ) : ZMod (2 ^ (m + 2)))

theorem sZ_one : sZ m 1 = 0 := by
  simp [sZ]

theorem four_mul_sZ_add_signZ (hm : 1 ≤ m) (π : Perm (Fin 4)) :
    4 * sZ m π + Multiplicative.toAdd (signZ (m + 2) (Perm.sign π)) = 0 := by
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · rw [sZ, h, if_pos rfl, signZ_one, toAdd_one]
    simp
  · rw [sZ, h, if_neg (by decide), signZ_neg_one, toAdd_ofAdd]
    have h2 : (4 * 2 ^ (m - 1) + 2 ^ (m + 2 - 1) : ℕ) = 2 ^ (m + 2) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [show k + 1 - 1 = k by omega, show k + 1 + 2 - 1 = k + 2 by omega]
      ring
    have h3 : ((4 * 2 ^ (m - 1) + 2 ^ (m + 2 - 1) : ℕ) : ZMod (2 ^ (m + 2))) = 0 := by
      rw [h2]
      exact ZMod.natCast_self _
    push_cast at h3 ⊢
    exact h3

theorem sum_sub_sZ (hm : 1 ≤ m) {a : L4Hat (m + 2)} (ha : a ∈ L4P (m + 2)) :
    ∑ i, (Multiplicative.toAdd a.left i - sZ m a.right) = 0 := by
  have h := congrArg Multiplicative.toAdd (mem_L4P.mp ha)
  rw [detL4_apply, toAdd_one] at h
  have h4 := four_mul_sZ_add_signZ hm (a.right : Perm (Fin 4))
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linear_combination h - h4

theorem cZ_sZ_add_sZ_sub (hm : 1 ≤ m) (π σ : Perm (Fin 4)) :
    cZ m (fun _ => sZ m π + sZ m σ - sZ m (π * σ)) = 0 := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have key : ∃ z : ℤ, (2 : ℤ) ^ m ∣ z ∧ sZ m π + sZ m σ - sZ m (π * σ) = (z : ZMod _) := by
    unfold sZ
    rw [Perm.sign_mul]
    rcases Int.units_eq_one_or (Perm.sign π) with h | h <;>
      rcases Int.units_eq_one_or (Perm.sign σ) with h' | h' <;> rw [h, h']
    · exact ⟨0, dvd_zero _, by simp⟩
    · exact ⟨0, dvd_zero _, by simp [hne]⟩
    · exact ⟨0, dvd_zero _, by simp [hne]⟩
    · refine ⟨2 ^ m, dvd_rfl, ?_⟩
      have h2 : (2 : ℤ) ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [show k + 1 - 1 = k by omega]
        ring
      have h11 : (-1 : ℤˣ) * -1 = 1 := by decide
      rw [h11, if_neg hne, if_pos rfl, ← h2, Int.cast_add, Int.cast_zero, sub_zero]
  obtain ⟨z, hz, hzeq⟩ := key
  rw [hzeq, cZ_const_intCast, Torus.ofInt_eq_zero_iff]
  intro i
  fin_cases i
  · simpa [Type200.k] using hz
  · simp
  · simp

theorem cZ_eq_of_eq_add_sZ (hm : 1 ≤ m) (π σ : Perm (Fin 4)) {X Y : Fin 4 → ZMod (2 ^ (m + 2))}
    (h : ∀ i, X i = Y i + (sZ m π + sZ m σ - sZ m (π * σ))) : cZ m X = cZ m Y := by
  have hXY : X = Y + fun _ => sZ m π + sZ m σ - sZ m (π * σ) := funext h
  rw [hXY, map_add, cZ_sZ_add_sZ_sub hm, add_zero]

@[expose] def psiHatFun (m : ℕ) (a : L4Hat (m + 2)) : L4Std m :=
  ⟨Multiplicative.ofAdd (cZ m fun i => Multiplicative.toAdd a.left i - sZ m a.right), a.right⟩

@[expose] def psiHat (hm : 1 ≤ m) : L4P (m + 2) →* L4Std m where
  toFun a := psiHatFun m a
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      simp only [psiHatFun, OneMemClass.coe_one, SemidirectProduct.one_left,
        SemidirectProduct.one_right, toAdd_ofAdd, toAdd_one, OneMemClass.coe_one, sZ_one,
        Pi.zero_apply, sub_zero]
      exact map_zero _
    · rfl
  map_mul' a b := by
    have hb := sum_sub_sZ hm b.2
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      simp only [psiHatFun, Subgroup.coe_mul, SemidirectProduct.mul_left,
        SemidirectProduct.mul_right, toAdd_ofAdd, toAdd_mul]
      rw [toAdd_ψ200, toAdd_ofAdd, ← cZ_perm _ hb, ← map_add (cZ m)]
      refine cZ_eq_of_eq_add_sZ hm ((a : L4Hat (m + 2)).right : Perm (Fin 4))
        ((b : L4Hat (m + 2)).right : Perm (Fin 4)) fun i => ?_
      simp only [Pi.add_apply, toAdd_mul, toAdd_actL4, Subgroup.coe_mul]
      ring
    · rfl

theorem psiHat_apply (hm : 1 ≤ m) (a : L4P (m + 2)) :
    psiHat hm a = ⟨Multiplicative.ofAdd (cZ m fun i =>
      Multiplicative.toAdd (a : L4Hat (m + 2)).left i - sZ m (a : L4Hat (m + 2)).right),
      (a : L4Hat (m + 2)).right⟩ := rfl

theorem psiHat_surjective (hm : 1 ≤ m) : Function.Surjective (psiHat hm) := by
  rintro ⟨x, π⟩
  obtain ⟨w, hw⟩ := Torus.exists_ofInt (Multiplicative.toAdd x)
  set d : Fin 4 → ZMod (2 ^ (m + 2)) := fun i => (bVec w i : ZMod (2 ^ (m + 2))) + sZ m π
    with hd
  have hmem : (⟨Multiplicative.ofAdd d, π⟩ : L4Hat (m + 2)) ∈ L4P (m + 2) := by
    rw [mem_L4P]
    apply Multiplicative.toAdd.injective
    rw [detL4_apply, toAdd_one]
    have h0 : ∑ i, (bVec w i : ZMod (2 ^ (m + 2))) = 0 := by
      rw [← Int.cast_sum, sum_bVec, Int.cast_zero]
    have h4 := four_mul_sZ_add_signZ hm (π : Perm (Fin 4))
    simp only [toAdd_ofAdd, hd, Finset.sum_add_distrib, h0, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, zero_add]
    push_cast
    exact h4
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [psiHat_apply]
    simp only [toAdd_ofAdd, hd, add_sub_cancel_right]
    rw [cZ_intCast, cVec_bVec, hw]
  · rfl

theorem psiHat_cL4 (hm : 1 ≤ m) : psiHat hm (cL4 (m + 2)) = 1 := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [psiHat_apply, coe_cL4]
    have h1 : ((cHat (m + 2)).right : Perm (Fin 4)) = 1 := rfl
    have h2 : ∀ i, Multiplicative.toAdd (cHat (m + 2)).left i =
        ((2 ^ m : ℤ) : ZMod (2 ^ (m + 2))) := fun i => by
        rw [show (cHat (m + 2)).left = Multiplicative.ofAdd (fun _ => zL4 (m + 2)) from rfl,
          toAdd_ofAdd, zL4, show m + 2 - 2 = m by omega]
        simp
    simp only [h1, h2, sZ_one, sub_zero, toAdd_ofAdd, SemidirectProduct.one_left, toAdd_one]
    rw [cZ_const_intCast, Torus.ofInt_eq_zero_iff]
    intro i
    fin_cases i
    · simp [Type200.k]
    · simp
    · simp
  · rfl

theorem ker_psiHat (hm : 1 ≤ m) : (psiHat hm).ker = Subgroup.zpowers (cL4 (m + 2)) := by
  refine le_antisymm (fun a ha => ?_) ((Subgroup.zpowers_le).mpr (psiHat_cL4 hm))
  rw [MonoidHom.mem_ker, psiHat_apply] at ha
  have hr : (a : L4Hat (m + 2)).right = 1 := congrArg SemidirectProduct.right ha
  have hl := congrArg (fun x : L4Std m => Multiplicative.toAdd x.left) ha
  simp only [toAdd_ofAdd, SemidirectProduct.one_left, toAdd_one, hr, OneMemClass.coe_one,
    sZ_one, sub_zero] at hl
  rw [mem_zpowers_cL4 (by omega)]
  refine ⟨hr, ?_⟩
  have hsum : ∑ i, Multiplicative.toAdd (a : L4Hat (m + 2)).left i = 0 := by
    have h := sum_sub_sZ hm a.2
    simpa only [hr, OneMemClass.coe_one, sZ_one, sub_zero] using h
  obtain ⟨v, hv0, hv⟩ := exists_intCast_eq_of_sum_eq_zero hsum
  rw [← hv, cZ_intCast, Torus.ofInt_eq_zero_iff] at hl
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  simp only [cVec, Type200.k, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  obtain ⟨t, ht⟩ := h0
  rw [Fin.sum_univ_four] at hv0
  have hv1 : ∀ i, (v i : ZMod (2 ^ (m + 2))) = (v 1 : ZMod (2 ^ (m + 2))) := by
    have e2 : (v 2 : ZMod (2 ^ (m + 2))) = v 1 := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact_mod_cast h1
    have e3 : (v 3 : ZMod (2 ^ (m + 2))) = v 1 := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact_mod_cast h2
    have e0 : (v 0 : ZMod (2 ^ (m + 2))) = v 1 := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      obtain ⟨s2, hs2⟩ := h1
      obtain ⟨s3, hs3⟩ := h2
      refine ⟨t - s2 - s3, ?_⟩
      push_cast
      linear_combination -hv0 + 4 * ht - hs2 - hs3
    intro i
    fin_cases i
    · exact e0
    · rfl
    · exact e2
    · exact e3
  intro i j
  rw [← hv]
  exact (hv1 i).trans (hv1 j).symm

@[expose] noncomputable def l4ModelEquivStd (hm : 1 ≤ m) : L4Model (m + 2) ≃* L4Std m :=
  (QuotientGroup.quotientMulEquivOfEq (ker_psiHat hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (psiHat_surjective hm))

end CFSG.CGT.Stroth77.L4Sylow
