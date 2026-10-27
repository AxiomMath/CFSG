module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.TwA5Cover

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] def coverLin (v : Fin 4 → ZMod 3) : Fin 6 → ZMod 3
  | 0 => v 0 + v 1 + v 2 + v 3
  | 1 => v 0 + v 1 + v 2 + v 3
  | 2 => v 0 + v 1 + v 3 + v 3
  | 3 => v 0 + v 1 + v 1 + v 2 + v 2 + v 3
  | 4 => v 0 + v 1 + v 1 + v 3
  | 5 => -((v 0 + v 1 + v 2 + v 3) + (v 0 + v 1 + v 2 + v 3) + (v 0 + v 1 + v 3 + v 3) +
      (v 0 + v 1 + v 1 + v 2 + v 2 + v 3) + (v 0 + v 1 + v 1 + v 3))

private theorem coverLin_add (v w : Fin 4 → ZMod 3) : coverLin (v + w) = coverLin v + coverLin w := by
  funext i
  fin_cases i <;> simp only [coverLin, Pi.add_apply] <;> abel

private theorem coverLin_sub (v w : Fin 4 → ZMod 3) : coverLin (v - w) = coverLin v - coverLin w := by
  funext i
  fin_cases i <;> simp only [coverLin, Pi.sub_apply] <;> abel

private theorem coverLin_zero : coverLin (0 : Fin 4 → ZMod 3) = 0 := by
  funext i
  fin_cases i <;> simp [coverLin] <;> exact neg_zero

private theorem coverLin_sum (v : Fin 4 → ZMod 3) : ∑ i, coverLin v i = 0 := by
  simp only [Fin.sum_univ_six, coverLin]
  abel

private theorem zmod_three (a : ZMod 3) : a + a + a = 0 := by
  fin_cases a <;> decide

private theorem omega_pow_val_add {ω : F} (hω3 : ω ^ 3 = 1) (a b : ZMod 3) :
    ω ^ ((a + b).val) = ω ^ a.val * ω ^ b.val := by
  have hmod : (a + b).val ≡ a.val + b.val [MOD 3] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  rw [pow_eq_pow_of_modEq hmod hω3, pow_add]

noncomputable abbrev coverEntry {ω : F} (v : Fin 4 → ZMod 3) : Fin 6 → F :=
  fun i => ω ^ (coverLin v i).val

private theorem coverEntry_add {ω : F} (hω3 : ω ^ 3 = 1) (v w : Fin 4 → ZMod 3) :
    coverEntry (ω := ω) (v + w) = coverEntry (ω := ω) v * coverEntry (ω := ω) w := by
  funext i
  simp only [coverEntry, Pi.mul_apply, coverLin_add, Pi.add_apply]
  exact omega_pow_val_add hω3 _ _

private theorem coverEntry_zero {ω : F} : coverEntry (ω := ω) (0 : Fin 4 → ZMod 3) = 1 := by
  funext i
  fin_cases i <;> simp [coverEntry, coverLin] <;>
    rw [show (-(0 : ZMod 3)) = 0 from neg_zero, ZMod.val_zero, pow_zero]

private theorem omega_order {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : orderOf ω = 3 := by
  have hdvd : orderOf ω ∣ 3 := orderOf_dvd_of_pow_eq_one hω3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    exact hω1 h1
  · exact h3'

private theorem omega_pow_val_eq {ω : F} (h : UnitaryFieldData 2 n F) (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) {a b : ℕ}
    (ha : a < 3) (hb : b < 3) (hpow : ω ^ a = ω ^ b) : a = b := by
  have hne : ω ≠ 0 := CFSG.GH74.Uniqueness.Bender.Frame.ne_zero_of_norm_eq_one hωnorm
  rcases le_total b a with hba | hab
  · have hb0 : ω ^ b ≠ 0 := pow_ne_zero _ hne
    have hsplit : ω ^ (a - b) * ω ^ b = ω ^ b := by
      rw [← pow_add, Nat.sub_add_cancel hba, hpow]
    have hd : ω ^ (a - b) = 1 := mul_right_cancel₀ hb0 (by rwa [one_mul])
    have h3 : orderOf ω ∣ a - b := (orderOf_dvd_iff_pow_eq_one).2 hd
    rw [omega_order hω3 hω1] at h3
    obtain ⟨k, hk⟩ := h3
    omega
  · have ha0 : ω ^ a ≠ 0 := pow_ne_zero _ hne
    have hsplit : ω ^ (b - a) * ω ^ a = ω ^ a := by
      rw [← pow_add, Nat.sub_add_cancel hab, ← hpow]
    have hd : ω ^ (b - a) = 1 := mul_right_cancel₀ ha0 (by rwa [one_mul])
    have h3 : orderOf ω ∣ b - a := (orderOf_dvd_iff_pow_eq_one).2 hd
    rw [omega_order hω3 hω1] at h3
    obtain ⟨k, hk⟩ := h3
    omega

theorem coverNorm (h : UnitaryFieldData 2 n F) {ω : F} (hωnorm : h.norm ω = 1)
    (v : Fin 4 → ZMod 3) : ∀ i, h.norm (coverEntry (ω := ω) v i) = 1 := by
  intro i
  rw [coverEntry]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.unitaryNorm_pow_eq_one h hωnorm (coverLin v i).val

theorem coverDet (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (v : Fin 4 → ZMod 3) : ∏ i, coverEntry (ω := ω) v i = 1 := by
  change ∏ i, ω ^ (coverLin v i).val = 1
  rw [Finset.prod_pow_eq_pow_sum]
  have hcast : ((∑ i, (coverLin v i).val : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact coverLin_sum v
  have h3 : 3 ∣ ∑ i, (coverLin v i).val :=
    (ZMod.natCast_eq_zero_iff _ 3).1 hcast
  exact (orderOf_dvd_iff_pow_eq_one).1 (by rw [omega_order hω3 hω1]; exact h3)

noncomputable abbrev coverDiag (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (v : Fin 4 → ZMod 3) : unitarySU 2 n F 6 :=
  diagSU h (coverEntry (ω := ω) v) (coverNorm h hωnorm v) (coverDet h hω3 hω1 v)

theorem coe_coverDiag (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (v : Fin 4 → ZMod 3) :
    (((coverDiag h hω3 hωnorm hω1 v : unitarySU 2 n F 6) : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) = diagonal (coverEntry (ω := ω) v) :=
  rfl

theorem coverDiag_zero (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    coverDiag h hω3 hωnorm hω1 (0 : Fin 4 → ZMod 3) = 1 := by
  apply Subtype.ext; apply Units.ext
  rw [coe_coverDiag, coverEntry_zero]
  simp [Matrix.diagonal_one]

theorem coverDiag_mul (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (v w : Fin 4 → ZMod 3) :
    coverDiag h hω3 hωnorm hω1 (v + w) =
      coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 w := by
  apply Subtype.ext; apply Units.ext
  rw [coe_coverDiag, Subgroup.coe_mul, Units.val_mul, coe_coverDiag, coe_coverDiag,
    diagonal_mul_diagonal, coverEntry_add hω3]
  rfl

private theorem coverDiag_inj (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    Function.Injective (coverDiag h hω3 hωnorm hω1) := by
  intro v w hvw
  have hentry : coverEntry (ω := ω) v = coverEntry (ω := ω) w := by
    have hmat := congrArg (fun z : unitarySU 2 n F 6 =>
      ((z : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hvw
    rw [coe_coverDiag, coe_coverDiag] at hmat
    funext i
    have := congrFun (congrFun hmat i) i
    simpa only [Matrix.diagonal_apply_eq] using this
  have hlin : ∀ i, coverLin v i = coverLin w i := by
    intro i
    have hpow : ω ^ (coverLin v i).val = ω ^ (coverLin w i).val := congrFun hentry i
    have hval : (coverLin v i).val = (coverLin w i).val :=
      omega_pow_val_eq h hω3 hωnorm hω1 (ZMod.val_lt _) (ZMod.val_lt _) hpow
    rw [← ZMod.natCast_zmod_val (coverLin v i), ← ZMod.natCast_zmod_val (coverLin w i), hval]
  have hu : ∀ i, coverLin (v - w) i = 0 := by
    intro i
    rw [coverLin_sub, Pi.sub_apply, hlin i, sub_self]
  have h0 := hu 0
  have h2 := hu 2
  have h3 := hu 3
  have h4 := hu 4
  set u : Fin 4 → ZMod 3 := v - w with hu'
  have e1 : u 2 = u 3 := by
    simp only [coverLin] at h0 h2
    linear_combination h0 - h2
  have e2 : u 1 = u 3 := by
    simp only [coverLin] at h2 h4
    linear_combination h4 - h2
  have e3 : u 0 = 0 := by
    simp only [coverLin] at h0
    rw [e2, e1] at h0
    have h3z : (3 : ZMod 3) = 0 := by decide
    have h : u 0 + (3 : ZMod 3) * u 3 = 0 := by linear_combination h0
    rwa [h3z, zero_mul, add_zero] at h
  have e4 : u 3 = 0 := by
    simp only [coverLin] at h3
    rw [e3, e2, e1] at h3
    have h : (2 : ZMod 3) * u 3 = 0 := by
      have hh := h3
      have hh5 : (5 : ZMod 3) * u 3 = 0 := by linear_combination hh
      rwa [show (5 : ZMod 3) = 2 by decide] at hh5
    exact (mul_eq_zero.mp h).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
  have huzero : u = 0 := by
    funext i
    fin_cases i
    · exact e3
    · simpa [e2] using e4
    · simpa [e1] using e4
    · exact e4
  have hsub : v - w = 0 := by rw [← hu']; exact huzero
  exact sub_eq_zero.mp hsub


open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

noncomputable abbrev coverSubgroup (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) : Subgroup (unitarySU 2 n F 6) where
  carrier := Set.range (coverDiag h hω3 hωnorm hω1)
  one_mem' := ⟨0, coverDiag_zero h hω3 hωnorm hω1⟩
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, coverDiag_mul h hω3 hωnorm hω1 v w⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    have h3v : v + v + v = 0 := by
      funext i
      exact zmod_three (v i)
    have h3 : coverDiag h hω3 hωnorm hω1 v ^ 3 = 1 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      rw [← coverDiag_mul h hω3 hωnorm hω1 v v]
      rw [← coverDiag_mul h hω3 hωnorm hω1 (v + v) v]
      rw [show (v + v) + v = 0 from h3v, coverDiag_zero]
    refine ⟨v + v, ?_⟩
    have hinv : (coverDiag h hω3 hωnorm hω1 v)⁻¹ =
        coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 v := by
      have h3' : coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 v *
          coverDiag h hω3 hωnorm hω1 v = 1 := by
        simpa [pow_succ, pow_two, mul_assoc] using h3
      calc (coverDiag h hω3 hωnorm hω1 v)⁻¹
          = (coverDiag h hω3 hωnorm hω1 v)⁻¹ * 1 := by rw [mul_one]
        _ = (coverDiag h hω3 hωnorm hω1 v)⁻¹ *
              (coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 v *
                coverDiag h hω3 hωnorm hω1 v) := by rw [h3']
        _ = coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 v := by group
    rw [hinv, coverDiag_mul h hω3 hωnorm hω1 v v]

theorem coverSubgroup_card (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    Nat.card (coverSubgroup h hω3 hωnorm hω1) = 3 ^ 4 := by
  have hinj : Function.Injective (coverDiag h hω3 hωnorm hω1) :=
    coverDiag_inj h hω3 hωnorm hω1
  let f : (Fin 4 → ZMod 3) → coverSubgroup h hω3 hωnorm hω1 :=
    fun v => ⟨coverDiag h hω3 hωnorm hω1 v, ⟨v, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w hvw => hinj (Subtype.ext_iff.mp hvw), ?_⟩
    rintro ⟨x, v, rfl⟩
    exact ⟨v, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_pi, Nat.card_zmod]

theorem coverSubgroup_elem (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    IsElemAbelian 3 (coverSubgroup h hω3 hωnorm hω1) := by
  refine ⟨⟨⟨fun A C => ?_⟩⟩, fun A hA => ?_⟩
  · obtain ⟨v, hv⟩ := A.2
    obtain ⟨w, hw⟩ := C.2
    have hA : A = ⟨coverDiag h hω3 hωnorm hω1 v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
    have hC : C = ⟨coverDiag h hω3 hωnorm hω1 w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
    rw [hA, hC]
    apply Subtype.ext
    change coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 w =
      coverDiag h hω3 hωnorm hω1 w * coverDiag h hω3 hωnorm hω1 v
    rw [← coverDiag_mul h hω3 hωnorm hω1 v w,
      ← coverDiag_mul h hω3 hωnorm hω1 w v, add_comm]
  · obtain ⟨v, rfl⟩ := hA
    have h3v : v + v + v = 0 := by
      funext i
      exact zmod_three (v i)
    calc coverDiag h hω3 hωnorm hω1 v ^ 3
        = coverDiag h hω3 hωnorm hω1 v * coverDiag h hω3 hωnorm hω1 v *
            coverDiag h hω3 hωnorm hω1 v := by
              rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      _ = coverDiag h hω3 hωnorm hω1 (v + v) * coverDiag h hω3 hωnorm hω1 v := by
            rw [← coverDiag_mul h hω3 hωnorm hω1 v v]
      _ = coverDiag h hω3 hωnorm hω1 ((v + v) + v) := by
            rw [← coverDiag_mul h hω3 hωnorm hω1 (v + v) v]
      _ = coverDiag h hω3 hωnorm hω1 0 := by rw [h3v]
      _ = 1 := coverDiag_zero h hω3 hωnorm hω1


open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] def vx : Fin 4 → ZMod 3 := fun i => if i = 0 then 1 else 0

@[expose] def vA : Fin 4 → ZMod 3 := fun i => if i = 0 then 2 else if i = 1 then 1 else 0

@[expose] def vB : Fin 4 → ZMod 3 :=
  fun i => if i = 0 then 2 else if i = 1 then 1 else if i = 2 then 2 else 1

private theorem coverLin_vx (i : Fin 6) : coverLin vx i = 1 := by
  fin_cases i <;> simp [coverLin, vx] <;> decide

private theorem coverLin_vA (i : Fin 6) :
    coverLin vA i = if i ∈ ({0, 1, 2} : Finset (Fin 6)) then 0 else 1 := by
  fin_cases i <;> simp [coverLin, vA] <;> decide

private theorem coverLin_vB (i : Fin 6) :
    coverLin vB i = if i ∈ ({0, 1, 3} : Finset (Fin 6)) then 0 else 2 := by
  fin_cases i <;> simp [coverLin, vB] <;> decide

private theorem zmod_val_zero : (0 : ZMod 3).val = 0 := rfl
private theorem zmod_val_one : (1 : ZMod 3).val = 1 := rfl
private theorem zmod_val_two : (2 : ZMod 3).val = 2 := rfl

theorem coverEntry_vx {ω : F} : coverEntry (ω := ω) vx = fun _ => ω := by
  funext i
  rw [coverEntry, coverLin_vx, zmod_val_one, pow_one]

private theorem coverEntry_vA {ω : F} : coverEntry (ω := ω) vA =
    fun i => if i ∈ ({0, 1, 2} : Finset (Fin 6)) then 1 else ω := by
  funext i
  rw [coverEntry, coverLin_vA]
  by_cases h : i ∈ ({0, 1, 2} : Finset (Fin 6))
  · simp [h, zmod_val_zero]
  · simp [h, zmod_val_one]

private theorem coverEntry_vB {ω : F} : coverEntry (ω := ω) vB =
    fun i => if i ∈ ({0, 1, 3} : Finset (Fin 6)) then 1 else ω ^ 2 := by
  funext i
  rw [coverEntry, coverLin_vB]
  by_cases h : i ∈ ({0, 1, 3} : Finset (Fin 6))
  · simp [h, zmod_val_zero]
  · simp [h, zmod_val_two]


open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem centralizer_vA (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    Subgroup.centralizer ({coverDiag h hω3 hωnorm hω1 vA} : Set (unitarySU 2 n F 6)) =
      unitaryBlockDiag h ({0, 1, 2} : Finset (Fin 6)) := by
  have hlν : (1 : F) ≠ ω := fun hh => hω1 hh.symm
  have hv : ∀ i, coverEntry (ω := ω) vA i =
      if i ∈ ({0, 1, 2} : Finset (Fin 6)) then (1 : F) else ω :=
    fun i => congrFun coverEntry_vA i
  simpa [coverDiag] using
    centralizer_diagSU_eq_unitaryBlockDiag (h := h) (I := ({0, 1, 2} : Finset (Fin 6)))
      (l := (1 : F)) (ν := ω) hlν (d := coverEntry (ω := ω) vA) hv
      (coverNorm h hωnorm vA) (coverDet h hω3 hω1 vA)

theorem centralizer_vB (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    Subgroup.centralizer ({coverDiag h hω3 hωnorm hω1 vB} : Set (unitarySU 2 n F 6)) =
      unitaryBlockDiag h ({0, 1, 3} : Finset (Fin 6)) := by
  have hlν : (1 : F) ≠ ω ^ 2 := by
    intro hh
    have h : ω ^ 3 = ω := by
      rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, ← hh, mul_one]
    rw [h] at hω3
    exact hω1 hω3
  have hv : ∀ i, coverEntry (ω := ω) vB i =
      if i ∈ ({0, 1, 3} : Finset (Fin 6)) then (1 : F) else ω ^ 2 :=
    fun i => congrFun coverEntry_vB i
  simpa [coverDiag] using
    centralizer_diagSU_eq_unitaryBlockDiag (h := h) (I := ({0, 1, 3} : Finset (Fin 6)))
      (l := (1 : F)) (ν := ω ^ 2) hlν (d := coverEntry (ω := ω) vB) hv
      (coverNorm h hωnorm vB) (coverDet h hω3 hω1 vB)


open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] def eExp (w : Fin 3 → ZMod 3) : Fin 4 → ZMod 3
  | 0 => w 0 + w 1 + w 1 + w 2 + w 2
  | 1 => w 1 + w 2
  | 2 => w 2 + w 2
  | 3 => w 2

theorem eExp_add (v w : Fin 3 → ZMod 3) : eExp (v + w) = eExp v + eExp w := by
  funext i
  fin_cases i <;> simp only [eExp, Pi.add_apply] <;> abel

theorem eExp_zero : eExp (0 : Fin 3 → ZMod 3) = 0 := by
  funext i
  fin_cases i <;> simp [eExp]

private theorem eExp_inj : Function.Injective eExp := by
  intro v w hvw
  have h := congrFun hvw
  have h2 : v 2 = w 2 := by
    have hh : v 2 + v 2 = w 2 + w 2 := by simpa [eExp] using h 2
    have h2' : (2 : ZMod 3) * v 2 = 2 * w 2 := by linear_combination hh
    exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h2'
  have h1 : v 1 = w 1 := by
    have hh : v 1 + v 2 = w 1 + w 2 := by simpa [eExp] using h 1
    rw [h2] at hh
    exact add_right_cancel hh
  have h0 : v 0 = w 0 := by
    have hh : v 0 + v 1 + v 1 + v 2 + v 2 = w 0 + w 1 + w 1 + w 2 + w 2 := by
      simpa [eExp] using h 0
    rw [h1, h2] at hh
    linear_combination hh
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

noncomputable abbrev coverDiagE (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) (w : Fin 3 → ZMod 3) : unitarySU 2 n F 6 :=
  coverDiag h hω3 hωnorm hω1 (eExp w)

noncomputable abbrev coverSubgroupE (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) : Subgroup (unitarySU 2 n F 6) where
  carrier := Set.range (coverDiagE h hω3 hωnorm hω1)
  one_mem' := ⟨0, by rw [coverDiagE, eExp_zero, coverDiag_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    refine ⟨v + w, ?_⟩
    rw [coverDiagE, eExp_add, coverDiag_mul, coverDiagE, coverDiagE]
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    have h3v : v + v + v = 0 := by funext i; exact zmod_three (v i)
    have h3 : coverDiagE h hω3 hωnorm hω1 v ^ 3 = 1 := by
      rw [coverDiagE, show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      rw [← coverDiag_mul h hω3 hωnorm hω1 (eExp v) (eExp v)]
      rw [← coverDiag_mul h hω3 hωnorm hω1 (eExp v + eExp v) (eExp v)]
      rw [← eExp_add, ← eExp_add, show v + v + v = 0 from h3v, eExp_zero, coverDiag_zero]
    refine ⟨v + v, ?_⟩
    have hinv : (coverDiagE h hω3 hωnorm hω1 v)⁻¹ =
        coverDiagE h hω3 hωnorm hω1 v * coverDiagE h hω3 hωnorm hω1 v := by
      have h3' : coverDiagE h hω3 hωnorm hω1 v * coverDiagE h hω3 hωnorm hω1 v *
          coverDiagE h hω3 hωnorm hω1 v = 1 := by
        simpa [pow_succ, pow_two, mul_assoc] using h3
      calc (coverDiagE h hω3 hωnorm hω1 v)⁻¹
          = (coverDiagE h hω3 hωnorm hω1 v)⁻¹ * 1 := by rw [mul_one]
        _ = (coverDiagE h hω3 hωnorm hω1 v)⁻¹ *
              (coverDiagE h hω3 hωnorm hω1 v * coverDiagE h hω3 hωnorm hω1 v *
                coverDiagE h hω3 hωnorm hω1 v) := by rw [h3']
        _ = coverDiagE h hω3 hωnorm hω1 v * coverDiagE h hω3 hωnorm hω1 v := by group
    rw [hinv]
    rw [coverDiagE, eExp_add, coverDiag_mul]

theorem coverSubgroupE_card (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    Nat.card (coverSubgroupE h hω3 hωnorm hω1) = 3 ^ 3 := by
  have hinj : Function.Injective (coverDiagE h hω3 hωnorm hω1) := by
    intro v w hvw
    apply eExp_inj
    exact coverDiag_inj h hω3 hωnorm hω1 hvw
  let f : (Fin 3 → ZMod 3) → coverSubgroupE h hω3 hωnorm hω1 :=
    fun v => ⟨coverDiagE h hω3 hωnorm hω1 v, ⟨v, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w hvw => hinj (Subtype.ext_iff.mp hvw), ?_⟩
    rintro ⟨x, v, rfl⟩
    exact ⟨v, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_pi, Nat.card_zmod]


open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.Y10F
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] def wx : Fin 3 → ZMod 3 := fun i => if i = 0 then 1 else 0
@[expose] def wA : Fin 3 → ZMod 3 := fun i => if i = 1 then 1 else 0
@[expose] def wB : Fin 3 → ZMod 3 := fun i => if i = 2 then 1 else 0

theorem eExp_wx : eExp wx = vx := by
  funext i
  fin_cases i <;> simp [eExp, wx, vx] <;> decide

theorem eExp_wA : eExp wA = vA := by
  funext i
  fin_cases i <;> simp [eExp, wA, vA] <;> decide

theorem eExp_wB : eExp wB = vB := by
  funext i
  fin_cases i <;> simp [eExp, wB, vB] <;> decide

theorem coverSubgroupE_le (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    coverSubgroupE h hω3 hωnorm hω1 ≤ coverSubgroup h hω3 hωnorm hω1 := by
  rintro _ ⟨w, rfl⟩
  exact ⟨eExp w, rfl⟩

theorem coverSubgroupE_elem (h : UnitaryFieldData 2 n F) {ω : F} (hω3 : ω ^ 3 = 1)
    (hωnorm : h.norm ω = 1) (hω1 : ω ≠ 1) :
    IsElemAbelian 3 (coverSubgroupE h hω3 hωnorm hω1) := by
  constructor
  · refine ⟨⟨fun A C => ?_⟩⟩
    obtain ⟨v, hv⟩ := A.2
    obtain ⟨w, hw⟩ := C.2
    have hA' : A = ⟨coverDiagE h hω3 hωnorm hω1 v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
    have hC' : C = ⟨coverDiagE h hω3 hωnorm hω1 w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
    rw [hA', hC']
    apply Subtype.ext
    change coverDiag h hω3 hωnorm hω1 (eExp v) * coverDiag h hω3 hωnorm hω1 (eExp w) =
      coverDiag h hω3 hωnorm hω1 (eExp w) * coverDiag h hω3 hωnorm hω1 (eExp v)
    rw [← coverDiag_mul, ← coverDiag_mul, add_comm]
  · intro A hA
    obtain ⟨v, hv⟩ := hA
    have hA' : A = coverDiagE h hω3 hωnorm hω1 v := hv.symm
    rw [hA']
    change coverDiag h hω3 hωnorm hω1 (eExp v) ^ 3 = 1
    have h3v : v + v + v = 0 := by funext i; exact zmod_three (v i)
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
    rw [← coverDiag_mul h hω3 hωnorm hω1 (eExp v) (eExp v)]
    rw [← coverDiag_mul h hω3 hωnorm hω1 (eExp v + eExp v) (eExp v)]
    rw [← eExp_add, ← eExp_add, show v + v + v = 0 from h3v, eExp_zero, coverDiag_zero]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.TwA5Cover
