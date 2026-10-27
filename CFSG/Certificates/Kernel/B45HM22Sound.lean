module

public import Certificates.Data.Kernel.B45HM22.Nor
public import CFSG.Certificates.Kernel.B45M12Sound
import all CFSG.Certificates.Kernel.B45M12Sound

public section

namespace CFSG.KC.B45HM22

open CFSG.KC.B45M12 CFSG.Quasithin.HM22 CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.B45Mat (genT untab_mulT vecMulT_spec)
open scoped Matrix

theorem boolProg_progC (p : List (ℕ × Bool)) :
    CFSG.Quasithin.B45Mat.M12.boolProg (progC p) = p := by
  rw [CFSG.Quasithin.B45Mat.M12.boolProg, progC, List.map_map]
  conv_rhs => rw [← List.map_id p]
  refine List.map_congr_left fun e _ => ?_
  obtain ⟨a, b⟩ := e
  cases b <;> rfl

theorem termsC_decode (t : List (List Bool × FieldFour)) :
    ((termsC t).map fun p => (CFSG.Quasithin.B45Mat.M12.boolWord p.1,
      CFSG.Quasithin.B45Mat.M12.ofCode4 p.2)) = t := by
  rw [termsC, List.map_map]
  conv_rhs => rw [← List.map_id t]
  refine List.map_congr_left fun e _ => ?_
  obtain ⟨w, ⟨re, im⟩⟩ := e
  have hw : CFSG.Quasithin.B45Mat.M12.boolWord (w.map (Bool.rec 1 2)) = w := by
    rw [CFSG.Quasithin.B45Mat.M12.boolWord, List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left fun b _ => by cases b <;> rfl
  change (CFSG.Quasithin.B45Mat.M12.boolWord (w.map (Bool.rec 1 2)),
    CFSG.Quasithin.B45Mat.M12.ofCode4 (Bool.toNat re + 2 * Bool.toNat im)) = (w, ⟨re, im⟩)
  rw [hw]
  cases re <;> cases im <;> rfl

theorem untab_unpack_pairMat (n : ℕ) (M : PM) :
    untab (PM.unpack n n M) = pairMat n n M := by
  rw [PM.untab_unpack]
  rfl

theorem norP_sound {n : ℕ} [NeZero n] {d : PSpin} {A B : PM} (h : norP n d A B = true) :
    (d.toSpin n).check (PM.unpack n n A) (PM.unpack n n B) = true := by
  simp only [norP, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hGa, hGb⟩, -⟩, hQil⟩, -⟩, hSil⟩, -⟩, hsp⟩, hdu⟩, hQQi⟩, hR⟩, hS⟩, hz₁⟩,
    hz₂⟩, hT⟩ := h
  have ha := untab_unpack_pairMat n A
  have hb := untab_unpack_pairMat n B
  have hact : ∀ z x, pvec n (actF4 (genF4 A B z) x) =
      untab (genT (PM.unpack n n A) (PM.unpack n n B) (z == 2)) *ᵥ pvec n x := by
    intro z x
    rw [genF4_eq, genT]
    split_ifs
    · rw [pvec_actF4_mulVec _ hGb, hb]
    · rw [pvec_actF4_mulVec _ hGa, ha]
  have hactT : ∀ z x, pvec n (actF4 (genF4 (trF4 n A) (trF4 n B) z) x) =
      (untab (genT (PM.unpack n n A) (PM.unpack n n B) (z == 2)))ᵀ *ᵥ pvec n x := by
    intro z x
    rw [genF4_eq, genT]
    split_ifs
    · rw [pvec_actF4_mulVec _ (le_of_eq (length_trF4 n B)), pairMat_trF4, hb]
    · rw [pvec_actF4_mulVec _ (le_of_eq (length_trF4 n A)), pairMat_trF4, ha]
  have hsum := pvec_sumTF4 (Ma := PM.unpack n n A) (Mb := PM.unpack n n B)
    (dec_foldl_word (pvec n) (fun z x => actF4 (genF4 (trF4 n A) (trF4 n B) z) x)
      (PM.unpack n n A) (PM.unpack n n B) hactT) (termsC d.terms)
  rw [termsC_decode] at hsum
  have hwv : pvec n d.w = fun i => (Vector.ofFn fun i : Fin n => d.w.get i)[i] := by
    funext i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rfl
  simp only [CFSG.Quasithin.B45Mat.SpinData.check, PSpin.toSpin, Bool.and_eq_true]
  refine ⟨⟨⟨⟨decide_eq_true ?_, decide_eq_true ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩,
    decide_eq_true ?_⟩
  · have e := pairMat_mulF4 (m := n) (n := n) d.Qi d.Q hQil
    rw [pairMat_eq_of_eqF4 hQQi, pairMat_idF4] at e
    rw [untab_mulT, untab_unpack_pairMat, untab_unpack_pairMat]
    exact e.symm
  · have hf := fun x : ℕ × ℕ =>
      (pvec_actF4_mulVec (trF4 n d.Q) (le_of_eq (length_trF4 n _))
        (sumTF4 (trF4 n A) (trF4 n B) (termsC d.terms) x)).trans
        ((congrArg (pairMat n n (trF4 n d.Q) *ᵥ ·) (hsum x)).trans (Matrix.mulVec_mulVec _ _ _))
    have e := pairMat_map (n := n) hf (trF4 n d.R)
    rw [pairMat_eq_of_eqF4 hR, pairMat_diag0F4, pairMat_trF4, pairMat_trF4] at e
    have e' := congrArg Matrix.transpose e
    simp only [Matrix.diagonal_transpose, Matrix.transpose_mul, Matrix.transpose_transpose] at e'
    rw [← Matrix.mul_assoc] at e'
    rw [untab_mulT, untab_mulT, untab_unpack_pairMat, untab_unpack_pairMat]
    exact e'.symm
  · have hu : pvec n (d.Q.headD (0, 0)) =
        fun i => (Vector.ofFn fun l : Fin n => (PM.unpack n n d.Q)[l][(0 : Fin n)])[i] := by
      funext i
      simp only [pvec, Fin.getElem_fin, Vector.getElem_ofFn, PM.unpack]
      generalize d.Q = Q
      cases Q <;> rfl
    obtain ⟨-, hSM⟩ := pairMat_spinF4M (prog := progC d.spin) hact hu
      (by rw [progC, List.length_map]; exact hsp)
    have e := pairMat_mulF4 (m := n) (n := n) d.Si
      (spinF4M A B (d.Q.headD (0, 0)) (progC d.spin)) hSil
    rw [pairMat_eq_of_eqF4 hS, pairMat_idF4, hSM, boolProg_progC] at e
    rw [untab_mulT, untab_unpack_pairMat]
    exact e.symm
  · intro j
    have hbz : pvec n (sumTF4 (trF4 n A) (trF4 n B) (termsC d.terms) d.w) = 0 := by
      funext i
      have h1 := congrArg (fun x => x.testBit i) hz₁
      have h2 := congrArg (fun x => x.testBit i) hz₂
      simp only [Nat.testBit_mod_two_pow, i.2, decide_true, Bool.true_and,
        Nat.zero_testBit] at h1 h2
      simp only [pvec, pent, h1, h2]
      rfl
    refine (congrFun (vecMulT_spec _ _) j).trans ?_
    rw [← hwv, ← Matrix.mulVec_transpose]
    exact congrFun ((hsum d.w).symm.trans hbz) j
  · obtain ⟨hUl, hUM⟩ := pairMat_spinF4M_dual (prog := progC d.dual) hactT hwv
      (by rw [progC, List.length_map]; exact hdu)
    have e := pairMat_mulF4 (m := n) (n := n) _ (trF4 n d.Ti) (le_of_eq hUl)
    rw [pairMat_eq_of_eqF4 hT, pairMat_idF4, hUM, pairMat_trF4, boolProg_progC] at e
    have e' := congrArg Matrix.transpose e
    simp only [Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose] at e'
    rw [untab_mulT, untab_unpack_pairMat]
    exact e'.symm

theorem nortonOK_of_norP {n : ℕ} [NeZero n] {d : PSpin} {A B : PM}
    (hp : (A.length == n && B.length == n && PM.eqm n (PM.mul A A) (PM.idm n) &&
      PM.eqm n (PM.mul B (PM.mul B (PM.mul B B))) (PM.idm n)) = true)
    (h : norP n d A B = true) : nortonOK n A B d = true := by
  rw [nortonOK, hp, norP_sound h]
  rfl

end CFSG.KC.B45HM22

end
