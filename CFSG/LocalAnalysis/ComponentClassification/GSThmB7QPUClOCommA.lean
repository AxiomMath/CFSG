module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenRefl
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL
  commute_signMat_iff commute_compInd_iff)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem exists_sq_add_sq_eq [Finite K] (hK : ringChar K ≠ 2) (c : K) :
    ∃ y z : K, y ^ 2 + z ^ 2 = c := by
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by norm_num) c) hodd
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
    at hab
  exact ⟨a, b, by linear_combination hab⟩

theorem bil_single_single (w : Fin d → K) (i j : Fin d) :
    bil w (Pi.single i 1) (Pi.single j 1) = if i = j then w i else 0 := by
  rw [bil_eq_sum, Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · intro k _ hk
    simp [hk]
  · simp

theorem bil_single_self (w : Fin d → K) (i : Fin d) :
    bil w (Pi.single i 1) (Pi.single i 1) = w i := by
  rw [bil_single_single, ite_eq_left rfl]

theorem bil_single_ne (w : Fin d → K) {i j : Fin d} (h : i ≠ j) :
    bil w (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [bil_single_single, ite_eq_right h]

theorem bil_add_left (w : Fin d → K) (v v' y : Fin d → K) :
    bil w (v + v') y = bil w v y + bil w v' y := by
  rw [bil, add_dotProduct]

theorem bil_add_right (w : Fin d → K) (v y y' : Fin d → K) :
    bil w v (y + y') = bil w v y + bil w v y' := by
  rw [bil, mulVec_add, dotProduct_add]

theorem coe_comm_reflGL (h2 : (2 : K) ≠ 0) {w : Fin d → K} {b : Fin d} (hwb : w b ≠ 0)
    {u : Fin d → K} (hQu : bil w u u = w b)
    (hv : bil w (Pi.single b 1 - u) (Pi.single b 1 - u) ≠ 0) :
    ((⁅reflGL (K := K) b, reflGLv w hv⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      signMat K {b} * reflM w u := by
  have hconj : reflM w u = reflM w (Pi.single b 1 - u) * signMat K {b} *
      reflM w (Pi.single b 1 - u) := by
    have e := conj_reflM w (Pi.single b 1) (g := reflGLv w hv) (by
      rw [coe_reflGLv]; exact reflM_isometry w hv)
    rw [coe_reflGLv, reflGLv_inv, coe_reflGLv, reflM_single w hwb,
      reflM_sub_mulVec h2 w ((bil_single_self w b).trans hQu.symm) hv] at e
    exact e.symm
  have hrbi : (((reflGL (K := K) b)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      signMat K {b} := by
    rw [inv_eq_of_mul_eq_one_right (Units.ext (Burgoyne.PSL.signMat_mul_self {b}) :
      reflGL (K := K) b * reflGL b = 1)]
    rfl
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hrbi, reflGLv_inv,
    coe_reflGLv, hconj]
  change signMat K {b} * reflM w (Pi.single b 1 - u) * signMat K {b} *
    reflM w (Pi.single b 1 - u) = _
  simp only [Matrix.mul_assoc]

theorem signMat_mul_reflM_apply (w : Fin d → K) (b : Fin d) (u : Fin d → K) :
    (signMat K {b} * reflM w u) b b = 2 / bil w u u * (u b * (w b * u b)) - 1 := by
  rw [signMat, diagonal_mul, reflM, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    one_apply_eq, smul_eq_mul, ite_eq_left (Finset.mem_singleton_self b)]
  ring

theorem comm_reflM_three_mulVec (h2 : (2 : K) ≠ 0) {w : Fin d → K} {a b c : Fin d}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hwab : w a = w b) (hwbc : w b = w c)
    (hu : bil w (Pi.single a 1 - Pi.single b 1) (Pi.single a 1 - Pi.single b 1) ≠ 0)
    (hv : bil w (Pi.single b 1 - Pi.single c 1) (Pi.single b 1 - Pi.single c 1) ≠ 0) :
    ((⁅reflGLv w hu, reflGLv w hv⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
      Pi.single a 1 = Pi.single c 1 := by
  have hfix : ∀ {x y z : Fin d}, z ≠ x → z ≠ y →
      reflM w (Pi.single x 1 - Pi.single y 1) *ᵥ Pi.single z 1 = Pi.single z 1 := by
    intro x y z hzx hzy
    rw [reflM_mulVec, bil_sub_left w (Pi.single x 1) (Pi.single y 1) (Pi.single z 1),
      bil_single_ne w (Ne.symm hzx), bil_single_ne w (Ne.symm hzy)]
    simp
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, reflGLv_inv,
    reflGLv_inv, coe_reflGLv, coe_reflGLv, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    hfix hab hac,
    reflM_sub_mulVec h2 w (by rw [bil_single_self, bil_single_self, hwab]) hu,
    reflM_sub_mulVec h2 w (by rw [bil_single_self, bil_single_self, hwbc]) hv,
    hfix (Ne.symm hac) (Ne.symm hbc)]

theorem exists_mem_ne_ne {s : Finset (Fin d)} (hs : 3 ≤ s.card) (a i : Fin d) :
    ∃ b ∈ s, b ≠ a ∧ b ≠ i := by
  have hc : 0 < ((s.erase a).erase i).card := by
    have h1 := Finset.pred_card_le_card_erase (s := s) (a := a)
    have h2 := Finset.pred_card_le_card_erase (s := s.erase a) (a := i)
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hc
  simp only [Finset.mem_erase] at hb
  exact ⟨b, hb.2.2, hb.2.1, hb.1⟩

theorem commute_signMat_single_of_isolated (h2 : (2 : K) ≠ 0) {D : Matrix (Fin d) (Fin d) K}
    {b : Fin d} (hDb : ∀ y, y ≠ b → D y b = 0 ∧ D b y = 0) :
    D * signMat K {b} = signMat K {b} * D := by
  refine ((commute_signMat_iff h2 {b} D).2 ((commute_compInd_iff {b} D).2 ?_)).symm
  intro i j hij
  simp only [Finset.mem_singleton] at hij
  by_cases hi : i = b
  · have hj : j ≠ b := hij.1 hi
    rw [hi]
    exact (hDb j hj).2
  · have hj : j = b := by
      by_contra hj
      exact hi (hij.2 hj)
    rw [hj]
    exact (hDb i hi).1

theorem mulVec_single_of_isolated {D : Matrix (Fin d) (Fin d) K} {i : Fin d}
    (hDi : ∀ y, y ≠ i → D y i = 0) : D *ᵥ Pi.single i 1 = D i i • Pi.single i 1 := by
  funext y
  rw [mulVec_single_one, col_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y = i
  · subst hy
    simp
  · rw [hDi y hy, Pi.single_eq_of_ne hy, mul_zero]

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem commute_reflM_of_mix (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} {D : Matrix (Fin d) (Fin d) K}
    (hD : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      D * (X : Matrix (Fin d) (Fin d) K) = (X : Matrix (Fin d) (Fin d) K) * D)
    {b : Fin d} (hb : b ∈ I) (hDb : D * signMat K {b} = signMat K {b} * D) {u : Fin d → K}
    (huI : ∀ i, i ∉ I → u i = 0) (hQu : bil w u u = w b)
    (hv : bil w (Pi.single b 1 - u) (Pi.single b 1 - u) ≠ 0) :
    D * reflM w u = reflM w u * D := by
  have hvI : ∀ i, i ∉ I → (Pi.single b 1 - u : Fin d → K) i = 0 := by
    intro i hi
    have hib : i ≠ b := fun h => hi (h ▸ hb)
    rw [Pi.sub_apply, Pi.single_eq_of_ne hib, huI i hi, sub_zero]
  have hX := hD _ (commutator_mem_commutator (reflGL_mem_oIsoBlock hw hb)
    (reflGLv_mem_oIsoBlock hw hv hvI))
  rw [coe_comm_reflGL h2 (hw b) hQu hv] at hX
  have hss : signMat K {b} * signMat K {b} = 1 := Burgoyne.PSL.signMat_mul_self {b}
  have e2 : signMat K {b} * (D * reflM w u) = signMat K {b} * (reflM w u * D) := by
    rw [← Matrix.mul_assoc, ← hDb, Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have e3 := congrArg (fun M => signMat K {b} * M) e2
  simp only [← Matrix.mul_assoc, hss, Matrix.one_mul] at e3
  exact e3

end CFSG.ComponentClassification.GSThmB.QPUCl
