module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenRefl
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL reflGL_mem
  compInd commute_signMat_iff commute_compInd_iff)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem col_eq_of_mix (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {I : Finset (Fin d)} {D : Matrix (Fin d) (Fin d) K}
    (hfix : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      D * (X : Matrix (Fin d) (Fin d) K) = (X : Matrix (Fin d) (Fin d) K) * D)
    {b x : Fin d} (hb : b ∈ I) (hx : x ∈ I) (hbx : b ≠ x)
    (hDb : ∀ y, y ≠ b → D y b = 0 ∧ D b y = 0)
    {l m : K} (hl : l ≠ 0) (hm : m ≠ 0) (hcirc : w b * l ^ 2 + w x * m ^ 2 = w b) :
    (∀ y, y ≠ x → D y x = 0) ∧ D x x = D b b := by
  set eb : Fin d → K := Pi.single b 1 with heb
  set ex : Fin d → K := Pi.single x 1 with hex
  set u : Fin d → K := l • eb + m • ex with hu
  have hbilb : ∀ y, bil w eb y = w b * y b := by
    intro y
    rw [bil_eq_sum, Finset.sum_eq_single b (fun i _ hi => by simp [heb, hi]) (by simp)]
    simp [heb]
  have hbilx : ∀ y, bil w ex y = w x * y x := by
    intro y
    rw [bil_eq_sum, Finset.sum_eq_single x (fun i _ hi => by simp [hex, hi]) (by simp)]
    simp [hex]
  have hub : u b = l := by simp [hu, heb, hex, hbx]
  have hux : u x = m := by simp [hu, heb, hex, Ne.symm hbx]
  have hbilu : ∀ y, bil w u y = l * (w b * y b) + m * (w x * y x) := by
    intro y
    have e : bil w u y = l * bil w eb y + m * bil w ex y := by
      simp only [bil, hu, add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [e, hbilb, hbilx]
  have hQu : bil w u u = w b := by
    rw [hbilu, hub, hux]
    linear_combination hcirc
  have hQeb : bil w eb eb = w b := by rw [hbilb]; simp [heb]
  have hl1 : l ≠ 1 := by
    rintro rfl
    have : w x * m ^ 2 = 0 := by linear_combination hcirc
    exact pow_ne_zero 2 hm ((mul_eq_zero.1 this).resolve_left (hw x))
  have hQv : bil w (eb - u) (eb - u) ≠ 0 := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right, hQeb, hQu, hbilb, bil_comm w u eb,
      hbilb, hub]
    have e : w b - w b * l - (w b * l - w b) = 2 * w b * (1 - l) := by ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero h2 (hw b)) (sub_ne_zero.2 (Ne.symm hl1))
  have hvI : ∀ i, i ∉ I → (eb - u) i = 0 := by
    intro i hi
    have hib : i ≠ b := fun h => hi (h ▸ hb)
    have hix : i ≠ x := fun h => hi (h ▸ hx)
    simp [hu, heb, hex, hib, hix]
  set rv := reflGLv w hQv with hrv
  have hrvI : rv ∈ oIsoBlock K hw I := reflGLv_mem_oIsoBlock hw hQv hvI
  have hrbI : reflGL (K := K) b ∈ oIsoBlock K hw I := reflGL_mem_oIsoBlock hw hb
  have hC := hfix _ (commutator_mem_commutator hrbI hrvI)
  have hDrb : D * signMat K {b} = signMat K {b} * D := by
    refine ((commute_signMat_iff h2 {b} D).2 ((commute_compInd_iff {b} D).2 ?_)).symm
    intro i j hij
    by_cases hi : i = b
    · subst hi
      have hj : j ≠ i := fun h => (hij.1 (Finset.mem_singleton_self i)) (h ▸
        Finset.mem_singleton_self i)
      exact (hDb j hj).2
    · have hj : j = b := by
        by_contra hj
        exact hi (Finset.mem_singleton.1 (hij.2 fun h => hj (Finset.mem_singleton.1 h)))
      subst hj
      exact (hDb i hi).1
  have hrb : ((reflGL (K := K) b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = signMat K {b} :=
    rfl
  have hrbm : signMat K {b} * signMat K {b} = 1 := by
    rw [← hrb, ← Units.val_mul]
    exact congrArg Units.val (mul_eq_one_iff_eq_inv.2 (inv_eq_of_mul_eq_one_right
      (Units.ext (PSL.signMat_mul_self {b}))).symm)
  have hcomm_u : D * reflM w u = reflM w u * D := by
    have hconj : reflM w u = reflM w (eb - u) * signMat K {b} * reflM w (eb - u) := by
      have e := conj_reflM w eb (g := rv) (by
        rw [hrv, coe_reflGLv]; exact reflM_isometry w hQv)
      rw [hrv, coe_reflGLv, reflGLv_inv, coe_reflGLv, reflM_single w (hw b),
        reflM_sub_mulVec h2 w (hQeb.trans hQu.symm) hQv] at e
      exact e.symm
    have e1 : (((⁅reflGL (K := K) b, rv⁆ : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
        signMat K {b} * reflM w u := by
      rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hrb, hrv,
        coe_reflGLv, reflGLv_inv, coe_reflGLv, hconj]
      have hrbi : (((reflGL (K := K) b)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          signMat K {b} := by
        rw [inv_eq_of_mul_eq_one_right (Units.ext (PSL.signMat_mul_self {b}) :
          reflGL (K := K) b * reflGL b = 1)]
        rfl
      rw [hrbi]
      simp only [Matrix.mul_assoc]
    rw [e1] at hC
    have e2 : signMat K {b} * (D * reflM w u) = signMat K {b} * (reflM w u * D) := by
      rw [← Matrix.mul_assoc, ← hDrb, Matrix.mul_assoc, hC, Matrix.mul_assoc]
    have e3 := congrArg (fun M => signMat K {b} * M) e2
    simp only [← Matrix.mul_assoc, hrbm, Matrix.one_mul] at e3
    exact e3
  obtain ⟨κ, hκ⟩ := exists_smul_of_commute_reflM h2 w (hQu.symm ▸ hw b) hcomm_u
  have hDu : ∀ i, (D *ᵥ u) i = l * D i b + m * D i x := by
    intro i
    rw [hu, mulVec_add, mulVec_smul, mulVec_smul, heb, hex, mulVec_single_one,
      mulVec_single_one]
    simp only [Pi.add_apply, Pi.smul_apply, col_apply, smul_eq_mul]
  have hκb : κ = D b b := by
    have e := congrFun hκ b
    rw [hDu, (hDb x hbx.symm).2, Pi.smul_apply, hub, smul_eq_mul, mul_zero, add_zero] at e
    have : l * (D b b - κ) = 0 := by linear_combination e
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hl)).symm
  have hcol : ∀ y, y ≠ b → D y x = κ * ex y := by
    intro y hyb
    have e := congrFun hκ y
    have huy : u y = m * ex y := by simp [hu, heb, hex, hyb]
    rw [hDu, (hDb y hyb).1, mul_zero, zero_add, Pi.smul_apply, smul_eq_mul, huy] at e
    have : m * (D y x - κ * ex y) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hm)
  refine ⟨fun y hyx => ?_, ?_⟩
  · by_cases hyb : y = b
    · subst hyb
      exact (hDb x hbx.symm).2
    · rw [hcol y hyb, hex]
      simp [hyx]
  · rw [hcol x (Ne.symm hbx), hex, Pi.single_eq_same, mul_one, hκb]

theorem exists_mix [Finite K] (h2 : (2 : K) ≠ 0) (hK5 : 5 ≤ Nat.card K) {c : K}
    (hc : ¬ IsSquare c) : ∃ l m : K, l ≠ 0 ∧ m ≠ 0 ∧ l ^ 2 + c * m ^ 2 = 1 := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨t, ht0, ht⟩ : ∃ t : K, t ≠ 0 ∧ 1 + c * t ^ 2 ≠ 0 := by
    by_cases h1 : 1 + c * 1 ^ 2 = 0
    ·
      classical
      have hc1 : c = -1 := by linear_combination h1
      have : Fintype K := Fintype.ofFinite K
      have hlt : ({0, 1, -1} : Finset K).card < (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        calc ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
          _ < Nat.card K := by omega
      obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      refine ⟨t, ht.1, ?_⟩
      rw [hc1]
      intro h0
      have : (t - 1) * (t + 1) = 0 := by linear_combination -h0
      rcases mul_eq_zero.1 this with h | h
      · exact ht.2.1 (sub_eq_zero.1 h)
      · exact ht.2.2 (eq_neg_of_add_eq_zero_left h)
    · exact ⟨1, one_ne_zero, h1⟩
  refine ⟨(1 - c * t ^ 2) / (1 + c * t ^ 2), 2 * t / (1 + c * t ^ 2), ?_, ?_, ?_⟩
  · refine div_ne_zero ?_ ht
    intro h0
    apply hc
    refine ⟨t⁻¹, ?_⟩
    have : c * t ^ 2 = 1 := by linear_combination -h0
    field_simp
    linear_combination this
  · exact div_ne_zero (mul_ne_zero h2 ht0) ht
  · field_simp
    ring

end CFSG.ComponentClassification.Burgoyne.O
