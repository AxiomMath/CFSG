module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

noncomputable section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.Orthogonal

section Model

variable (F : Type) [Field F]

private abbrev kdQ : QuadraticForm F (Fin 4 ⊕ Fin 4 → F) :=
  CFSG.LieType.Universal.Spin.quadPlus 4 F

private def kdEv (i : Fin 4) : Fin 4 ⊕ Fin 4 → F := Pi.single (Sum.inl i) 1

private def kdFv (i : Fin 4) : Fin 4 ⊕ Fin 4 → F := Pi.single (Sum.inr i) 1

private def kdW1 (a b : F) : Fin 4 ⊕ Fin 4 → F := a • kdEv F 1 + b • kdFv F 1

private def kdW3 (c d : F) : Fin 4 ⊕ Fin 4 → F := c • kdEv F 3 + d • kdFv F 3

private def kdSign (k : Fin 4 ⊕ Fin 4) : F :=
  if k = .inl 0 ∨ k = .inl 1 ∨ k = .inr 0 ∨ k = .inr 1 then -1 else 1

private theorem kdSign_mul_self (k : Fin 4 ⊕ Fin 4) : kdSign F k * kdSign F k = 1 := by
  unfold kdSign
  split_ifs <;> norm_num

private theorem kdQ_polar (v w : Fin 4 ⊕ Fin 4 → F) :
    QuadraticMap.polar (kdQ F) v w =
      v (.inl 0) * w (.inr 0) + w (.inl 0) * v (.inr 0) +
      (v (.inl 1) * w (.inr 1) + w (.inl 1) * v (.inr 1)) +
      (v (.inl 2) * w (.inr 2) + w (.inl 2) * v (.inr 2)) +
      (v (.inl 3) * w (.inr 3) + w (.inl 3) * v (.inr 3)) := by
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus, Fin.sum_univ_four]

private theorem kdQ_apply (v : Fin 4 ⊕ Fin 4 → F) :
    kdQ F v = v (.inl 0) * v (.inr 0) + v (.inl 1) * v (.inr 1) +
      v (.inl 2) * v (.inr 2) + v (.inl 3) * v (.inr 3) := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply, Fin.sum_univ_four]

private theorem kdQ_ev0 : kdQ F (kdEv F 0) = 0 := by
  simp [kdQ_apply, kdEv, Pi.single_apply]

private theorem kdQ_ev1 : kdQ F (kdEv F 1) = 0 := by
  simp [kdQ_apply, kdEv, Pi.single_apply]

private theorem kdQ_ev2 : kdQ F (kdEv F 2) = 0 := by
  simp [kdQ_apply, kdEv, Pi.single_apply]

private theorem kdQ_fv0 : kdQ F (kdFv F 0) = 0 := by
  simp [kdQ_apply, kdFv, Pi.single_apply]

private theorem kdQ_w1 (a b : F) : kdQ F (kdW1 F a b) = a * b := by
  simp [kdQ_apply, kdW1, kdEv, kdFv, Pi.single_apply]

private theorem kdQ_w3 (c d : F) : kdQ F (kdW3 F c d) = c * d := by
  simp [kdQ_apply, kdW3, kdEv, kdFv, Pi.single_apply]

private theorem kdQ_neg_fv1 : kdQ F (-kdFv F 1) = 0 := by
  simp [kdQ_apply, kdFv, Pi.single_apply]

private theorem kdpol_ev0_w1 (a b : F) :
    QuadraticMap.polar (kdQ F) (kdEv F 0) (kdW1 F a b) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW1, Pi.single_apply]

private theorem kdpol_ev2_w3 (c d : F) :
    QuadraticMap.polar (kdQ F) (kdEv F 2) (kdW3 F c d) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW3, Pi.single_apply]

private theorem kdpol_ev2_ev0 : QuadraticMap.polar (kdQ F) (kdEv F 2) (kdEv F 0) = 0 := by
  simp [kdQ_polar, kdEv, Pi.single_apply]

private theorem kdpol_ev2_w1 (a b : F) :
    QuadraticMap.polar (kdQ F) (kdEv F 2) (kdW1 F a b) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW1, Pi.single_apply]

private theorem kdpol_w3_ev0 (c d : F) :
    QuadraticMap.polar (kdQ F) (kdW3 F c d) (kdEv F 0) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW3, Pi.single_apply]

private theorem kdpol_w3_w1 (a b c d : F) :
    QuadraticMap.polar (kdQ F) (kdW3 F c d) (kdW1 F a b) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW1, kdW3, Pi.single_apply]

private theorem kdpol_fv0_ev0 : QuadraticMap.polar (kdQ F) (kdFv F 0) (kdEv F 0) = 1 := by
  simp [kdQ_polar, kdEv, kdFv, Pi.single_apply]

private theorem kdpol_fv0_w1 (a b : F) :
    QuadraticMap.polar (kdQ F) (kdFv F 0) (kdW1 F a b) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW1, Pi.single_apply]

private theorem kdpol_fv0_ev2 : QuadraticMap.polar (kdQ F) (kdFv F 0) (kdEv F 2) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, Pi.single_apply]

private theorem kdpol_fv0_w3 (c d : F) :
    QuadraticMap.polar (kdQ F) (kdFv F 0) (kdW3 F c d) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW3, Pi.single_apply]

private theorem kdpol_fv2_ev2 : QuadraticMap.polar (kdQ F) (kdFv F 2) (kdEv F 2) = 1 := by
  simp [kdQ_polar, kdEv, kdFv, Pi.single_apply]

private theorem kdpol_fv2_ev0 : QuadraticMap.polar (kdQ F) (kdFv F 2) (kdEv F 0) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, Pi.single_apply]

private theorem kdpol_fv2_w1 (a b : F) :
    QuadraticMap.polar (kdQ F) (kdFv F 2) (kdW1 F a b) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW1, Pi.single_apply]

private theorem kdpol_fv2_w3 (c d : F) :
    QuadraticMap.polar (kdQ F) (kdFv F 2) (kdW3 F c d) = 0 := by
  simp [kdQ_polar, kdEv, kdFv, kdW3, Pi.single_apply]

private theorem kdpol_ev0_ev1 : QuadraticMap.polar (kdQ F) (kdEv F 0) (kdEv F 1) = 0 := by
  simp [kdQ_polar, kdEv, Pi.single_apply]

private theorem kdpol_fv0_mfv1 :
    QuadraticMap.polar (kdQ F) (kdFv F 0) (-kdFv F 1) = 0 := by
  simp [kdQ_polar, kdFv, Pi.single_apply]

private theorem kdpol_v_ev0 (v : Fin 4 ⊕ Fin 4 → F) :
    QuadraticMap.polar (kdQ F) v (kdEv F 0) = v (.inr 0) := by
  simp [kdQ_polar, kdEv, Pi.single_apply]

private theorem kdpol_v_ev1 (v : Fin 4 ⊕ Fin 4 → F) :
    QuadraticMap.polar (kdQ F) v (kdEv F 1) = v (.inr 1) := by
  simp [kdQ_polar, kdEv, Pi.single_apply]

private theorem kdpol_v_fv0 (v : Fin 4 ⊕ Fin 4 → F) :
    QuadraticMap.polar (kdQ F) v (kdFv F 0) = v (.inl 0) := by
  simp [kdQ_polar, kdFv, Pi.single_apply]

private theorem kdpol_v_mfv1 (v : Fin 4 ⊕ Fin 4 → F) :
    QuadraticMap.polar (kdQ F) v (-kdFv F 1) = -v (.inl 1) := by
  simp [kdQ_polar, kdFv, Pi.single_apply]

private theorem kd_eichler_comm {u w u' w' : Fin 4 ⊕ Fin 4 → F}
    (h1 : QuadraticMap.polar (kdQ F) u u' = 0) (h2 : QuadraticMap.polar (kdQ F) u w' = 0)
    (h3 : QuadraticMap.polar (kdQ F) w u' = 0) (h4 : QuadraticMap.polar (kdQ F) w w' = 0) :
    eichler (kdQ F) u w * eichler (kdQ F) u' w' =
      eichler (kdQ F) u' w' * eichler (kdQ F) u w := by
  have hg := eichler_mem_orthogonalGroup (kdQ F) u' w'
  have hu := eichler_apply_of_polar_eq_zero (u := u') (w := w') h1 h2
  have hw := eichler_apply_of_polar_eq_zero (u := u') (w := w') h3 h4
  have key := eichler_conj hg u w
  rw [hu, hw] at key
  exact (mul_inv_eq_iff_eq_mul.1 key).symm

private def kdE1 (a b : F) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  eichler (kdQ F) (kdEv F 0) (kdW1 F a b)

private def kdE3 (c d : F) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  eichler (kdQ F) (kdEv F 2) (kdW3 F c d)

private theorem kdE1_mul (a b a' b' : F) :
    kdE1 F a b * kdE1 F a' b' = kdE1 F (a + a') (b + b') := by
  unfold kdE1
  rw [eichler_mul (kdpol_ev0_w1 F a b) (kdpol_ev0_w1 F a' b')]
  congr 1
  unfold kdW1
  module

private theorem kdE3_mul (c d c' d' : F) :
    kdE3 F c d * kdE3 F c' d' = kdE3 F (c + c') (d + d') := by
  unfold kdE3
  rw [eichler_mul (kdpol_ev2_w3 F c d) (kdpol_ev2_w3 F c' d')]
  congr 1
  unfold kdW3
  module

private theorem kdE3_E1_comm (c d a b : F) :
    kdE3 F c d * kdE1 F a b = kdE1 F a b * kdE3 F c d := by
  unfold kdE1 kdE3
  exact kd_eichler_comm F (u := kdEv F 2) (w := kdW3 F c d) (u' := kdEv F 0)
    (w' := kdW1 F a b) (kdpol_ev2_ev0 F) (kdpol_ev2_w1 F a b) (kdpol_w3_ev0 F c d)
    (kdpol_w3_w1 F a b c d)

private def kdG4 (x : F × F × F × F) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  kdE1 F x.1 x.2.1 * kdE3 F x.2.2.1 x.2.2.2

private theorem kdG4_zero : kdG4 F 0 = 1 := by
  simp [kdG4, kdE1, kdE3, kdW1, kdW3, eichler_zero_right]

private theorem kdG4_add (x y : F × F × F × F) : kdG4 F (x + y) = kdG4 F x * kdG4 F y := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp only [kdG4, Prod.mk_add_mk]
  rw [← kdE1_mul, ← kdE3_mul]
  exact (Commute.mul_mul_mul_comm (kdE3_E1_comm F c d a' b') _ _).symm

private theorem kdG4_mem (x : F × F × F × F) : kdG4 F x ∈ elementaryGroup (kdQ F) := by
  unfold kdG4 kdE1 kdE3
  exact Subgroup.mul_mem _ (eichler_mem_elementaryGroup (kdQ F) _ _)
    (eichler_mem_elementaryGroup (kdQ F) _ _)

private theorem kdG4_fv0 (a b c d : F) :
    kdG4 F (a, b, c, d) (kdFv F 0) = kdFv F 0 + kdW1 F a b - (a * b) • kdEv F 0 := by
  simp only [kdG4, kdE1, kdE3, LinearEquiv.mul_apply]
  rw [eichler_apply_of_polar_eq_zero (kdpol_fv0_ev2 F) (kdpol_fv0_w3 F c d)]
  rw [eichler_apply (kdQ_ev0 F) (kdpol_ev0_w1 F a b) (kdFv F 0), kdpol_fv0_ev0 F,
    kdpol_fv0_w1 F a b, kdQ_w1 F a b]
  simp

private theorem kdE3_fv2 (c d : F) :
    kdE3 F c d (kdFv F 2) = kdFv F 2 + kdW3 F c d - (c * d) • kdEv F 2 := by
  unfold kdE3
  rw [eichler_apply (kdQ_ev2 F) (kdpol_ev2_w3 F c d) (kdFv F 2), kdpol_fv2_ev2 F,
    kdpol_fv2_w3 F c d, kdQ_w3 F c d]
  simp

private theorem kdG4_fv2 (a b c d : F) :
    kdG4 F (a, b, c, d) (kdFv F 2) = kdFv F 2 + kdW3 F c d - (c * d) • kdEv F 2 := by
  have hfix1 : kdE1 F a b (kdFv F 2) = kdFv F 2 :=
    eichler_apply_of_polar_eq_zero (kdpol_fv2_ev0 F) (kdpol_fv2_w1 F a b)
  have hfix2 : kdE1 F a b (kdW3 F c d) = kdW3 F c d :=
    eichler_apply_of_polar_eq_zero (kdpol_w3_ev0 F c d) (kdpol_w3_w1 F a b c d)
  have hfix3 : kdE1 F a b (kdEv F 2) = kdEv F 2 :=
    eichler_apply_of_polar_eq_zero (kdpol_ev2_ev0 F) (kdpol_ev2_w1 F a b)
  simp only [kdG4, LinearEquiv.mul_apply]
  rw [kdE3_fv2, map_sub, map_add, map_smul, hfix1, hfix2, hfix3]

private theorem kdG4_eq_zero_of_scalar (x : F × F × F × F)
    (hx : ∃ c : F, ∀ v, kdG4 F x v = c • v) : x = 0 := by
  obtain ⟨c0, hc⟩ := hx
  obtain ⟨a, b, c, d⟩ := x
  have h0 := hc (kdFv F 0)
  have h2 := hc (kdFv F 2)
  rw [kdG4_fv0] at h0
  rw [kdG4_fv2] at h2
  have e2 := congrFun h0 (.inl 1)
  have e3 := congrFun h0 (.inr 1)
  have e4 := congrFun h2 (.inl 3)
  have e5 := congrFun h2 (.inr 3)
  simp [kdFv, kdEv, kdW1, kdW3, Pi.single_apply] at e2 e3 e4 e5
  simp [e2, e3, e4, e5]

private def kdPsiH : Multiplicative (F × F × F × F) →* elementaryGroup (kdQ F) where
  toFun x := ⟨kdG4 F (Multiplicative.toAdd x), kdG4_mem F _⟩
  map_one' := Subtype.ext (by simp [kdG4_zero])
  map_mul' x y := Subtype.ext (by simp only [toAdd_mul, kdG4_add, Subgroup.coe_mul])

private def kdT : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) where
  toFun v := fun k => kdSign F k * v k
  invFun v := fun k => kdSign F k * v k
  map_add' v w := by
    funext k
    simp [mul_add]
  map_smul' c v := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    funext k
    simp only [← mul_assoc, kdSign_mul_self, one_mul]
  right_inv v := by
    funext k
    simp only [← mul_assoc, kdSign_mul_self, one_mul]

private theorem kdT_apply (v : Fin 4 ⊕ Fin 4 → F) (k : Fin 4 ⊕ Fin 4) :
    kdT F v k = kdSign F k * v k := rfl

private theorem kdT_sq : kdT F * kdT F = 1 := by
  refine LinearEquiv.ext fun v => funext fun k => ?_
  show kdT F (kdT F v) k = v k
  rw [kdT_apply, kdT_apply, ← mul_assoc, kdSign_mul_self, one_mul]

private theorem kdT_ev0 : kdT F (kdEv F 0) = -kdEv F 0 := by
  funext k
  rcases k with i | i <;> fin_cases i <;> simp [kdT_apply, kdSign, kdEv, Pi.single_apply]

private theorem kdT_ev2 : kdT F (kdEv F 2) = kdEv F 2 := by
  funext k
  rcases k with i | i <;> fin_cases i <;> simp [kdT_apply, kdSign, kdEv, Pi.single_apply]

private theorem kdT_w1 (a b : F) : kdT F (kdW1 F a b) = -kdW1 F a b := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [kdT_apply, kdSign, kdW1, kdEv, kdFv, Pi.single_apply]

private theorem kdT_w3 (c d : F) : kdT F (kdW3 F c d) = kdW3 F c d := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [kdT_apply, kdSign, kdW3, kdEv, kdFv, Pi.single_apply]

private theorem kdT_not_scalar [CharP F 3] : ¬ ∃ c : F, ∀ v, kdT F v = c • v := by
  rintro ⟨c, hc⟩
  have h1 := congrFun (hc (kdEv F 0)) (.inl 0)
  have h2 := congrFun (hc (kdEv F 2)) (.inl 2)
  simp [kdT_apply, kdSign, kdEv, Pi.single_apply] at h1 h2
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h4 : (2 : F) = 0 := by linear_combination h2 - h1
  have h5 : (1 : F) = 0 := by linear_combination h3 - h4
  exact one_ne_zero h5

private def kdA : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  eichler (kdQ F) (kdEv F 0) (kdEv F 1)

private def kdB : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
  eichler (kdQ F) (kdFv F 0) (-kdFv F 1)

private theorem kdA_apply (v : Fin 4 ⊕ Fin 4 → F) :
    kdA F v = v + v (.inr 0) • kdEv F 1 - v (.inr 1) • kdEv F 0 := by
  unfold kdA
  rw [eichler_apply (kdQ_ev0 F) (kdpol_ev0_ev1 F) v, kdpol_v_ev0 F v, kdpol_v_ev1 F v,
    kdQ_ev1 F]
  simp

private theorem kdB_apply (v : Fin 4 ⊕ Fin 4 → F) :
    kdB F v = v - v (.inl 0) • kdFv F 1 + v (.inl 1) • kdFv F 0 := by
  unfold kdB
  rw [eichler_apply (kdQ_fv0 F) (kdpol_fv0_mfv1 F) v, kdpol_v_fv0 F v, kdpol_v_mfv1 F v,
    kdQ_neg_fv1 F]
  simp only [zero_mul, add_zero, neg_smul, smul_neg, sub_neg_eq_add]
  module

private theorem kdA_mem : kdA F ∈ elementaryGroup (kdQ F) :=
  eichler_mem_elementaryGroup (kdQ F) _ _

private theorem kdB_mem : kdB F ∈ elementaryGroup (kdQ F) :=
  eichler_mem_elementaryGroup (kdQ F) _ _

private theorem kdAB_sq [CharP F 3] : kdA F * kdB F * (kdA F * kdB F) = kdT F := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  refine LinearEquiv.ext fun v => funext fun k => ?_
  simp only [LinearEquiv.mul_apply, kdA_apply, kdB_apply, kdT_apply]
  rcases k with i | i <;> fin_cases i
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
    linear_combination (2 * v (.inl 0) - v (.inr 1)) * h3
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
    linear_combination (2 * v (.inl 1) + v (.inr 0)) * h3
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
    linear_combination (v (.inr 0) + v (.inl 1)) * h3
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
    linear_combination (v (.inr 1) - v (.inl 0)) * h3
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]
  · simp [kdEv, kdFv, kdSign, Pi.single_apply]

private theorem kdT_mem_orth [CharP F 3] :
    kdT F ∈ TauCeti.QuadraticMap.orthogonalGroup (kdQ F) := by
  rw [← kdAB_sq F]
  have hA := elementaryGroup_le_orthogonalGroup (kdQ F) (kdA_mem F)
  have hB := elementaryGroup_le_orthogonalGroup (kdQ F) (kdB_mem F)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB) (Subgroup.mul_mem _ hA hB)

private theorem kdT_mem_E [CharP F 3] : kdT F ∈ elementaryGroup (kdQ F) := by
  rw [← kdAB_sq F]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (kdA_mem F) (kdB_mem F))
    (Subgroup.mul_mem _ (kdA_mem F) (kdB_mem F))

private theorem kd_eichler_neg_neg (u w : Fin 4 ⊕ Fin 4 → F) :
    eichler (kdQ F) (-u) (-w) = eichler (kdQ F) u w := by
  have h := eichler_smul_left (Q := kdQ F) (-1 : F) u (-w)
  simpa using h

private theorem kdT_comm_E1 [CharP F 3] (a b : F) :
    kdT F * kdE1 F a b = kdE1 F a b * kdT F := by
  have hc := eichler_conj (kdT_mem_orth F) (kdEv F 0) (kdW1 F a b)
  rw [kdT_ev0, kdT_w1, kd_eichler_neg_neg] at hc
  exact mul_inv_eq_iff_eq_mul.1 hc

private theorem kdT_comm_E3 [CharP F 3] (c d : F) :
    kdT F * kdE3 F c d = kdE3 F c d * kdT F := by
  have hc := eichler_conj (kdT_mem_orth F) (kdEv F 2) (kdW3 F c d)
  rw [kdT_ev2, kdT_w3] at hc
  exact mul_inv_eq_iff_eq_mul.1 hc

private theorem kdG4_comm_T [CharP F 3] (x : F × F × F × F) :
    kdG4 F x * kdT F = kdT F * kdG4 F x := by
  simp only [kdG4]
  calc kdE1 F x.1 x.2.1 * kdE3 F x.2.2.1 x.2.2.2 * kdT F
      = kdE1 F x.1 x.2.1 * (kdE3 F x.2.2.1 x.2.2.2 * kdT F) := mul_assoc _ _ _
    _ = kdE1 F x.1 x.2.1 * (kdT F * kdE3 F x.2.2.1 x.2.2.2) := by rw [← kdT_comm_E3]
    _ = (kdE1 F x.1 x.2.1 * kdT F) * kdE3 F x.2.2.1 x.2.2.2 := (mul_assoc _ _ _).symm
    _ = (kdT F * kdE1 F x.1 x.2.1) * kdE3 F x.2.2.1 x.2.2.2 := by rw [← kdT_comm_E1]
    _ = kdT F * (kdE1 F x.1 x.2.1 * kdE3 F x.2.2.1 x.2.2.2) := mul_assoc _ _ _

end Model

private abbrev kdZ (F : Type) [Field F] : Subgroup (elementaryGroup (kdQ F)) :=
  (scalars F (Fin 4 ⊕ Fin 4 → F)).subgroupOf (elementaryGroup (kdQ F))

private theorem mem_kdZ_iff (F : Type) [Field F] (g : elementaryGroup (kdQ F)) :
    g ∈ kdZ F ↔ ∃ c : F, ∀ v, (g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) v = c • v := by
  rw [kdZ, Subgroup.mem_subgroupOf, mem_scalars]

private theorem kd_isElemAbelian_top (F : Type) [Field F] (h3 : (3 : F) = 0) :
    IsElemAbelian 3 (⊤ : Subgroup (Multiplicative (F × F × F × F))) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun x _ => ?_⟩
  rw [← toAdd_eq_zero, toAdd_pow]
  ext <;> simp [nsmul_eq_mul, h3]

private instance kdFinite_linearEquiv (F : Type) [Field F] [Finite F] :
    Finite ((Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) :=
  Finite.of_injective (fun e : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F) =>
    (e : (Fin 4 ⊕ Fin 4 → F) → (Fin 4 ⊕ Fin 4 → F)))
    (fun _ _ h => LinearEquiv.ext fun v => congrFun h v)

private instance kdFinite_projElementary (F : Type) [Field F] [Finite F] :
    Finite (ProjElementary (CFSG.LieType.Universal.Spin.quadPlus 4 F)) :=
  inferInstance

private theorem kd4_rank (F : Type) [Field F] [Finite F] [CharP F 3] (a : ℕ)
    (ha : Nat.card F = 3 ^ a) :
    4 * a ≤ GLATwoLocalRank 3 (ProjElementary (CFSG.LieType.Universal.Spin.quadPlus 4 F)) := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  let ψP : Multiplicative (F × F × F × F) →* ProjElementary (kdQ F) :=
    (QuotientGroup.mk' (kdZ F)).comp (kdPsiH F)
  have hinj : Function.Injective ψP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx0 : ((kdPsiH F x : elementaryGroup (kdQ F)) : ProjElementary (kdQ F)) = 1 := hx
    rw [QuotientGroup.eq_one_iff, mem_kdZ_iff] at hx0
    exact toAdd_eq_zero.1 (kdG4_eq_zero_of_scalar F (Multiplicative.toAdd x) hx0)
  have hcardF : Nat.card (Multiplicative (F × F × F × F)) = 3 ^ (4 * a) := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (F × F × F × F) ≃ F × F × F × F),
      Nat.card_prod, Nat.card_prod, Nat.card_prod, ha]
    ring
  have hcardE : Nat.card ((⊤ : Subgroup (Multiplicative (F × F × F × F))).map ψP) =
      3 ^ (4 * a) := by
    rw [Subgroup.card_map_of_injective hinj, Subgroup.card_top, hcardF]
  have hEab : IsElemAbelian 3 ((⊤ : Subgroup (Multiplicative (F × F × F × F))).map ψP) :=
    (kd_isElemAbelian_top F h3).map ψP
  let T0H : elementaryGroup (kdQ F) := ⟨kdT F, kdT_mem_E F⟩
  have hs1 : QuotientGroup.mk' (kdZ F) T0H ≠ 1 := by
    intro h
    have h0 : T0H ∈ kdZ F := (QuotientGroup.eq_one_iff _).1 h
    rw [mem_kdZ_iff] at h0
    exact kdT_not_scalar F h0
  have hT0sq : T0H ^ 2 = 1 := Subtype.ext (by
    show kdT F ^ 2 = 1
    rw [pow_two, kdT_sq F])
  have hs2 : (QuotientGroup.mk' (kdZ F) T0H) ^ 2 = 1 := by
    rw [← map_pow, hT0sq, map_one]
  have hT : Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H) ≠ ⊥ :=
    fun h => hs1 (Subgroup.zpowers_eq_bot.1 h)
  have h2T : IsPGroup 2 (Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H)) :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1, pow_one])
  have hcomm : ∀ y : Multiplicative (F × F × F × F),
      Commute (ψP y) (QuotientGroup.mk' (kdZ F) T0H) := by
    intro y
    have hyt : kdPsiH F y * T0H = T0H * kdPsiH F y := Subtype.ext (kdG4_comm_T F _)
    show QuotientGroup.mk' (kdZ F) (kdPsiH F y) * QuotientGroup.mk' (kdZ F) T0H =
      QuotientGroup.mk' (kdZ F) T0H * QuotientGroup.mk' (kdZ F) (kdPsiH F y)
    rw [← map_mul, ← map_mul, hyt]
  have hEN : (⊤ : Subgroup (Multiplicative (F × F × F × F))).map ψP ≤
      Subgroup.normalizer
        ((Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H) : Subgroup (ProjElementary (kdQ F))) :
          Set (ProjElementary (kdQ F))) := by
    rintro x ⟨y, -, rfl⟩
    have hcu : ∀ u ∈ Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H),
        Commute (ψP y) u := by
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      exact (hcomm y).zpow_right k
    have hfix : ∀ u ∈ Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H),
        ψP y * u * (ψP y)⁻¹ = u := by
      intro u hu
      rw [mul_inv_eq_iff_eq_mul]
      exact (hcu u hu).eq
    have hfix' : ∀ u ∈ Subgroup.zpowers (QuotientGroup.mk' (kdZ F) T0H),
        (ψP y)⁻¹ * u * ψP y = u := by
      intro u hu
      rw [(hcu u hu).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hfix h hh]
      exact hh
    · intro hh
      have e := hfix' _ hh
      have e2 : (ψP y)⁻¹ * (ψP y * h * (ψP y)⁻¹) * ψP y = h := by group
      rw [e2] at e
      rw [e]
      exact hh
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    (by norm_num : 1 < 3) hT h2T hEab hEN hcardE

theorem kdD4TwoLocal_holds : KDD4TwoLocal := by
  unfold KDD4TwoLocal
  intro S _ _ q hv hq3 hS
  obtain ⟨e⟩ := hS
  have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨.D 4 q, hv⟩ = 3 :=
    (TauCeti.LieTypeIndex.characteristic_D 4 q).trans hq3
  have hCharP : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) 3 := by
    rw [← hchar]
    infer_instance
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) =
      3 ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.PrimePower.card_def, hq3]
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let e' := e.trans
    ((CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv).trans
      (statedProjEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus 4
          ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩))
        (commutator_orthogonalGroup_quadPlus (by norm_num))))
  have h := kd4_rank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) q.exponent hcard
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr
    (by norm_num : 1 < 3) e'] at h
  exact h

end

end CFSG.LocalAnalysis.GLTheoremA
