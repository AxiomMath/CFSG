module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThreeCheck
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoHermitian

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary

namespace QTwoGammaThree

private theorem gam3_ptOK {a : Nat} (ha : ptOK (pt a) = true) :
    qC (pt a) = 0 ∧ hC (pt a) (pt a) = 1 := by
  simpa [ptOK, Bool.and_eq_true_iff, beq_iff_eq] using ha

private theorem gam3_orthOK {a b : Nat} (h : orthOK (pt a) (pt b) = true) :
    pC (pt a) (pt b) = 0 ∧ hC (pt a) (pt b) = 0 := by
  simpa [orthOK, Bool.and_eq_true_iff, beq_iff_eq] using h

private theorem gam3_expandOK {v : V6} {a b c : Nat}
    (h : expandOK v (pt a) (pt b) (pt c) = true) :
    addC (addC (smulC (hC v (pt a)) (pt a)) (smulC (hC v (pt b)) (pt b)))
      (smulC (hC v (pt c)) (pt c)) = v := by
  simpa [expandOK, beq_iff_eq] using h

theorem pt_spec {i : Nat} (hi : i < 240) : qC (pt i) = 0 ∧ hC (pt i) (pt i) = 1 := by
  exact gam3_ptOK (List.all_eq_true.mp ptsCheck_eq_true i (List.mem_range.mpr hi))

theorem tree_spec {i : Nat} (h0 : 0 < i) (hi : i < 240) :
    ∃ j a b c : Nat, j < i ∧
      (qC (pt a) = 0 ∧ hC (pt a) (pt a) = 1) ∧ (qC (pt b) = 0 ∧ hC (pt b) (pt b) = 1) ∧
      (qC (pt c) = 0 ∧ hC (pt c) (pt c) = 1) ∧
      (pC (pt a) (pt b) = 0 ∧ hC (pt a) (pt b) = 0) ∧
      (pC (pt a) (pt c) = 0 ∧ hC (pt a) (pt c) = 0) ∧
      (pC (pt b) (pt c) = 0 ∧ hC (pt b) (pt c) = 0) ∧
      addC (addC (smulC (hC (pt i) (pt a)) (pt a)) (smulC (hC (pt i) (pt b)) (pt b)))
        (smulC (hC (pt i) (pt c)) (pt c)) = pt i ∧
      addC (addC (smulC (hC (pt j) (pt a)) (pt a)) (smulC (hC (pt j) (pt b)) (pt b)))
        (smulC (hC (pt j) (pt c)) (pt c)) = pt j := by
  have hmem : i - 1 ∈ List.range 239 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp treeCheck_eq_true (i - 1) hmem
  rw [treeOK] at h
  simp only [Bool.and_eq_true_iff, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hji, hpa⟩, hpb⟩, hpc⟩, hab⟩, hac⟩, hbc⟩, hei⟩, hej⟩ := h
  have hei' : expandOK (pt i) (pt (tree.getD (i - 1) (0, 0, 0, 0)).2.1)
      (pt (tree.getD (i - 1) (0, 0, 0, 0)).2.2.1)
      (pt (tree.getD (i - 1) (0, 0, 0, 0)).2.2.2) = true := by
    simpa [Nat.sub_add_cancel h0] using hei
  refine ⟨(tree.getD (i - 1) (0, 0, 0, 0)).1, (tree.getD (i - 1) (0, 0, 0, 0)).2.1,
    (tree.getD (i - 1) (0, 0, 0, 0)).2.2.1, (tree.getD (i - 1) (0, 0, 0, 0)).2.2.2,
    ?_, gam3_ptOK hpa, gam3_ptOK hpb, gam3_ptOK hpc, gam3_orthOK hab, gam3_orthOK hac,
    gam3_orthOK hbc, gam3_expandOK hei', gam3_expandOK hej⟩
  omega

private theorem gam3_fMul_one (a : Fin 4) : fMul 1 a = a := by
  fin_cases a <;> decide

private theorem gam3_smulC_one (v : V6) : smulC 1 v = v := by
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ := v
  simp [smulC, gam3_fMul_one]

private theorem gam3_exists_pt_of_mem_pts {k : Nat} (hk : k ∈ pts) :
    ∃ i < 240, pt i = ofCode k := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hk
  have hlen : pts.length = 240 := by decide +kernel
  refine ⟨i, by omega, ?_⟩
  have hd : pts.getD i 0 = k := by rw [List.getD_eq_getElem pts 0 hi, hget]
  change ofCode (pts.getD i 0) = ofCode k
  rw [hd]

theorem cover_spec (v : V6) (hq : qC v = 0) (hh : hC v v ≠ 0) :
    ∃ i < 240, ∃ c : Fin 4, c ≠ 0 ∧ smulC c v = pt i := by
  obtain ⟨a0, a1, a2, b0, b1, b2⟩ := v
  have hf4 : ∀ a : Fin 4, a ∈ f4s := by
    intro a
    fin_cases a <;> simp [f4s]
  have hcov : coverOK ⟨a0, a1, a2, b0, b1, b2⟩ = true := by
    have hc := coverCheck_eq_true
    simp only [coverCheck] at hc
    have h := List.all_eq_true.mp hc a0 (hf4 a0)
    have h := List.all_eq_true.mp h a1 (hf4 a1)
    have h := List.all_eq_true.mp h a2 (hf4 a2)
    have h := List.all_eq_true.mp h b0 (hf4 b0)
    have h := List.all_eq_true.mp h b1 (hf4 b1)
    exact List.all_eq_true.mp h b2 (hf4 b2)
  have hcond : (qC ⟨a0, a1, a2, b0, b1, b2⟩ == 0 &&
      hC ⟨a0, a1, a2, b0, b1, b2⟩ ⟨a0, a1, a2, b0, b1, b2⟩ != 0) = true := by
    rw [Bool.and_eq_true_iff]
    exact ⟨by simpa [beq_iff_eq] using hq, by simpa [bne_iff_ne] using hh⟩
  have hc := hcov
  rw [coverOK] at hc
  rw [hcond] at hc
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true_iff, List.elem_iff] at hc
  rw [or_assoc] at hc
  rcases hc with h1 | h2 | h3
  · obtain ⟨i, hi, hpti⟩ := gam3_exists_pt_of_mem_pts h1
    exact ⟨i, hi, 1, by decide, by rw [hpti, ofCode_code, gam3_smulC_one]⟩
  · obtain ⟨i, hi, hpti⟩ := gam3_exists_pt_of_mem_pts h2
    exact ⟨i, hi, 2, by decide, by rw [hpti, ofCode_code]⟩
  · obtain ⟨i, hi, hpti⟩ := gam3_exists_pt_of_mem_pts h3
    exact ⟨i, hi, 3, by decide, by rw [hpti, ofCode_code]⟩

variable {K : Type} [Field K]

@[expose] def ι (w : K) (k : Fin 4) : K := ![0, 1, w, w + 1] k

@[expose] def lift (w : K) (v : V6) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim ![ι w v.x0, ι w v.x1, ι w v.x2] ![ι w v.y0, ι w v.y1, ι w v.y2]

variable [CharP K 2] {w : K}

omit [CharP K 2] in
private theorem gam3_w_ne_zero (hw : w * w = w + 1) : w ≠ 0 := by
  rintro rfl
  rw [mul_zero, zero_add] at hw
  exact one_ne_zero hw.symm

private theorem gam3_w_ne_one (hw : w * w = w + 1) : w ≠ 1 := by
  rintro rfl
  rw [mul_one, CharTwo.add_self_eq_zero] at hw
  exact one_ne_zero hw

private theorem gam3_w_add_one_ne_zero (hw : w * w = w + 1) : w + 1 ≠ 0 := by
  intro h
  exact gam3_w_ne_one hw (CharTwo.add_eq_zero.mp h)

omit [CharP K 2] in
private theorem gam3_w_add_one_ne_one (hw : w * w = w + 1) : w + 1 ≠ 1 := by
  intro h
  refine gam3_w_ne_zero hw (add_right_cancel (a := w) (b := 1) (c := 0) ?_)
  rw [h, zero_add]

omit [CharP K 2] in
private theorem gam3_w_ne_add_one (_hw : w * w = w + 1) : w ≠ w + 1 := by
  intro h
  have h1 : w + 0 = w + 1 := by rw [add_zero]; exact h
  exact one_ne_zero (add_left_cancel h1).symm

private noncomputable def gam3_code (x : K) : Fin 4 := by
  classical
  exact if x = 0 then 0 else if x = 1 then 1 else if x = w then 2 else 3

private theorem gam3_code_ι (hw : w * w = w + 1) (a : Fin 4) : gam3_code (w := w) (ι w a) = a := by
  classical
  have h0 := gam3_w_ne_zero hw
  have h1 := gam3_w_ne_one hw
  have h2 := gam3_w_add_one_ne_zero hw
  have h3 := gam3_w_add_one_ne_one hw
  have h4 : w + 1 ≠ w := fun h => gam3_w_ne_add_one hw h.symm
  fin_cases a <;> simp [ι, gam3_code, h0, h1, h2, h3, h4]

private theorem gam3_w_add_w_add_one : w + (w + 1) = 1 := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem ι_fAdd (a b : Fin 4) : ι w (fAdd a b) = ι w a + ι w b := by
  fin_cases a <;> fin_cases b <;>
    simp [ι, fAdd, CharTwo.add_self_eq_zero, gam3_w_add_w_add_one, add_comm, add_left_comm]

private theorem gam3_w_mul_add_one (hw : w * w = w + 1) : w * (w + 1) = 1 := by
  rw [mul_add, mul_one, hw, add_comm (w + 1) w, ← add_assoc, CharTwo.add_self_eq_zero,
    zero_add]

private theorem gam3_add_one_mul (hw : w * w = w + 1) : (w + 1) * w = 1 := by
  rw [add_mul, one_mul, hw, add_comm (w + 1) w, ← add_assoc, CharTwo.add_self_eq_zero,
    zero_add]

private theorem gam3_add_one_sq (hw : w * w = w + 1) : (w + 1) * (w + 1) = w := by
  calc (w + 1) * (w + 1) = (w + 1) * w + (w + 1) := by rw [mul_add, mul_one]
    _ = 1 + (w + 1) := by rw [gam3_add_one_mul hw]
    _ = w := by
      rw [add_comm 1 (w + 1), add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem ι_fMul (hw : w * w = w + 1) (a b : Fin 4) : ι w (fMul a b) = ι w a * ι w b := by
  have h1 := gam3_w_mul_add_one hw
  have h2 := gam3_add_one_mul hw
  have h3 := gam3_add_one_sq hw
  fin_cases a <;> fin_cases b <;>
    simp [ι, fMul, hw, h1, h2, h3]

theorem ι_injective (hw : w * w = w + 1) : Function.Injective (ι w) := by
  intro a b hab
  have h := congrArg (gam3_code (w := w)) hab
  simpa [gam3_code_ι hw] using h

theorem ι_surjective [Finite K] (hK : Nat.card K = 4) (hw : w * w = w + 1) :
    Function.Surjective (ι w) := by
  have hbij : Function.Bijective (ι w) :=
    (Nat.bijective_iff_injective_and_card (ι w)).mpr
      ⟨ι_injective hw, by simpa using hK.symm⟩
  exact hbij.surjective

theorem σ_ι {σ : K ≃+* K} (hσw : σ w = w + 1) (a : Fin 4) : σ (ι w a) = ι w (fMul a a) := by
  have hσw1 : σ (w + 1) = w := by
    rw [map_add, hσw, map_one, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  fin_cases a <;> simp [ι, fMul, hσw, hσw1]

omit [CharP K 2] in
private theorem gam3_lift_inl_zero (v : V6) : lift w v (Sum.inl 0) = ι w v.x0 := rfl

omit [CharP K 2] in
private theorem gam3_lift_inl_one (v : V6) : lift w v (Sum.inl 1) = ι w v.x1 := rfl

omit [CharP K 2] in
private theorem gam3_lift_inl_two (v : V6) : lift w v (Sum.inl 2) = ι w v.x2 := rfl

omit [CharP K 2] in
private theorem gam3_lift_inr_zero (v : V6) : lift w v (Sum.inr 0) = ι w v.y0 := rfl

omit [CharP K 2] in
private theorem gam3_lift_inr_one (v : V6) : lift w v (Sum.inr 1) = ι w v.y1 := rfl

omit [CharP K 2] in
private theorem gam3_lift_inr_two (v : V6) : lift w v (Sum.inr 2) = ι w v.y2 := rfl

theorem quadPlus_lift (hw : w * w = w + 1) (v : V6) :
    quadPlus 3 K (lift w v) = ι w (qC v) := by
  rw [quadPlus_apply, Fin.sum_univ_three]
  simp only [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two,
    gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, qC]
  simp only [← ι_fMul hw, ← ι_fAdd]

theorem polar_lift (hw : w * w = w + 1) (u v : V6) :
    polar (quadPlus 3 K) (lift w u) (lift w v) = ι w (pC u v) := by
  rw [polar_quadPlus, Fin.sum_univ_three]
  simp only [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two,
    gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, pC]
  simp only [← ι_fMul hw, ← ι_fAdd]

theorem flipHerm_lift {σ : K ≃+* K} (hw : w * w = w + 1) (hσw : σ w = w + 1) (u v : V6) :
    flipHerm σ (lift w u) (lift w v) = ι w (hC u v) := by
  rw [flipHerm_apply, Fin.sum_univ_three]
  simp only [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two,
    gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, hC, σ_ι hσw]
  simp only [← ι_fMul hw, ← ι_fAdd]

theorem lift_smulC (hw : w * w = w + 1) (c : Fin 4) (v : V6) :
    lift w (smulC c v) = ι w c • lift w v := by
  funext x
  cases x with
  | inl i =>
    fin_cases i <;>
      simp [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two, smulC, ι_fMul hw]
  | inr i =>
    fin_cases i <;>
      simp [gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, smulC, ι_fMul hw]

theorem lift_addC (u v : V6) : lift w (addC u v) = lift w u + lift w v := by
  funext x
  cases x with
  | inl i =>
    fin_cases i <;>
      simp [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two, addC, ι_fAdd]
  | inr i =>
    fin_cases i <;>
      simp [gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, addC, ι_fAdd]

theorem exists_lift [Finite K] (hK : Nat.card K = 4) (hw : w * w = w + 1)
    (x : Fin 3 ⊕ Fin 3 → K) : ∃ v, lift w v = x := by
  have hsurj := ι_surjective (w := w) hK hw
  refine ⟨⟨Function.surjInv hsurj (x (Sum.inl 0)), Function.surjInv hsurj (x (Sum.inl 1)),
    Function.surjInv hsurj (x (Sum.inl 2)), Function.surjInv hsurj (x (Sum.inr 0)),
    Function.surjInv hsurj (x (Sum.inr 1)), Function.surjInv hsurj (x (Sum.inr 2))⟩, ?_⟩
  funext y
  cases y with
  | inl i =>
    fin_cases i <;>
      simp [gam3_lift_inl_zero, gam3_lift_inl_one, gam3_lift_inl_two, Function.surjInv_eq]
  | inr i =>
    fin_cases i <;>
      simp [gam3_lift_inr_zero, gam3_lift_inr_one, gam3_lift_inr_two, Function.surjInv_eq]

end QTwoGammaThree

open QTwoGammaThree

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

theorem QTwoGammaThree.exists_sigma_eq_add_one (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) : ∃ w : K, σ w = w + 1 ∧ w * w = w + 1 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have hfix : σ (c + σ c) = c + σ c := hσ.trace_fixed c
  have hne : c + σ c ≠ 0 := by
    intro h
    exact hc (CharTwo.add_eq_zero.mp h).symm
  have hsum : c + σ c = 1 := qTwo_fixed_eq_one hσ hK hfix hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (by rw [map_zero])
  have hσc : σ c = c + 1 := by
    calc σ c = 0 + σ c := (zero_add _).symm
      _ = (c + c) + σ c := by rw [CharTwo.add_self_eq_zero]
      _ = c + (c + σ c) := by rw [add_assoc]
      _ = c + 1 := by rw [hsum]
  have hnorm : σ c * c = 1 := qTwo_norm_eq_one hσ hK hc0
  have hcc : c * c = c + 1 := by
    have h : (c + 1) * c = 1 := by rw [← hσc]; exact hnorm
    rw [add_mul, one_mul] at h
    calc c * c = c * c + 0 := (add_zero _).symm
      _ = c * c + (c + c) := by rw [CharTwo.add_self_eq_zero]
      _ = (c * c + c) + c := by rw [add_assoc]
      _ = 1 + c := by rw [h]
      _ = c + 1 := add_comm 1 c
  exact ⟨c, hσc, hcc⟩

omit [Finite K] [CharP K 2] in
theorem isSolid_sup_of_orth (hσ : IsUnitaryInvolution σ) {A B C : Fin 3 ⊕ Fin 3 → K}
    (hA : quadPlus 3 K A = 0) (hB : quadPlus 3 K B = 0) (hC : quadPlus 3 K C = 0)
    (hAA : flipHerm σ A A = 1) (hBB : flipHerm σ B B = 1) (hCC : flipHerm σ C C = 1)
    (hAB : polar (quadPlus 3 K) A B = 0) (hAC : polar (quadPlus 3 K) A C = 0)
    (hBC : polar (quadPlus 3 K) B C = 0) (hAB' : flipHerm σ A B = 0) (hAC' : flipHerm σ A C = 0)
    (hBC' : flipHerm σ B C = 0) :
    IsSolid σ ((K ∙ A ⊔ K ∙ B) ⊔ K ∙ C) := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h] at hAA
    simp at hAA
  have hB0 : B ≠ 0 := by
    intro h
    rw [h] at hBB
    simp at hBB
  have hC0 : C ≠ 0 := by
    intro h
    rw [h] at hCC
    simp at hCC
  have hAsub : IsFlipflopSub σ (K ∙ A) :=
    (isFlipflopSub_span_singleton_iff hA0).mpr ⟨hA, by rw [hAA]; exact one_ne_zero⟩
  have hBsub : IsFlipflopSub σ (K ∙ B) :=
    (isFlipflopSub_span_singleton_iff hB0).mpr ⟨hB, by rw [hBB]; exact one_ne_zero⟩
  have hCsub : IsFlipflopSub σ (K ∙ C) :=
    (isFlipflopSub_span_singleton_iff hC0).mpr ⟨hC, by rw [hCC]; exact one_ne_zero⟩
  have hqAB : (K ∙ A : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ qPerp 3 K (K ∙ B) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, smul_eq_mul, polar_comm (quadPlus 3 K) B A, hAB, mul_zero]
  have hqAC : (K ∙ A : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ qPerp 3 K (K ∙ C) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, smul_eq_mul, polar_comm (quadPlus 3 K) C A, hAC, mul_zero]
  have hqBC : (K ∙ B : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ qPerp 3 K (K ∙ C) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, smul_eq_mul, polar_comm (quadPlus 3 K) C B, hBC, mul_zero]
  have hhAB : (K ∙ A : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ flipOrth σ (K ∙ B) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_flipOrth_span_singleton]
    rw [← flipHerm_conj hσ.invol A B, hAB', map_zero]
  have hhAC : (K ∙ A : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ flipOrth σ (K ∙ C) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_flipOrth_span_singleton]
    rw [← flipHerm_conj hσ.invol A C, hAC', map_zero]
  have hhBC : (K ∙ B : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ flipOrth σ (K ∙ C) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_flipOrth_span_singleton]
    rw [← flipHerm_conj hσ.invol B C, hBC', map_zero]
  have hABorth := IsFlipflopSub.sup_of_orth hσ.invol hAsub hBsub hqAB hhAB
  have hqABC : (K ∙ A ⊔ K ∙ B : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ qPerp 3 K (K ∙ C) :=
    sup_le hqAC hqBC
  have hhABC : (K ∙ A ⊔ K ∙ B : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≤ flipOrth σ (K ∙ C) :=
    sup_le hhAC hhBC
  have hABC := IsFlipflopSub.sup_of_orth hσ.invol hABorth.1 hCsub hqABC hhABC
  refine ⟨hABC.1, ?_⟩
  have hdimAB : Module.finrank K ↥(K ∙ A ⊔ K ∙ B) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ A) (K ∙ B)
    rw [hABorth.2.eq_bot, finrank_bot, finrank_span_singleton hA0,
      finrank_span_singleton hB0] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ A ⊔ K ∙ B) (K ∙ C)
  rw [hABC.2.eq_bot, finrank_bot, hdimAB, finrank_span_singleton hC0] at h
  omega

theorem flipPt_solidChain_of_card_eq_four (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (p p' : FlipPt σ 3) :
    Relation.ReflTransGen (fun x y : FlipPt σ 3 => ∃ S, IsSolid σ S ∧ x.1 ≤ S ∧ y.1 ≤ S) p p' := by
  obtain ⟨w, hσw, hw⟩ := exists_sigma_eq_add_one hσ hK
  have hPpt : ∀ (i : Nat) (hi : i < 240), IsFlipflopPt σ (K ∙ lift w (pt i)) := by
    intro i hi
    have hspec := pt_spec hi
    have hh : flipHerm σ (lift w (pt i)) (lift w (pt i)) = 1 := by
      rw [flipHerm_lift hw hσw, hspec.2]
      rfl
    have hxne : lift w (pt i) ≠ 0 := by
      intro hx0
      rw [hx0] at hh
      simp at hh
    exact (isFlipflopPt_span_singleton_iff hxne).mpr
      ⟨by rw [quadPlus_lift hw, hspec.1]; rfl, by rw [hh]; exact one_ne_zero⟩
  let P : (i : Nat) → i < 240 → FlipPt σ 3 :=
    fun i hi => ⟨K ∙ lift w (pt i), hPpt i hi⟩
  let R : FlipPt σ 3 → FlipPt σ 3 → Prop :=
    fun x y => ∃ S, IsSolid σ S ∧ x.1 ≤ S ∧ y.1 ≤ S
  have hmain : ∀ (i : Nat) (hi : i < 240), Relation.ReflTransGen R (P i hi) (P 0 (by omega)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases h0 : i = 0
      · subst h0
        exact Relation.ReflTransGen.refl
      · have hpos : 0 < i := Nat.pos_of_ne_zero h0
        obtain ⟨j, a, b, c, hji, hpa, hpb, hpc, hab, hac, hbc, hei, hej⟩ :=
          tree_spec hpos hi
        let A : Fin 3 ⊕ Fin 3 → K := lift w (pt a)
        let B : Fin 3 ⊕ Fin 3 → K := lift w (pt b)
        let C : Fin 3 ⊕ Fin 3 → K := lift w (pt c)
        let S : Submodule K (Fin 3 ⊕ Fin 3 → K) := (K ∙ A ⊔ K ∙ B) ⊔ K ∙ C
        have hS : IsSolid σ S := by
          change IsSolid σ ((K ∙ A ⊔ K ∙ B) ⊔ K ∙ C)
          refine isSolid_sup_of_orth hσ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · rw [quadPlus_lift hw, hpa.1]; rfl
          · rw [quadPlus_lift hw, hpb.1]; rfl
          · rw [quadPlus_lift hw, hpc.1]; rfl
          · rw [flipHerm_lift hw hσw, hpa.2]; rfl
          · rw [flipHerm_lift hw hσw, hpb.2]; rfl
          · rw [flipHerm_lift hw hσw, hpc.2]; rfl
          · rw [polar_lift hw, hab.1]; rfl
          · rw [polar_lift hw, hac.1]; rfl
          · rw [polar_lift hw, hbc.1]; rfl
          · rw [flipHerm_lift hw hσw, hab.2]; rfl
          · rw [flipHerm_lift hw hσw, hac.2]; rfl
          · rw [flipHerm_lift hw hσw, hbc.2]; rfl
        have hmemA : A ∈ S := Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.mem_span_singleton_self A))
        have hmemB : B ∈ S := Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.mem_span_singleton_self B))
        have hmemC : C ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self C)
        have hexp : lift w (pt i) =
            ι w (hC (pt i) (pt a)) • A + ι w (hC (pt i) (pt b)) • B +
              ι w (hC (pt i) (pt c)) • C := by
          have hl : lift w (pt i) = lift w (addC (addC
              (smulC (hC (pt i) (pt a)) (pt a)) (smulC (hC (pt i) (pt b)) (pt b)))
              (smulC (hC (pt i) (pt c)) (pt c))) := by rw [hei]
          rw [hl, lift_addC, lift_addC, lift_smulC hw, lift_smulC hw, lift_smulC hw]
        have hmi : lift w (pt i) ∈ S := by
          rw [hexp]
          exact Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.smul_mem S _ hmemA) (Submodule.smul_mem S _ hmemB))
            (Submodule.smul_mem S _ hmemC)
        have hexpj : lift w (pt j) =
            ι w (hC (pt j) (pt a)) • A + ι w (hC (pt j) (pt b)) • B +
              ι w (hC (pt j) (pt c)) • C := by
          have hl : lift w (pt j) = lift w (addC (addC
              (smulC (hC (pt j) (pt a)) (pt a)) (smulC (hC (pt j) (pt b)) (pt b)))
              (smulC (hC (pt j) (pt c)) (pt c))) := by rw [hej]
          rw [hl, lift_addC, lift_addC, lift_smulC hw, lift_smulC hw, lift_smulC hw]
        have hmj : lift w (pt j) ∈ S := by
          rw [hexpj]
          exact Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.smul_mem S _ hmemA) (Submodule.smul_mem S _ hmemB))
            (Submodule.smul_mem S _ hmemC)
        have hPiS : (P i hi).1 ≤ S := (Submodule.span_singleton_le_iff_mem _ S).mpr hmi
        have hPjS : (P j (by omega)).1 ≤ S :=
          (Submodule.span_singleton_le_iff_mem _ S).mpr hmj
        have hstep : R (P i hi) (P j (by omega)) := ⟨S, hS, hPiS, hPjS⟩
        exact (Relation.ReflTransGen.single hstep).trans (ih j hji (by omega))
  have hcov : ∀ q : FlipPt σ 3, ∃ (i : Nat) (hi : i < 240), q = P i hi := by
    intro q
    obtain ⟨x, hqx, hxq, hxh⟩ := IsFlipflopPt.exists_eq_span q.2
    obtain ⟨v, rfl⟩ := exists_lift hK hw x
    have hqv : qC v = 0 := by
      apply ι_injective hw
      rw [← quadPlus_lift hw v, hxq]
      rfl
    have hhv : hC v v ≠ 0 := by
      intro h
      apply hxh
      rw [flipHerm_lift hw hσw v v, h]
      rfl
    obtain ⟨i, hi, c, hc0, hsmul⟩ := cover_spec v hqv hhv
    refine ⟨i, hi, ?_⟩
    apply Subtype.ext
    change q.1 = K ∙ lift w (pt i)
    rw [hqx, ← hsmul, lift_smulC hw]
    have hcne : ι w c ≠ 0 := by
      intro h
      exact hc0 (ι_injective hw (by rw [h]; rfl))
    rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcne)]
  obtain ⟨i, hi, hpi⟩ := hcov p
  obtain ⟨i', hi', hpi'⟩ := hcov p'
  rw [hpi, hpi']
  have hsymm : Std.Symm R := ⟨fun a b h => by
    obtain ⟨S, hS, ha, hb⟩ := h
    exact ⟨S, hS, hb, ha⟩⟩
  have hrt : Std.Symm (Relation.ReflTransGen R) :=
    @Relation.ReflTransGen.symmetric (FlipPt σ 3) R hsymm
  have hback : Relation.ReflTransGen R (P 0 (by omega)) (P i' hi') :=
    hrt.symm (P i' hi') (P 0 (by omega)) (hmain i' hi')
  exact (hmain i hi).trans hback

theorem flagGraph_two_connected_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) : (flagGraph σ 2).Connected := by
  let G : SimpleGraph (FlagVert σ 2) := flagGraph σ 2
  let R : FlipPt σ 3 → FlipPt σ 3 → Prop :=
    fun x y => ∃ S, IsSolid σ S ∧ x.1 ≤ S ∧ y.1 ≤ S
  have hchain := flipPt_solidChain_of_card_eq_four hσ hK
  have finrank_pt (p : FlipPt σ 3) : Module.finrank K p.1 = 1 := by
    obtain ⟨v, hpv, -, hh⟩ := IsFlipflopPt.exists_eq_span p.2
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hh (by simp)
    rw [hpv, finrank_span_singleton hv0]
  have ptVert_spec (p : FlipPt σ 3) : IsFlipflopSub σ p.1 ∧ p.1 ≠ ⊥ ∧
      Module.finrank K p.1 ≠ 2 := by
    obtain ⟨v, hpv, hq, hh⟩ := IsFlipflopPt.exists_eq_span p.2
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hh (by simp)
    have hsub : IsFlipflopSub σ (K ∙ v) :=
      (isFlipflopSub_span_singleton_iff hv0).mpr ⟨hq, hh⟩
    have hne : (K ∙ v) ≠ ⊥ := fun h => hv0 ((Submodule.span_singleton_eq_bot).mp h)
    have hdim : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
    rw [hpv]
    exact ⟨hsub, hne, by omega⟩
  let ptVert (p : FlipPt σ 3) : FlagVert σ 2 :=
    ⟨p.1, (ptVert_spec p).1, (ptVert_spec p).2.1, (ptVert_spec p).2.2⟩
  have hdim_cases (U : FlagVert σ 2) :
      Module.finrank K U.1 = 1 ∨ Module.finrank K U.1 = 3 := by
    have hle := IsFlipflopSub.finrank_le U.2.1
    have hne0 : Module.finrank K U.1 ≠ 0 :=
      fun h0 => U.2.2.1 (Submodule.finrank_eq_zero.mp h0)
    have hne2 := U.2.2.2
    omega
  have ptSolid_adj {p : FlipPt σ 3} {U : FlagVert σ 2} (hp : p.1 ≤ U.1)
      (hU : Module.finrank K U.1 = 3) : G.Adj (ptVert p) U := by
    refine Or.inl (lt_of_le_of_ne hp ?_)
    intro heq
    have hp1 := finrank_pt p
    rw [heq, hU] at hp1
    omega
  have chain_step (x y : FlipPt σ 3) (h : R x y) :
      G.Reachable (ptVert x) (ptVert y) := by
    obtain ⟨S, hS, hxS, hyS⟩ := h
    have hS2 : Module.finrank K S = 3 := hS.2
    have hSne : S ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hS2
      omega
    let SV : FlagVert σ 2 := ⟨S, hS.1, hSne, by rw [hS2]; omega⟩
    have hx1 := finrank_pt x
    have hy1 := finrank_pt y
    have hxlt : (ptVert x).1 < SV.1 := by
      refine lt_of_le_of_ne hxS ?_
      intro heq
      rw [heq, hS2] at hx1
      omega
    have hylt : (ptVert y).1 < SV.1 := by
      refine lt_of_le_of_ne hyS ?_
      intro heq
      rw [heq, hS2] at hy1
      omega
    exact (SimpleGraph.Adj.reachable (Or.inl hxlt)).trans
      (SimpleGraph.Adj.reachable (Or.inr (Or.inl hylt)))
  have chain_reach : ∀ x y : FlipPt σ 3, Relation.ReflTransGen R x y →
      G.Reachable (ptVert x) (ptVert y) := by
    intro x y hxy
    induction hxy with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail hab hbc ih => exact ih.trans (chain_step _ _ hbc)
  have hex : ∀ U : FlagVert σ 2, ∃ p : FlipPt σ 3, p.1 ≤ U.1 := by
    intro U
    rcases hdim_cases U with h1 | h3
    · obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.2.2.1
      have hspan : U.1 = K ∙ v := by
        refine (Submodule.eq_of_le_of_finrank_eq
          ((Submodule.span_singleton_le_iff_mem _ U.1).mpr hvU) ?_).symm
        rw [finrank_span_singleton hv0, h1]
      have hsub : IsFlipflopSub σ (K ∙ v) := hspan ▸ U.2.1
      obtain ⟨hq, hh⟩ := (isFlipflopSub_span_singleton_iff hv0).mp hsub
      refine ⟨⟨K ∙ v, (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hq, hh⟩⟩, ?_⟩
      rw [hspan]
    · obtain ⟨b, hb⟩ := exists_orthonormal_basis (σ := σ) hσ.invol hσ.exists_ne
        (fun a ha ha0 => by
          obtain ⟨c, hc⟩ := hσ.norm_surj a ha ha0
          exact ⟨c, by rw [mul_comm] at hc; exact hc⟩) U.2.1
      let i : Fin (Module.finrank K U.1) := ⟨0, by omega⟩
      let v : Fin 3 ⊕ Fin 3 → K := (b i : U.1)
      have hvU : v ∈ U.1 := (b i).2
      have hq : quadPlus 3 K v = 0 := U.2.1.total v hvU
      have hh : flipHerm σ v v = 1 := by
        have := hb i i
        simpa [v] using this
      have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hh
        simp at hh
      refine ⟨⟨K ∙ v, ?_⟩, (Submodule.span_singleton_le_iff_mem _ U.1).mpr hvU⟩
      exact (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hq, by rw [hh]; exact one_ne_zero⟩
  rw [SimpleGraph.connected_iff]
  constructor
  · intro U W
    obtain ⟨pU, hpU⟩ := hex U
    obtain ⟨pW, hpW⟩ := hex W
    have hU : G.Reachable U (ptVert pU) := by
      rcases hdim_cases U with h1 | h3
      · have heq : ptVert pU = U := by
          apply Subtype.ext
          exact Submodule.eq_of_le_of_finrank_eq hpU (by rw [finrank_pt pU, h1])
        rw [heq]
      · exact SimpleGraph.Adj.reachable (ptSolid_adj hpU h3).symm
    have hW : G.Reachable (ptVert pW) W := by
      rcases hdim_cases W with h1 | h3
      · have heq : ptVert pW = W := by
          apply Subtype.ext
          exact Submodule.eq_of_le_of_finrank_eq hpW (by rw [finrank_pt pW, h1])
        rw [heq]
      · exact SimpleGraph.Adj.reachable (ptSolid_adj hpW h3)
    exact hU.trans ((chain_reach pU pW (hchain pU pW)).trans hW)
  · exact ⟨ptVert ⟨K ∙ stdE (K := K) (⟨0, by omega⟩ : Fin 3),
      isFlipflopPt_stdE (n := 3) (by omega)⟩⟩

end CFSG.ClassicalInvolution.PhanDn
