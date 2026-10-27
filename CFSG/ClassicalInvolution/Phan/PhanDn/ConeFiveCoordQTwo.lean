module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagCone
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoFiveModel
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoHermitian

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

private def res12 : (Fin 5 ⊕ Fin 5 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.pi (Sum.elim
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inl 1),
      LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inl 2)]
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inr 1),
      LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inr 2)])

private def res34 : (Fin 5 ⊕ Fin 5 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.pi (Sum.elim
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inl 3),
      LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inl 4)]
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inr 3),
      LinearMap.proj (R := K) (φ := fun _ : Fin 5 ⊕ Fin 5 => K) (.inr 4)])

@[simp] private theorem res12_inl_zero (x : Fin 5 ⊕ Fin 5 → K) :
    res12 x (.inl 0) = x (.inl 1) := by
  simp [res12]

@[simp] private theorem res12_inl_one (x : Fin 5 ⊕ Fin 5 → K) :
    res12 x (.inl 1) = x (.inl 2) := by
  simp [res12]

@[simp] private theorem res12_inr_zero (x : Fin 5 ⊕ Fin 5 → K) :
    res12 x (.inr 0) = x (.inr 1) := by
  simp [res12]

@[simp] private theorem res12_inr_one (x : Fin 5 ⊕ Fin 5 → K) :
    res12 x (.inr 1) = x (.inr 2) := by
  simp [res12]

@[simp] private theorem res34_inl_zero (x : Fin 5 ⊕ Fin 5 → K) :
    res34 x (.inl 0) = x (.inl 3) := by
  simp [res34]

@[simp] private theorem res34_inl_one (x : Fin 5 ⊕ Fin 5 → K) :
    res34 x (.inl 1) = x (.inl 4) := by
  simp [res34]

@[simp] private theorem res34_inr_zero (x : Fin 5 ⊕ Fin 5 → K) :
    res34 x (.inr 0) = x (.inr 3) := by
  simp [res34]

@[simp] private theorem res34_inr_one (x : Fin 5 ⊕ Fin 5 → K) :
    res34 x (.inr 1) = x (.inr 4) := by
  simp [res34]

private def emb12 : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K) :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin 2 ⊕ Fin 2 => K) (.inl 0)).smulRight (stdE (K := K) 1) +
  (LinearMap.proj (.inl 1)).smulRight (stdE 2) +
  (LinearMap.proj (.inr 0)).smulRight (stdF 1) +
  (LinearMap.proj (.inr 1)).smulRight (stdF 2)

private def emb34 : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K) :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin 2 ⊕ Fin 2 => K) (.inl 0)).smulRight
    (stdE (K := K) (3 : Fin 5)) +
  (LinearMap.proj (.inl 1)).smulRight (stdE 4) +
  (LinearMap.proj (.inr 0)).smulRight (stdF 3) +
  (LinearMap.proj (.inr 1)).smulRight (stdF 4)

@[simp] private theorem emb12_inl_one (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inl 1) = x (.inl 0) := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inl_two (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inl 2) = x (.inl 1) := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inr_one (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inr 1) = x (.inr 0) := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inr_two (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inr 2) = x (.inr 1) := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inl_zero (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inl 0) = 0 := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inr_zero (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inr 0) = 0 := by
  simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inl_three (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inl 3) = x (.inl 0) := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inl_four (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inl 4) = x (.inl 1) := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inr_three (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inr 3) = x (.inr 0) := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inr_four (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inr 4) = x (.inr 1) := by
  simp [emb34, LinearMap.smulRight_apply]


@[simp] private theorem emb12_inl_three (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inl 3) = 0 := by simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inl_four (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inl 4) = 0 := by simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inr_three (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inr 3) = 0 := by simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb12_inr_four (x : Fin 2 ⊕ Fin 2 → K) :
    emb12 x (.inr 4) = 0 := by simp [emb12, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inl_zero (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inl 0) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inl_one (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inl 1) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inl_two (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inl 2) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inr_zero (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inr 0) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inr_one (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inr 1) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]

@[simp] private theorem emb34_inr_two (x : Fin 2 ⊕ Fin 2 → K) :
    emb34 x (.inr 2) = 0 := by
  simp [emb34, LinearMap.smulRight_apply]


section coordinate_expansions

variable (x y : Fin 5 ⊕ Fin 5 → K)

private theorem quadPlus_five_eq :
    quadPlus 5 K x = x (.inl 0) * x (.inr 0) + quadPlus 2 K (res12 x) +
      quadPlus 2 K (res34 x) := by
  rw [quadPlus_apply, quadPlus_apply, quadPlus_apply, Fin.sum_univ_five, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [res12, res34]
  ring

private theorem polar_five_eq :
    polar (quadPlus 5 K) x y = x (.inl 0) * y (.inr 0) + x (.inr 0) * y (.inl 0) +
      polar (quadPlus 2 K) (res12 x) (res12 y) +
      polar (quadPlus 2 K) (res34 x) (res34 y) := by
  rw [polar_quadPlus, polar_quadPlus, polar_quadPlus, Fin.sum_univ_five, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [res12, res34]
  ring

private theorem flipHerm_five_eq :
    flipHerm σ x y = x (.inl 0) * σ (y (.inl 0)) + x (.inr 0) * σ (y (.inr 0)) +
      flipHerm σ (res12 x) (res12 y) + flipHerm σ (res34 x) (res34 y) := by
  rw [flipHerm_apply, flipHerm_apply, flipHerm_apply, Fin.sum_univ_five, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [res12, res34]
  ring

private theorem res34_eq_zero (h3 : x (.inl 3) = 0 ∧ x (.inr 3) = 0)
    (h4 : x (.inl 4) = 0 ∧ x (.inr 4) = 0) : res34 x = 0 := by
  funext i
  rcases i with j | j <;> fin_cases j <;> simp [h3, h4]

private theorem eq_emb12_add_emb34 (h0l : x (.inl 0) = 0) (h0r : x (.inr 0) = 0) :
    x = emb12 (res12 x) + emb34 (res34 x) := by
  ext v
  rcases v with i | i <;> fin_cases i <;> simp [h0l, h0r, stdE, stdF, emb12, emb34, res12, res34]

end coordinate_expansions

section membership_in_the_orthogonal_space

private def rowVec (γ : Fin 5 ⊕ Fin 5 → K) : Fin 2 ⊕ Fin 2 → K := res12 γ

private noncomputable def coneSpace (σ : K ≃+* K) (γ : Fin 5 ⊕ Fin 5 → K) :
    Submodule K (Fin 5 ⊕ Fin 5 → K) :=
  qPerp 5 K ((K ∙ stdE (K := K) 0) ⊔ K ∙ γ) ⊓
    flipOrth σ ((K ∙ stdE (K := K) 0) ⊔ K ∙ γ)

@[simp] private theorem rowVec_def (γ : Fin 5 ⊕ Fin 5 → K) : rowVec γ = res12 γ := rfl

private theorem row_of_mem_coneSpace {γ x : Fin 5 ⊕ Fin 5 → K} (hσ : IsUnitaryInvolution σ)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hx : x ∈ coneSpace σ γ) :
    x (.inl 0) = 0 ∧ x (.inr 0) = 0 ∧
      polar (quadPlus 2 K) (res12 x) (rowVec γ) = 0 ∧
      flipHerm σ (res12 x) (rowVec γ) = 0 := by
  obtain ⟨hq, hft⟩ := Submodule.mem_inf.mp hx
  rw [mem_qPerp] at hq
  rw [mem_flipOrth] at hft
  have hstdq : polar (quadPlus 5 K) (stdE (K := K) 0) x = 0 :=
    hq _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have hstdh : flipHerm σ (stdE (K := K) 0) x = 0 :=
    hft _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have hγq : polar (quadPlus 5 K) γ x = 0 :=
    hq _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hγh : flipHerm σ γ x = 0 :=
    hft _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hxr0 : x (.inr 0) = 0 := by
    rw [← polar_quadPlus_single_inl (n := 5) (K := K) x 0]
    rwa [polar_comm]
  have hxl0 : x (.inl 0) = 0 := by
    rw [← flipHerm_stdE_right (σ := σ) x 0]
    exact (flipHerm_eq_zero_iff (σ := σ) (n := 5) hσ.invol).mp hstdh
  have hres34 : res34 γ = 0 := res34_eq_zero γ h3 h4
  have hpolar : polar (quadPlus 2 K) (res12 γ) (res12 x) = 0 := by
    have h := hγq
    rw [polar_five_eq γ x, hxr0, hxl0, hres34] at h
    simpa [rowVec_def] using h
  have hflip : flipHerm σ (res12 γ) (res12 x) = 0 := by
    have h := hγh
    rw [flipHerm_five_eq γ x, hxr0, hxl0, hres34] at h
    simpa [rowVec_def] using h
  refine ⟨hxl0, hxr0, ?_, ?_⟩
  · rw [rowVec_def, polar_comm]
    exact hpolar
  · rw [rowVec_def]
    exact (flipHerm_eq_zero_iff (σ := σ) (n := 2) hσ.invol).mp hflip

private theorem mem_coneSpace_of_row {γ x : Fin 5 ⊕ Fin 5 → K} (hσ : IsUnitaryInvolution σ)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (h0l : x (.inl 0) = 0) (h0r : x (.inr 0) = 0)
    (hpolar : polar (quadPlus 2 K) (res12 x) (rowVec γ) = 0)
    (hflip : flipHerm σ (res12 x) (rowVec γ) = 0) : x ∈ coneSpace σ γ := by
  have hres34 : res34 γ = 0 := res34_eq_zero γ h3 h4
  have hpolar' : polar (quadPlus 2 K) (res12 γ) (res12 x) = 0 := by
    rwa [rowVec_def, polar_comm] at hpolar
  have hflip' : flipHerm σ (res12 γ) (res12 x) = 0 :=
    (flipHerm_eq_zero_iff (σ := σ) (n := 2) hσ.invol).mp (by rwa [rowVec_def] at hflip)
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_qPerp]
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
    obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [polar_add_left, polar_smul_left, polar_smul_left]
    have h1 : polar (quadPlus 5 K) (stdE (K := K) 0) x = 0 := by
      rw [show stdE (K := K) 0 = Pi.single (.inl (0 : Fin 5)) 1 from rfl, polar_comm,
        polar_quadPlus_single_inl (n := 5) (K := K) x 0, h0r]
    have h2 : polar (quadPlus 5 K) γ x = 0 := by
      rw [polar_five_eq γ x, h0l, h0r, hres34]
      simp [hpolar']
    rw [h1, h2, smul_zero, smul_zero, add_zero]
  · rw [mem_flipOrth]
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
    obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left]
    have h1 : flipHerm σ (stdE (K := K) 0) x = 0 := by
      rw [flipHerm_eq_zero_iff (σ := σ) (n := 5) hσ.invol, flipHerm_stdE_right, h0l]
    have h2 : flipHerm σ γ x = 0 := by
      rw [flipHerm_five_eq γ x, h0l, h0r, hres34]
      simp [hflip']
    rw [h1, h2, mul_zero, mul_zero, add_zero]

end membership_in_the_orthogonal_space



section row_conditions

private theorem rowVec_ne_zero {γ : Fin 5 ⊕ Fin 5 → K}
    (h12 : ¬ (γ (.inl 1) = 0 ∧ γ (.inr 1) = 0 ∧ γ (.inl 2) = 0 ∧ γ (.inr 2) = 0)) :
    rowVec γ ≠ 0 := by
  rintro h
  apply h12
  have h1 := congrFun h (.inl 0)
  have h2 := congrFun h (.inl 1)
  have h3 := congrFun h (.inr 0)
  have h4 := congrFun h (.inr 1)
  simp [rowVec, res12] at h1 h2 h3 h4
  exact ⟨h1, h3, h2, h4⟩

private theorem row_condition [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {γ : Fin 5 ⊕ Fin 5 → K} (hγ : IsFlipflopPt σ (K ∙ γ))
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (h0 : γ (.inl 0) ≠ 0 ∨ γ (.inr 0) ≠ 0) :
    (quadPlus 2 K (rowVec γ) = 0 ∧ flipHerm σ (rowVec γ) (rowVec γ) = 0) ∨
      (quadPlus 2 K (rowVec γ) ≠ 0 ∧ flipHerm σ (rowVec γ) (rowVec γ) = 1) := by
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    simp at h0
  obtain ⟨hQ, hH⟩ := (isFlipflopPt_span_singleton_iff (σ := σ) hγ0).mp hγ
  have hH1 : flipHerm σ γ γ = 1 :=
    qTwo_fixed_eq_one hσ hK (flipHerm_self_mem_fixed (n := 5) hσ.invol γ) hH
  have hQ5 : quadPlus 5 K γ = γ (.inl 0) * γ (.inr 0) + quadPlus 2 K (rowVec γ) := by
    rw [quadPlus_five_eq, res34_eq_zero γ h3 h4]
    simp [rowVec_def]
  have hH5 : flipHerm σ γ γ = γ (.inl 0) * σ (γ (.inl 0)) +
      γ (.inr 0) * σ (γ (.inr 0)) + flipHerm σ (rowVec γ) (rowVec γ) := by
    rw [flipHerm_five_eq, res34_eq_zero γ h3 h4]
    simp [rowVec_def]
  have hQv : quadPlus 2 K (rowVec γ) = γ (.inl 0) * γ (.inr 0) := by
    have hst : γ (.inl 0) * γ (.inr 0) + quadPlus 2 K (rowVec γ) = 0 := by
      rw [← hQ5, hQ]
    have h' : quadPlus 2 K (rowVec γ) = -(γ (.inl 0) * γ (.inr 0)) := by
      linear_combination hst
    rwa [CharTwo.neg_eq] at h'
  have hHv : flipHerm σ (rowVec γ) (rowVec γ) =
      1 + γ (.inl 0) * σ (γ (.inl 0)) + γ (.inr 0) * σ (γ (.inr 0)) := by
    have hst : γ (.inl 0) * σ (γ (.inl 0)) + γ (.inr 0) * σ (γ (.inr 0)) +
        flipHerm σ (rowVec γ) (rowVec γ) = 1 := by
      rw [← hH5, hH1]
    have h' : flipHerm σ (rowVec γ) (rowVec γ) =
        1 - γ (.inl 0) * σ (γ (.inl 0)) - γ (.inr 0) * σ (γ (.inr 0)) := by
      linear_combination hst
    rwa [sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.neg_eq] at h'
  rcases eq_or_ne (γ (.inl 0) * γ (.inr 0)) 0 with hst0 | hst0
  · left
    have hQ0 : quadPlus 2 K (rowVec γ) = 0 := by rw [hQv, hst0]
    refine ⟨hQ0, ?_⟩
    rcases mul_eq_zero.mp hst0 with hs | ht
    · have ht0 : γ (.inr 0) ≠ 0 := by
        rcases h0 with h | h
        · exact absurd hs h
        · exact h
      have htσ : γ (.inr 0) * σ (γ (.inr 0)) = 1 := by
        have h := qTwo_norm_eq_one hσ hK ht0
        rwa [mul_comm] at h
      rw [hHv, hs, htσ]
      simp [CharTwo.add_self_eq_zero]
    · have hs0 : γ (.inl 0) ≠ 0 := by
        rcases h0 with h | h
        · exact h
        · exact absurd ht h
      have hsσ : γ (.inl 0) * σ (γ (.inl 0)) = 1 := by
        have h := qTwo_norm_eq_one hσ hK hs0
        rwa [mul_comm] at h
      rw [hHv, hsσ, ht]
      simp [CharTwo.add_self_eq_zero]
  · right
    refine ⟨?_, ?_⟩
    · rw [hQv]
      exact hst0
    · have hs0 : γ (.inl 0) ≠ 0 := fun h => hst0 (by rw [h, zero_mul])
      have ht0 : γ (.inr 0) ≠ 0 := fun h => hst0 (by rw [h, mul_zero])
      have hsσ : γ (.inl 0) * σ (γ (.inl 0)) = 1 := by
        have h := qTwo_norm_eq_one hσ hK hs0
        rwa [mul_comm] at h
      have htσ : γ (.inr 0) * σ (γ (.inr 0)) = 1 := by
        have h := qTwo_norm_eq_one hσ hK ht0
        rwa [mul_comm] at h
      rw [hHv, hsσ, htσ, CharTwo.add_self_eq_zero, zero_add]

end row_conditions

section coordinate_embeddings

private def res12Three : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
  LinearMap.pi (Sum.elim
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inl 1),
      LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inl 2)]
    ![LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inr 1),
      LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inr 2)])

@[simp] private theorem res12Three_inl_zero (y : Fin 3 ⊕ Fin 3 → K) :
    res12Three y (.inl 0) = y (.inl 1) := by simp [res12Three]

@[simp] private theorem res12Three_inl_one (y : Fin 3 ⊕ Fin 3 → K) :
    res12Three y (.inl 1) = y (.inl 2) := by simp [res12Three]

@[simp] private theorem res12Three_inr_zero (y : Fin 3 ⊕ Fin 3 → K) :
    res12Three y (.inr 0) = y (.inr 1) := by simp [res12Three]

@[simp] private theorem res12Three_inr_one (y : Fin 3 ⊕ Fin 3 → K) :
    res12Three y (.inr 1) = y (.inr 2) := by simp [res12Three]

@[simp] private theorem res12_emb12 (y : Fin 2 ⊕ Fin 2 → K) : res12 (emb12 y) = y := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

@[simp] private theorem res12_emb34 (y : Fin 2 ⊕ Fin 2 → K) : res12 (emb34 y) = 0 := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

@[simp] private theorem res34_emb12 (y : Fin 2 ⊕ Fin 2 → K) : res34 (emb12 y) = 0 := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

@[simp] private theorem res34_emb34 (y : Fin 2 ⊕ Fin 2 → K) : res34 (emb34 y) = y := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

@[simp] private theorem res34_emb12_add_emb34 (a b : Fin 2 ⊕ Fin 2 → K) :
    res34 (emb12 a + emb34 b) = b := by
  rw [map_add, res34_emb12, res34_emb34]
  simp

private theorem quadPlus_emb12 (y : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 5 K (emb12 y) = quadPlus 2 K y := by
  rw [quadPlus_five_eq, res12_emb12, res34_emb12]
  simp

private theorem quadPlus_emb34 (y : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 5 K (emb34 y) = quadPlus 2 K y := by
  rw [quadPlus_five_eq, res12_emb34, res34_emb34]
  simp

private theorem polar_emb12 (a b : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 5 K) (emb12 a) (emb12 b) = polar (quadPlus 2 K) a b := by
  rw [polar_five_eq, res12_emb12, res34_emb12]
  simp

private theorem polar_emb34 (a b : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 5 K) (emb34 a) (emb34 b) = polar (quadPlus 2 K) a b := by
  rw [polar_five_eq, res12_emb34, res34_emb34]
  simp

private theorem polar_emb12_emb34 (a b : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 5 K) (emb12 a) (emb34 b) = 0 := by
  rw [polar_five_eq, res12_emb12, res34_emb12]
  simp

private theorem dFlip_emb12 (y : Fin 2 ⊕ Fin 2 → K) :
    dFlip σ (emb12 y) = emb12 (dFlip σ y) := by
  ext v
  rcases v with i | i <;> fin_cases i <;> simp [dFlip]

private theorem dFlip_emb34 (y : Fin 2 ⊕ Fin 2 → K) :
    dFlip σ (emb34 y) = emb34 (dFlip σ y) := by
  ext v
  rcases v with i | i <;> fin_cases i <;> simp [dFlip]

end coordinate_embeddings


section standard_points

@[simp] private theorem res12_stdE_three : res12 (stdE (K := K) (3 : Fin 5)) = 0 := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

@[simp] private theorem res12_stdE_four : res12 (stdE (K := K) (4 : Fin 5)) = 0 := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp

private theorem stdE_three_mem_coneSpace (hσ : IsUnitaryInvolution σ)
    {γ : Fin 5 ⊕ Fin 5 → K} (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) : stdE (K := K) (3 : Fin 5) ∈ coneSpace σ γ := by
  refine mem_coneSpace_of_row hσ h3 h4 (by simp) (by simp) ?_ ?_
  · rw [res12_stdE_three]; simp
  · rw [res12_stdE_three]; simp

private theorem stdE_four_mem_coneSpace (hσ : IsUnitaryInvolution σ)
    {γ : Fin 5 ⊕ Fin 5 → K} (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) : stdE (K := K) (4 : Fin 5) ∈ coneSpace σ γ := by
  refine mem_coneSpace_of_row hσ h3 h4 (by simp) (by simp) ?_ ?_
  · rw [res12_stdE_four]; simp
  · rw [res12_stdE_four]; simp

private theorem isFlipflopPt_stdE_three (σ : K ≃+* K) :
    IsFlipflopPt σ (K ∙ stdE (K := K) (3 : Fin 5)) := by
  refine (isFlipflopPt_span_singleton_iff (σ := σ) ?_).mpr ⟨quadPlus_stdE _, ?_⟩
  · intro h
    have h1 := congrFun h (.inl 3)
    simp [stdE] at h1
  · rw [flipHerm_stdE_stdE, if_pos rfl]
    exact one_ne_zero

private theorem isFlipflopPt_stdE_four (σ : K ≃+* K) :
    IsFlipflopPt σ (K ∙ stdE (K := K) (4 : Fin 5)) := by
  refine (isFlipflopPt_span_singleton_iff (σ := σ) ?_).mpr ⟨quadPlus_stdE _, ?_⟩
  · intro h
    have h1 := congrFun h (.inl 4)
    simp [stdE] at h1
  · rw [flipHerm_stdE_stdE, if_pos rfl]
    exact one_ne_zero

private noncomputable def stdPointThree (σ : K ≃+* K) : FlipPt σ 5 :=
  ⟨K ∙ stdE (K := K) (3 : Fin 5), isFlipflopPt_stdE_three σ⟩

private noncomputable def stdPointFour (σ : K ≃+* K) : FlipPt σ 5 :=
  ⟨K ∙ stdE (K := K) (4 : Fin 5), isFlipflopPt_stdE_four σ⟩

private theorem coneStep_of_orth_point (hσ : ∀ x, σ (σ x) = x)
    {γ : Fin 5 ⊕ Fin 5 → K} {p q : FlipPt σ 5}
    (hpE : p.1 ≤ coneSpace σ γ) (hqE : q.1 ≤ coneSpace σ γ)
    (hpq : p.1 ≤ qPerp 5 K q.1) (hph : p.1 ≤ flipOrth σ q.1) :
    ConeStep σ 4 (coneSpace σ γ) p q := by
  obtain ⟨hsup, hdisj⟩ := IsFlipflopSub.sup_of_orth hσ p.2.isFlipflopSub q.2.isFlipflopSub hpq hph
  have hTle : p.1 ⊔ q.1 ≤ coneSpace σ γ := sup_le hpE hqE
  have hdim : Module.finrank K ↥(p.1 ⊔ q.1) + 2 ≤ 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
    rw [hdisj.eq_bot, finrank_bot, add_zero, p.2.finrank_eq_one, q.2.finrank_eq_one] at h
    omega
  exact ⟨p.1 ⊔ q.1, hsup, hTle, hdim, le_sup_left, le_sup_right⟩

private theorem coneStep_to_stdPointFour (hσ : ∀ x, σ (σ x) = x)
    {γ x : Fin 5 ⊕ Fin 5 → K} {p : FlipPt σ 5} (hp : p.1 = K ∙ x)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hσ' : IsUnitaryInvolution σ)
    (hpE : p.1 ≤ coneSpace σ γ) (hx4 : x (.inl 4) = 0 ∧ x (.inr 4) = 0) :
    ConeStep σ 4 (coneSpace σ γ) p (stdPointFour σ) := by
  refine coneStep_of_orth_point hσ hpE ?_ ?_ ?_
  · rw [show (stdPointFour σ).1 = K ∙ stdE (K := K) (4 : Fin 5) from rfl]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (stdE_four_mem_coneSpace hσ' h3 h4)
  · rw [hp, Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left]
    have hz : polar (quadPlus 5 K) (stdE (K := K) (4 : Fin 5)) x = 0 := by
      rw [polar_comm, show stdE (K := K) (4 : Fin 5) = Pi.single (.inl (4 : Fin 5)) 1 from rfl,
        polar_quadPlus_single_inl (n := 5) (K := K) x 4, hx4.2]
    rw [hz, smul_zero]
  · rw [hp, Submodule.span_singleton_le_iff_mem, mem_flipOrth]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_left]
    have hz : flipHerm σ (stdE (K := K) (4 : Fin 5)) x = 0 := by
      rw [flipHerm_eq_zero_iff (n := 5) hσ, flipHerm_stdE_right, hx4.1]
    rw [hz, mul_zero]

private theorem coneStep_to_stdPointThree (hσ : ∀ x, σ (σ x) = x)
    {γ x : Fin 5 ⊕ Fin 5 → K} {p : FlipPt σ 5} (hp : p.1 = K ∙ x)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hσ' : IsUnitaryInvolution σ)
    (hpE : p.1 ≤ coneSpace σ γ) (hx3 : x (.inl 3) = 0 ∧ x (.inr 3) = 0) :
    ConeStep σ 4 (coneSpace σ γ) p (stdPointThree σ) := by
  refine coneStep_of_orth_point hσ hpE ?_ ?_ ?_
  · rw [show (stdPointThree σ).1 = K ∙ stdE (K := K) (3 : Fin 5) from rfl]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (stdE_three_mem_coneSpace hσ' h3 h4)
  · rw [hp, Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left]
    have hz : polar (quadPlus 5 K) (stdE (K := K) (3 : Fin 5)) x = 0 := by
      rw [polar_comm, show stdE (K := K) (3 : Fin 5) = Pi.single (.inl (3 : Fin 5)) 1 from rfl,
        polar_quadPlus_single_inl (n := 5) (K := K) x 3, hx3.2]
    rw [hz, smul_zero]
  · rw [hp, Submodule.span_singleton_le_iff_mem, mem_flipOrth]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_left]
    have hz : flipHerm σ (stdE (K := K) (3 : Fin 5)) x = 0 := by
      rw [flipHerm_eq_zero_iff (n := 5) hσ, flipHerm_stdE_right, hx3.1]
    rw [hz, mul_zero]

private theorem coneStep_stdPointThree_stdPointFour (hσ : ∀ x, σ (σ x) = x)
    (hσ' : IsUnitaryInvolution σ) {γ : Fin 5 ⊕ Fin 5 → K}
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) :
    ConeStep σ 4 (coneSpace σ γ) (stdPointThree σ) (stdPointFour σ) := by
  refine coneStep_to_stdPointFour hσ (p := stdPointThree σ) (x := stdE (K := K) (3 : Fin 5))
    rfl h3 h4 hσ' ?_ (by simp)
  rw [show (stdPointThree σ).1 = K ∙ stdE (K := K) (3 : Fin 5) from rfl]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr (stdE_three_mem_coneSpace hσ' h3 h4)

end standard_points


section twisted_model

private noncomputable def psi (U W : Fin 5 ⊕ Fin 5 → K) :
    (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K) :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inl 0)).smulRight U +
  (LinearMap.proj (R := K) (φ := fun _ : Fin 3 ⊕ Fin 3 => K) (.inr 0)).smulRight W +
  emb34.comp res12Three

private theorem psi_apply (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    psi U W y = y (.inl 0) • U + y (.inr 0) • W + emb34 (res12Three y) := by
  simp [psi]

@[simp] private theorem psi_emb12_inl_zero (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inl 0) = 0 := by
  simp [psi, emb34]

@[simp] private theorem psi_emb12_inr_zero (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inr 0) = 0 := by
  simp [psi, emb34]

@[simp] private theorem psi_inl_one (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    psi U W y (.inl 1) = y (.inl 0) * U (.inl 1) + y (.inr 0) * W (.inl 1) := by
  simp [psi, emb34]

@[simp] private theorem psi_inl_two (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    psi U W y (.inl 2) = y (.inl 0) * U (.inl 2) + y (.inr 0) * W (.inl 2) := by
  simp [psi, emb34]

@[simp] private theorem psi_inr_one (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    psi U W y (.inr 1) = y (.inl 0) * U (.inr 1) + y (.inr 0) * W (.inr 1) := by
  simp [psi, emb34]

@[simp] private theorem psi_inr_two (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    psi U W y (.inr 2) = y (.inl 0) * U (.inr 2) + y (.inr 0) * W (.inr 2) := by
  simp [psi, emb34]

@[simp] private theorem psi_emb12_inl_three (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inl 3) = y (.inl 1) := by
  simp [psi, emb34]

@[simp] private theorem psi_emb12_inl_four (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inl 4) = y (.inl 2) := by
  simp [psi, emb34]

@[simp] private theorem psi_emb12_inr_three (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inr 3) = y (.inr 1) := by
  simp [psi, emb34]

@[simp] private theorem psi_emb12_inr_four (u w : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) : psi (emb12 u) (emb12 w) y (.inr 4) = y (.inr 2) := by
  simp [psi, emb34]

private theorem quadPlus_three_eq (y : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K y = y (.inl 0) * y (.inr 0) + quadPlus 2 K (res12Three y) := by
  rw [quadPlus_apply, quadPlus_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [res12Three]
  ring

@[simp] private theorem res12_psi (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    res12 (psi U W y) =
      y (.inl 0) • res12 U + y (.inr 0) • res12 W + res12 (emb34 (res12Three y)) := by
  rw [psi_apply, map_add, map_add, map_smul, map_smul]

@[simp] private theorem res34_psi (U W : Fin 5 ⊕ Fin 5 → K) (y : Fin 3 ⊕ Fin 3 → K) :
    res34 (psi U W y) =
      y (.inl 0) • res34 U + y (.inr 0) • res34 W + res34 (emb34 (res12Three y)) := by
  rw [psi_apply, map_add, map_add, map_smul, map_smul]

private theorem quadPlus_psi {U W : Fin 5 ⊕ Fin 5 → K} (hU : quadPlus 5 K U = 0)
    (hW : quadPlus 5 K W = 0)
    (hUW : polar (quadPlus 5 K) U W = 1)
    (hUE : ∀ h : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 5 K) U (emb34 h) = 0)
    (hWE : ∀ h : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 5 K) W (emb34 h) = 0)
    (y : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 5 K (psi U W y) = quadPlus 3 K y := by
  simp only [psi_apply, quadPlus_three_eq, QuadraticMap.map_add (quadPlus 5 K),
    QuadraticMap.map_smul (quadPlus 5 K), hU, hW, hUW, hUE, hWE, polar_add_left,
    polar_smul_left, polar_smul_right, smul_zero, add_zero, zero_add,
    quadPlus_emb34]
  ring

private theorem polar_psi_psi {U W : Fin 5 ⊕ Fin 5 → K} (hU : quadPlus 5 K U = 0)
    (hW : quadPlus 5 K W = 0)
    (hUW : polar (quadPlus 5 K) U W = 1)
    (hUE : ∀ h : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 5 K) U (emb34 h) = 0)
    (hWE : ∀ h : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 5 K) W (emb34 h) = 0)
    (y y' : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 5 K) (psi U W y) (psi U W y') = polar (quadPlus 3 K) y y' := by
  change quadPlus 5 K (psi U W y + psi U W y') - quadPlus 5 K (psi U W y) -
    quadPlus 5 K (psi U W y') =
      quadPlus 3 K (y + y') - quadPlus 3 K y - quadPlus 3 K y'
  rw [show psi U W y + psi U W y' = psi U W (y + y')
    from (map_add (psi U W) y y').symm,
    quadPlus_psi hU hW hUW hUE hWE, quadPlus_psi hU hW hUW hUE hWE,
    quadPlus_psi hU hW hUW hUE hWE]

end twisted_model


section twisted_form_calculations

@[simp] private theorem dFlipTw_inl_zero (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inl 0) = σ (y (.inl 0)) := rfl

@[simp] private theorem dFlipTw_inr_zero (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inr 0) = σ (y (.inr 0)) := rfl

@[simp] private theorem dFlipTw_inl_one (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inl 1) = σ (y (.inr 1)) := rfl

@[simp] private theorem dFlipTw_inr_one (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inr 1) = σ (y (.inl 1)) := rfl

@[simp] private theorem dFlipTw_inl_two (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inl 2) = σ (y (.inr 2)) := rfl

@[simp] private theorem dFlipTw_inr_two (y : Fin 3 ⊕ Fin 3 → K) :
    dFlipTw σ y (.inr 2) = σ (y (.inl 2)) := rfl

private theorem res12Three_dFlipTw (y : Fin 3 ⊕ Fin 3 → K) :
    res12Three (dFlipTw σ y) = dFlip σ (res12Three y) := by
  ext i
  rcases i with j | j <;> fin_cases j <;> simp [res12Three, dFlipTw, dFlip]

private theorem dFlip_psi {U W : Fin 5 ⊕ Fin 5 → K}
    (hU : dFlip σ U = U) (hW : dFlip σ W = W) (y : Fin 3 ⊕ Fin 3 → K) :
    dFlip σ (psi U W y) = psi U W (dFlipTw σ y) := by
  rw [psi_apply, psi_apply, dFlip_add, dFlip_add, dFlip_smul, dFlip_smul, hU, hW,
    dFlip_emb34, res12Three_dFlipTw, dFlipTw_inl_zero, dFlipTw_inr_zero]

private def chartVec (α β : K) (g : Fin 2 ⊕ Fin 2 → K) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim ![α, g (.inl 0), g (.inl 1)] ![β, g (.inr 0), g (.inr 1)]

omit [Field K] in
@[simp] private theorem chartVec_inl_zero (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inl 0) = α := by simp [chartVec]

omit [Field K] in
@[simp] private theorem chartVec_inl_one (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inl 1) = g (.inl 0) := by simp [chartVec]

omit [Field K] in
@[simp] private theorem chartVec_inl_two (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inl 2) = g (.inl 1) := by simp [chartVec]

omit [Field K] in
@[simp] private theorem chartVec_inr_zero (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inr 0) = β := by simp [chartVec]

omit [Field K] in
@[simp] private theorem chartVec_inr_one (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inr 1) = g (.inr 0) := by simp [chartVec]

omit [Field K] in
@[simp] private theorem chartVec_inr_two (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    chartVec α β g (.inr 2) = g (.inr 1) := by simp [chartVec]

@[simp] private theorem res12Three_chartVec (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    res12Three (chartVec α β g) = g := by
  ext i; rcases i with j | j <;> fin_cases j <;> simp [res12Three, chartVec]

private theorem quadPlus_three_chartVec (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    quadPlus 3 K (chartVec α β g) = α * β + quadPlus 2 K g := by
  rw [quadPlus_three_eq, res12Three_chartVec]
  simp [chartVec]

private theorem polar_three_chartVec (α β : K) (g : Fin 2 ⊕ Fin 2 → K)
    (y : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 3 K) (chartVec α β g) y =
      α * y (.inr 0) + β * y (.inl 0) + polar (quadPlus 2 K) g (res12Three y) := by
  rw [polar_quadPlus, Fin.sum_univ_three]
  conv_rhs => rw [polar_quadPlus, Fin.sum_univ_two]
  simp
  ring

private theorem polar_chartVec_dFlipTw (α β : K) (g : Fin 2 ⊕ Fin 2 → K) :
    polar (quadPlus 3 K) (chartVec α β g) (dFlipTw σ (chartVec α β g)) =
      α * σ β + β * σ α + flipHerm σ g g := by
  rw [polar_quadPlus, flipHerm_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [chartVec_inl_zero, chartVec_inl_one, chartVec_inl_two, chartVec_inr_zero,
    chartVec_inr_one, chartVec_inr_two, dFlipTw_inl_zero, dFlipTw_inl_one, dFlipTw_inl_two,
    dFlipTw_inr_zero, dFlipTw_inr_one, dFlipTw_inr_two]
  ring

private theorem polar_psi_of_row {x : Fin 5 ⊕ Fin 5 → K} {u w : Fin 2 ⊕ Fin 2 → K}
    {α β : K} (hx : x = emb12 (res12 x) + emb34 (res34 x))
    (hα : polar (quadPlus 2 K) (res12 x) w = α)
    (hβ : polar (quadPlus 2 K) (res12 x) u = β) (y : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 5 K) x (psi (emb12 u) (emb12 w) y) =
      α * y (.inr 0) + β * y (.inl 0) +
        polar (quadPlus 2 K) (res34 x) (res12Three y) := by
  have h1 : ∀ z : Fin 2 ⊕ Fin 2 → K,
      polar (quadPlus 5 K) (emb34 (res34 x)) (emb12 z) = 0 := fun z => by
    rw [polar_comm]
    exact polar_emb12_emb34 z (res34 x)
  rw [hx, psi_apply, polar_add_left]
  simp only [polar_add_right, polar_smul_right, polar_emb12, polar_emb12_emb34, h1,
    hα, hβ, smul_eq_mul, mul_zero, add_zero, zero_add, res34_emb12_add_emb34,
    polar_emb34]
  ring

end twisted_form_calculations


section totally_singular_alternative

private theorem dFlip_polar_row (hσ : ∀ x, σ (σ x) = x) {v0 y : Fin 2 ⊕ Fin 2 → K}
    (hp : polar (quadPlus 2 K) y v0 = 0) (hh : flipHerm σ y v0 = 0) :
    polar (quadPlus 2 K) (dFlip σ y) v0 = 0 ∧ flipHerm σ (dFlip σ y) v0 = 0 := by
  constructor
  · rw [show v0 = dFlip σ (dFlip σ v0) from (dFlip_dFlip hσ v0).symm, polar_dFlip]
    rw [show polar (quadPlus 2 K) y (dFlip σ v0) = flipHerm σ y v0 from rfl, hh, map_zero]
  · show polar (quadPlus 2 K) (dFlip σ y) (dFlip σ v0) = 0
    rw [polar_dFlip, hp, map_zero]

private theorem dFlip_mem_linear (hσ : ∀ x, σ (σ x) = x) {v0 u w y : Fin 2 ⊕ Fin 2 → K}
    (hu : dFlip σ u = u) (hw : dFlip σ w = w)
    (hpv : polar (quadPlus 2 K) y v0 = 0) (hhv : flipHerm σ y v0 = 0)
    (hpu : polar (quadPlus 2 K) y u = 0) (hpw : polar (quadPlus 2 K) y w = 0) :
    polar (quadPlus 2 K) (dFlip σ y) v0 = 0 ∧ flipHerm σ (dFlip σ y) v0 = 0 ∧
      polar (quadPlus 2 K) (dFlip σ y) u = 0 ∧
        polar (quadPlus 2 K) (dFlip σ y) w = 0 := by
  obtain ⟨h1, h2⟩ := dFlip_polar_row hσ hpv hhv
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [show u = dFlip σ (dFlip σ u) from (dFlip_dFlip hσ u).symm, polar_dFlip, hu, hpu,
      map_zero]
  · rw [show w = dFlip σ (dFlip σ w) from (dFlip_dFlip hσ w).symm, polar_dFlip, hw, hpw,
      map_zero]

private theorem zero_pair_of_row_singular [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {γ x : Fin 5 ⊕ Fin 5 → K} (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) (hxE : x ∈ coneSpace σ γ)
    (hxQ : quadPlus 5 K x = 0) (hxH : flipHerm σ x x ≠ 0)
    (hE1 : ∀ y : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) y (rowVec γ) = 0 →
      flipHerm σ y (rowVec γ) = 0 → quadPlus 2 K y = 0) :
    (x (.inl 4) = 0 ∧ x (.inr 4) = 0) ∨ (x (.inl 3) = 0 ∧ x (.inr 3) = 0) := by
  obtain ⟨hxl0, hxr0, hp, hh⟩ := row_of_mem_coneSpace hσ h3 h4 hxE
  have hQ12 : quadPlus 2 K (res12 x) = 0 := hE1 _ hp hh
  obtain ⟨hp', hh'⟩ := dFlip_polar_row hσ.invol hp hh
  have hQd : quadPlus 2 K (dFlip σ (res12 x)) = 0 := hE1 _ hp' hh'
  have hQsum : quadPlus 2 K (res12 x + dFlip σ (res12 x)) = 0 := by
    refine hE1 _ ?_ ?_
    · rw [polar_add_left, hp, hp', zero_add]
    · rw [flipHerm_add_left, hh, hh', zero_add]
  have hself : flipHerm σ (res12 x) (res12 x) = 0 := by
    have h := QuadraticMap.map_add (quadPlus 2 K) (res12 x) (dFlip σ (res12 x))
    rw [hQsum, hQ12, hQd] at h
    have hpz : polar (quadPlus 2 K) (res12 x) (dFlip σ (res12 x)) = 0 := by
      simpa using h.symm
    simpa [flipHerm] using hpz
  have hQ34 : quadPlus 2 K (res34 x) = 0 := by
    have h := quadPlus_five_eq x
    rw [hxl0, hxr0, hxQ, hQ12] at h
    simpa using h.symm
  have hH34 : flipHerm σ (res34 x) (res34 x) ≠ 0 := by
    intro h34
    apply hxH
    have h := flipHerm_five_eq (σ := σ) x x
    rw [hxl0, hxr0, hself, h34] at h
    simpa using h
  rcases isFlipflopPt_vec_block_of_card_eq_four hσ hK hQ34 hH34 with h4' | h3'
  · exact Or.inl ⟨by simpa using h4'.1, by simpa using h4'.2⟩
  · exact Or.inr ⟨by simpa using h3'.1, by simpa using h3'.2⟩

private theorem reach_std_of_singular [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {γ x : Fin 5 ⊕ Fin 5 → K} {p : FlipPt σ 5} (hpval : p.1 = K ∙ x)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hxE : x ∈ coneSpace σ γ) (hxQ : quadPlus 5 K x = 0)
    (hxH : flipHerm σ x x ≠ 0)
    (hE1 : ∀ y : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) y (rowVec γ) = 0 →
      flipHerm σ y (rowVec γ) = 0 → quadPlus 2 K y = 0) :
    Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointFour σ) ∨
      Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointThree σ) := by
  have hpE : p.1 ≤ coneSpace σ γ := by
    rw [hpval]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxE
  rcases zero_pair_of_row_singular hσ hK h3 h4 hxE hxQ hxH hE1 with h4' | h3'
  · exact Or.inl (Relation.ReflTransGen.single
      (coneStep_to_stdPointFour hσ.invol hpval h3 h4 hσ hpE h4'))
  · exact Or.inr (Relation.ReflTransGen.single
      (coneStep_to_stdPointThree hσ.invol hpval h3 h4 hσ hpE h3'))

end totally_singular_alternative


section hyperbolic_expansion

private theorem sub_mem_linear
    {v0 u w y : Fin 2 ⊕ Fin 2 → K} {α β : K}
    (hα : α = polar (quadPlus 2 K) y w) (hβ : β = polar (quadPlus 2 K) y u)
    (huu : polar (quadPlus 2 K) u u = 0) (hww : polar (quadPlus 2 K) w w = 0)
    (huw : polar (quadPlus 2 K) u w = 1)
    (hyv : polar (quadPlus 2 K) y v0 = 0) (hhyv : flipHerm σ y v0 = 0)
    (huv : polar (quadPlus 2 K) u v0 = 0) (hhuv : flipHerm σ u v0 = 0)
    (hwv : polar (quadPlus 2 K) w v0 = 0) (hhwv : flipHerm σ w v0 = 0) :
    polar (quadPlus 2 K) (y - α • u - β • w) v0 = 0 ∧
      flipHerm σ (y - α • u - β • w) v0 = 0 ∧
      polar (quadPlus 2 K) (y - α • u - β • w) u = 0 ∧
      polar (quadPlus 2 K) (y - α • u - β • w) w = 0 := by
  have hwu : polar (quadPlus 2 K) w u = 1 := by rw [polar_comm]; exact huw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hyv, huv, hwv]
    simp
  · rw [flipHerm_sub_left, flipHerm_sub_left, flipHerm_smul_left, flipHerm_smul_left,
      hhyv, hhuv, hhwv]
    simp
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, huu, hwu,
      smul_zero, smul_eq_mul, mul_one, ← hβ, sub_zero]
    exact sub_self β
  · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, huw, hww,
      smul_eq_mul, mul_one, smul_zero, ← hα, sub_self, sub_zero]

private theorem quadPlus_sum_eq {u w r : Fin 2 ⊕ Fin 2 → K}
    (hQu : quadPlus 2 K u = 0) (hQw : quadPlus 2 K w = 0)
    (huw : polar (quadPlus 2 K) u w = 1) (hru : polar (quadPlus 2 K) r u = 0)
    (hrw : polar (quadPlus 2 K) r w = 0) (hQr : quadPlus 2 K r = 0) (α β : K) :
    quadPlus 2 K (r + α • u + β • w) = α * β := by
  simp only [QuadraticMap.map_add (quadPlus 2 K), QuadraticMap.map_smul (quadPlus 2 K),
    hQu, hQw, hQr, huw, hru, hrw, polar_add_left, polar_smul_left, polar_smul_right,
    smul_zero, add_zero, zero_add]
  ring

private theorem flipHerm_sum_eq (hσ : ∀ x, σ (σ x) = x)
    {v0 u w r : Fin 2 ⊕ Fin 2 → K} {α β : K}
    (hu : dFlip σ u = u) (hw : dFlip σ w = w)
    (hrv : polar (quadPlus 2 K) r v0 = 0) (hhrv : flipHerm σ r v0 = 0)
    (hru : polar (quadPlus 2 K) r u = 0) (hrw : polar (quadPlus 2 K) r w = 0)
    (hR : ∀ z : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) z v0 = 0 →
      flipHerm σ z v0 = 0 → polar (quadPlus 2 K) z u = 0 →
      polar (quadPlus 2 K) z w = 0 → quadPlus 2 K z = 0)
    (huu : polar (quadPlus 2 K) u u = 0) (hww : polar (quadPlus 2 K) w w = 0)
    (huw : polar (quadPlus 2 K) u w = 1) :
    flipHerm σ (r + α • u + β • w) (r + α • u + β • w) = α * σ β + β * σ α := by
  have hdr := dFlip_mem_linear hσ hu hw hrv hhrv hru hrw
  have hQr := hR r hrv hhrv hru hrw
  have hQdr := hR (dFlip σ r) hdr.1 hdr.2.1 hdr.2.2.1 hdr.2.2.2
  have hsumlin : polar (quadPlus 2 K) (r + dFlip σ r) v0 = 0 ∧
      flipHerm σ (r + dFlip σ r) v0 = 0 ∧
      polar (quadPlus 2 K) (r + dFlip σ r) u = 0 ∧
      polar (quadPlus 2 K) (r + dFlip σ r) w = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_add_left, hrv, hdr.1, add_zero]
    · rw [flipHerm_add_left, hhrv, hdr.2.1, add_zero]
    · rw [polar_add_left, hru, hdr.2.2.1, add_zero]
    · rw [polar_add_left, hrw, hdr.2.2.2, add_zero]
  have hQsum := hR (r + dFlip σ r) hsumlin.1 hsumlin.2.1 hsumlin.2.2.1 hsumlin.2.2.2
  have hrr : flipHerm σ r r = 0 := by
    have h := QuadraticMap.map_add (quadPlus 2 K) r (dFlip σ r)
    rw [hQsum, hQr, hQdr] at h
    have hp : polar (quadPlus 2 K) r (dFlip σ r) = 0 := by simpa using h.symm
    simpa [flipHerm] using hp
  have hru' : flipHerm σ r u = 0 := by
    rw [show flipHerm σ r u = polar (quadPlus 2 K) r (dFlip σ u) from rfl, hu, hru]
  have hrw' : flipHerm σ r w = 0 := by
    rw [show flipHerm σ r w = polar (quadPlus 2 K) r (dFlip σ w) from rfl, hw, hrw]
  have hur' : flipHerm σ u r = 0 := by
    rw [show flipHerm σ u r = polar (quadPlus 2 K) u (dFlip σ r) from rfl]
    rw [polar_comm]
    exact hdr.2.2.1
  have hwr' : flipHerm σ w r = 0 := by
    rw [show flipHerm σ w r = polar (quadPlus 2 K) w (dFlip σ r) from rfl]
    rw [polar_comm]
    exact hdr.2.2.2
  have huu' : flipHerm σ u u = 0 := by
    rw [show flipHerm σ u u = polar (quadPlus 2 K) u (dFlip σ u) from rfl, hu, huu]
  have hww' : flipHerm σ w w = 0 := by
    rw [show flipHerm σ w w = polar (quadPlus 2 K) w (dFlip σ w) from rfl, hw, hww]
  have huw' : flipHerm σ u w = 1 := by
    rw [show flipHerm σ u w = polar (quadPlus 2 K) u (dFlip σ w) from rfl, hw, huw]
  have hwu' : flipHerm σ w u = 1 := by
    rw [show flipHerm σ w u = polar (quadPlus 2 K) w (dFlip σ u) from rfl, hu]
    rw [polar_comm]
    exact huw
  simp only [flipHerm_add_left, flipHerm_add_right, flipHerm_smul_left, flipHerm_smul_right,
    hrr, hru', hrw', hur', hwr', huu', hww', huw', hwu', mul_zero, add_zero]
  ring

end hyperbolic_expansion


section cone_reduction

private theorem exists_singular_chartVec [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) {γ x : Fin 5 ⊕ Fin 5 → K}
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hxE : x ∈ coneSpace σ γ) (hxQ : quadPlus 5 K x = 0)
    (hxH : flipHerm σ x x ≠ 0)
    {u w : Fin 2 ⊕ Fin 2 → K} (hu : dFlip σ u = u) (hw : dFlip σ w = w)
    (hQu : quadPlus 2 K u = 0) (hQw : quadPlus 2 K w = 0)
    (huw : polar (quadPlus 2 K) u w = 1)
    (huv : polar (quadPlus 2 K) u (rowVec γ) = 0)
    (hhuv : flipHerm σ u (rowVec γ) = 0)
    (hwv : polar (quadPlus 2 K) w (rowVec γ) = 0)
    (hhwv : flipHerm σ w (rowVec γ) = 0)
    (hR : ∀ y : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) y (rowVec γ) = 0 →
      flipHerm σ y (rowVec γ) = 0 → polar (quadPlus 2 K) y u = 0 →
      polar (quadPlus 2 K) y w = 0 → quadPlus 2 K y = 0) :
    ∃ α β : K, α = polar (quadPlus 2 K) (res12 x) w ∧
      β = polar (quadPlus 2 K) (res12 x) u ∧
      quadPlus 3 K (chartVec α β (res34 x)) = 0 ∧
      polar (quadPlus 3 K) (chartVec α β (res34 x))
        (dFlipTw σ (chartVec α β (res34 x))) ≠ 0 := by
  obtain ⟨hxl0, hxr0, hpv, hhv⟩ := row_of_mem_coneSpace hσ h3 h4 hxE
  have huu : polar (quadPlus 2 K) u u = 0 := polar_self_of_singular hQu
  have hww : polar (quadPlus 2 K) w w = 0 := polar_self_of_singular hQw
  set α : K := polar (quadPlus 2 K) (res12 x) w with hα
  set β : K := polar (quadPlus 2 K) (res12 x) u with hβ
  set r : Fin 2 ⊕ Fin 2 → K := res12 x - α • u - β • w with hr
  have hlin : polar (quadPlus 2 K) r (rowVec γ) = 0 ∧
      flipHerm σ r (rowVec γ) = 0 ∧ polar (quadPlus 2 K) r u = 0 ∧
        polar (quadPlus 2 K) r w = 0 := by
    rw [hr]
    exact sub_mem_linear hα hβ huu hww huw hpv hhv huv hhuv hwv hhwv
  have hQr : quadPlus 2 K r = 0 :=
    hR r hlin.1 hlin.2.1 hlin.2.2.1 hlin.2.2.2
  have hy_eq : res12 x = r + α • u + β • w := by
    rw [hr]
    abel
  have hQ12 : quadPlus 2 K (res12 x) = α * β := by
    rw [hy_eq]
    exact quadPlus_sum_eq hQu hQw huw hlin.2.2.1 hlin.2.2.2 hQr α β
  have hH12 : flipHerm σ (res12 x) (res12 x) = α * σ β + β * σ α := by
    rw [hy_eq]
    exact flipHerm_sum_eq hσ.invol hu hw hlin.1 hlin.2.1 hlin.2.2.1 hlin.2.2.2 hR
      huu hww huw
  have hQx : quadPlus 5 K x = α * β + quadPlus 2 K (res34 x) := by
    rw [quadPlus_five_eq, hxl0, hxr0, hQ12]
    simp
  have hHx : flipHerm σ x x =
      α * σ β + β * σ α + flipHerm σ (res34 x) (res34 x) := by
    rw [flipHerm_five_eq, hxl0, hxr0, hH12]
    simp
  have hQx' : quadPlus 3 K (chartVec α β (res34 x)) = 0 := by
    rw [quadPlus_three_chartVec, ← hQx, hxQ]
  have hxx' : polar (quadPlus 3 K) (chartVec α β (res34 x))
      (dFlipTw σ (chartVec α β (res34 x))) ≠ 0 := by
    rw [polar_chartVec_dFlipTw, ← hHx]
    exact hxH
  exact ⟨α, β, hα, hβ, hQx', hxx'⟩

private theorem exists_orthogonal_point_of_hyperbolic [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {γ x : Fin 5 ⊕ Fin 5 → K}
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hxE : x ∈ coneSpace σ γ) (hxQ : quadPlus 5 K x = 0)
    (hxH : flipHerm σ x x ≠ 0)
    {u w : Fin 2 ⊕ Fin 2 → K} (hu : dFlip σ u = u) (hw : dFlip σ w = w)
    (hQu : quadPlus 2 K u = 0) (hQw : quadPlus 2 K w = 0)
    (huw : polar (quadPlus 2 K) u w = 1)
    (huv : polar (quadPlus 2 K) u (rowVec γ) = 0)
    (hhuv : flipHerm σ u (rowVec γ) = 0)
    (hwv : polar (quadPlus 2 K) w (rowVec γ) = 0)
    (hhwv : flipHerm σ w (rowVec γ) = 0)
    (hR : ∀ y : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) y (rowVec γ) = 0 →
      flipHerm σ y (rowVec γ) = 0 → polar (quadPlus 2 K) y u = 0 →
      polar (quadPlus 2 K) y w = 0 → quadPlus 2 K y = 0) :
    ∃ z : Fin 5 ⊕ Fin 5 → K, z ∈ coneSpace σ γ ∧ quadPlus 5 K z = 0 ∧
      flipHerm σ z z ≠ 0 ∧ polar (quadPlus 5 K) x z = 0 ∧ flipHerm σ x z = 0 ∧
      ((z (.inl 4) = 0 ∧ z (.inr 4) = 0) ∨ (z (.inl 3) = 0 ∧ z (.inr 3) = 0)) := by
  obtain ⟨hxl0, hxr0, hpv, hhv⟩ := row_of_mem_coneSpace hσ h3 h4 hxE
  obtain ⟨α, β, hα, hβ, hQx', hxx'⟩ :=
    exists_singular_chartVec hσ h3 h4 hxE hxQ hxH hu hw hQu hQw huw huv hhuv hwv hhwv hR
  obtain ⟨z', hz'Q, hz'H, hxz', hxz'd, hz'pair⟩ :=
    exists_orth_dFlipTw_of_card_eq_four hσ hK hQx' hxx'
  set z : Fin 5 ⊕ Fin 5 → K := psi (emb12 u) (emb12 w) z' with hzdef
  have hUQ : quadPlus 5 K (emb12 u) = 0 := by rw [quadPlus_emb12, hQu]
  have hWQ : quadPlus 5 K (emb12 w) = 0 := by rw [quadPlus_emb12, hQw]
  have hUW : polar (quadPlus 5 K) (emb12 u) (emb12 w) = 1 := by
    rw [polar_emb12, huw]
  have hUE : ∀ h : Fin 2 ⊕ Fin 2 → K,
      polar (quadPlus 5 K) (emb12 u) (emb34 h) = 0 := fun h => polar_emb12_emb34 u h
  have hWE : ∀ h : Fin 2 ⊕ Fin 2 → K,
      polar (quadPlus 5 K) (emb12 w) (emb34 h) = 0 := fun h => polar_emb12_emb34 w h
  have hz12 : res12 z = z' (.inl 0) • u + z' (.inr 0) • w := by
    rw [hzdef, res12_psi]
    simp
  have hzE : z ∈ coneSpace σ γ := by
    refine mem_coneSpace_of_row hσ h3 h4 ?_ ?_ ?_ ?_
    · rw [hzdef]; simp
    · rw [hzdef]; simp
    · rw [hz12, polar_add_left, polar_smul_left, polar_smul_left, huv, hwv]
      simp
    · rw [hz12, flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left, hhuv, hhwv]
      simp
  have hzQ : quadPlus 5 K z = 0 := by
    rw [hzdef, quadPlus_psi hUQ hWQ hUW hUE hWE, hz'Q]
  have hu' : dFlip σ (emb12 u) = emb12 u := by rw [dFlip_emb12, hu]
  have hw' : dFlip σ (emb12 w) = emb12 w := by rw [dFlip_emb12, hw]
  have hdz : dFlip σ z = psi (emb12 u) (emb12 w) (dFlipTw σ z') := by
    rw [hzdef]
    exact dFlip_psi hu' hw' z'
  have hzH : flipHerm σ z z ≠ 0 := by
    rw [flipHerm, hdz, polar_psi_psi hUQ hWQ hUW hUE hWE]
    exact hz'H
  have hxsplit : x = emb12 (res12 x) + emb34 (res34 x) := eq_emb12_add_emb34 x hxl0 hxr0
  have hpol_xz : polar (quadPlus 5 K) x z = 0 := by
    rw [hzdef, polar_psi_of_row hxsplit hα.symm hβ.symm z']
    rw [← polar_three_chartVec α β (res34 x) z']
    exact hxz'
  have hfl_xz : flipHerm σ x z = 0 := by
    rw [flipHerm, hdz, polar_psi_of_row hxsplit hα.symm hβ.symm (dFlipTw σ z')]
    rw [← polar_three_chartVec α β (res34 x) (dFlipTw σ z')]
    exact hxz'd
  have hzero : (z (.inl 4) = 0 ∧ z (.inr 4) = 0) ∨
      (z (.inl 3) = 0 ∧ z (.inr 3) = 0) := by
    rcases hz'pair with h2 | h1
    · exact Or.inl ⟨by rw [hzdef]; simpa using h2.1, by rw [hzdef]; simpa using h2.2⟩
    · exact Or.inr ⟨by rw [hzdef]; simpa using h1.1, by rw [hzdef]; simpa using h1.2⟩
  exact ⟨z, hzE, hzQ, hzH, hpol_xz, hfl_xz, hzero⟩

private theorem reach_std_of_hyperbolic [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {γ x : Fin 5 ⊕ Fin 5 → K} {p : FlipPt σ 5} (hpval : p.1 = K ∙ x)
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (hxE : x ∈ coneSpace σ γ) (hxQ : quadPlus 5 K x = 0)
    (hxH : flipHerm σ x x ≠ 0)
    {u w : Fin 2 ⊕ Fin 2 → K} (hu : dFlip σ u = u) (hw : dFlip σ w = w)
    (hQu : quadPlus 2 K u = 0) (hQw : quadPlus 2 K w = 0)
    (huw : polar (quadPlus 2 K) u w = 1)
    (huv : polar (quadPlus 2 K) u (rowVec γ) = 0)
    (hhuv : flipHerm σ u (rowVec γ) = 0)
    (hwv : polar (quadPlus 2 K) w (rowVec γ) = 0)
    (hhwv : flipHerm σ w (rowVec γ) = 0)
    (hR : ∀ y : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) y (rowVec γ) = 0 →
      flipHerm σ y (rowVec γ) = 0 → polar (quadPlus 2 K) y u = 0 →
      polar (quadPlus 2 K) y w = 0 → quadPlus 2 K y = 0) :
    Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointFour σ) ∨
      Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointThree σ) := by
  obtain ⟨z, hzE, hzQ, hzH, hpol_xz, hfl_xz, hzero⟩ :=
    exists_orthogonal_point_of_hyperbolic hσ hK h3 h4 hxE hxQ hxH hu hw hQu hQw huw
      huv hhuv hwv hhwv hR
  have hz0 : z ≠ 0 := by
    intro h
    apply hzH
    rw [h]
    simp
  let q : FlipPt σ 5 := ⟨K ∙ z, (isFlipflopPt_span_singleton_iff hz0).mpr ⟨hzQ, hzH⟩⟩
  have hqval : q.1 = K ∙ z := rfl
  have hpE : p.1 ≤ coneSpace σ γ := by
    rw [hpval]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxE
  have hqE : q.1 ≤ coneSpace σ γ := (Submodule.span_singleton_le_iff_mem _ _).mpr hzE
  have hpq : p.1 ≤ qPerp 5 K q.1 := by
    rw [hpval, hqval, Submodule.span_singleton_le_iff_mem, mem_qPerp]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [polar_smul_left, polar_comm, hpol_xz, smul_zero]
  have hph : p.1 ≤ flipOrth σ q.1 := by
    rw [hpval, hqval, Submodule.span_singleton_le_iff_mem, mem_flipOrth]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hzx : flipHerm σ z x = 0 := (flipHerm_eq_zero_iff (n := 5) hσ.invol).mp hfl_xz
    rw [flipHerm_smul_left, hzx, mul_zero]
  have hstep1 : ConeStep σ 4 (coneSpace σ γ) p q :=
    coneStep_of_orth_point hσ.invol hpE hqE hpq hph
  rcases hzero with h4' | h3'
  · exact Or.inl ((Relation.ReflTransGen.single hstep1).tail
      (coneStep_to_stdPointFour hσ.invol hqval h3 h4 hσ hqE h4'))
  · exact Or.inr ((Relation.ReflTransGen.single hstep1).tail
      (coneStep_to_stdPointThree hσ.invol hqval h3 h4 hσ hqE h3'))

end cone_reduction


section cone_connectivity

private theorem coneConnected_coneSpace [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {γ : Fin 5 ⊕ Fin 5 → K} (hγ : IsFlipflopPt σ (K ∙ γ))
    (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0) (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0)
    (h0 : γ (.inl 0) ≠ 0 ∨ γ (.inr 0) ≠ 0)
    (h12 : ¬ (γ (.inl 1) = 0 ∧ γ (.inr 1) = 0 ∧ γ (.inl 2) = 0 ∧ γ (.inr 2) = 0)) :
    ConeConnected σ 4 (coneSpace σ γ) := by
  classical
  have hrow := row_condition hσ hK hγ h3 h4 h0
  have hsplit := singular_or_exists_fixed_hyperbolic_of_card_eq_four hσ hK
    (rowVec_ne_zero h12) hrow
  have hreach : ∀ p : FlipPt σ 5, p.1 ≤ coneSpace σ γ →
      Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointFour σ) ∨
        Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) p (stdPointThree σ) := by
    intro p hpE
    obtain ⟨x, hpval, hxQ, hxH⟩ := p.2.exists_eq_span
    have hxmem : x ∈ p.1 := by
      rw [hpval]
      exact Submodule.mem_span_singleton_self x
    have hxE : x ∈ coneSpace σ γ := hpE hxmem
    rcases hsplit with hsing | hspec
    · exact reach_std_of_singular hσ hK hpval h3 h4 hxE hxQ hxH hsing
    · obtain ⟨u, w, hu, hw, hQu, hQw, huw, huv, hhuv, hwv, hhwv, hR⟩ := hspec
      exact reach_std_of_hyperbolic hσ hK hpval h3 h4 hxE hxQ hxH hu hw hQu hQw huw
        huv hhuv hwv hhwv hR
  have h34 : ConeStep σ 4 (coneSpace σ γ) (stdPointThree σ) (stdPointFour σ) :=
    coneStep_stdPointThree_stdPointFour hσ.invol hσ h3 h4
  have h43 : ConeStep σ 4 (coneSpace σ γ) (stdPointFour σ) (stdPointThree σ) :=
    ConeStep.symm h34
  have hrev : ∀ {a b : FlipPt σ 5},
      Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) a b →
        Relation.ReflTransGen (ConeStep σ 4 (coneSpace σ γ)) b a := by
    intro a b h
    have : Std.Symm (ConeStep σ 4 (coneSpace σ γ)) :=
      ⟨fun a b hab => ConeStep.symm hab⟩
    exact Std.Symm.symm a b h
  intro y y' hy hy'
  rcases hreach y hy with hy4 | hy3
  · rcases hreach y' hy' with hy'4 | hy'3
    · exact hy4.trans (hrev hy'4)
    · exact hy4.trans ((Relation.ReflTransGen.single h43).trans (hrev hy'3))
  · rcases hreach y' hy' with hy'4 | hy'3
    · exact hy3.trans ((Relation.ReflTransGen.single h34).trans (hrev hy'4))
    · exact hy3.trans (hrev hy'3)

end cone_connectivity

theorem coneConnected_five_coord_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) {γ : Fin (4 + 1) ⊕ Fin (4 + 1) → K}
    (hγ : IsFlipflopPt σ (K ∙ γ)) (h3 : γ (.inl 3) = 0 ∧ γ (.inr 3) = 0)
    (h4 : γ (.inl 4) = 0 ∧ γ (.inr 4) = 0) (h0 : γ (.inl 0) ≠ 0 ∨ γ (.inr 0) ≠ 0)
    (h12 : ¬ (γ (.inl 1) = 0 ∧ γ (.inr 1) = 0 ∧ γ (.inl 2) = 0 ∧ γ (.inr 2) = 0)) :
    ConeConnected σ 4 (qPerp (4 + 1) K ((K ∙ stdE 0) ⊔ K ∙ γ) ⊓
      flipOrth σ ((K ∙ stdE 0) ⊔ K ∙ γ)) := by
  show ConeConnected σ 4 (coneSpace σ γ)
  exact coneConnected_coneSpace hσ hK hγ h3 h4 h0 h12

end CFSG.ClassicalInvolution.PhanDn
