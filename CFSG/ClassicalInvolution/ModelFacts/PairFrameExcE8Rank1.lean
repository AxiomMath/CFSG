module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Descent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Commute

variable {F : Type} [Field F]

theorem pinnedX_commute_of_iform_eq_zero_E8 {α β : Fin (Tag.rank .E8) → ℤ} (hα : IsRoot .E8 α)
    (hβ : IsRoot .E8 β) (h : iform α β = 0) (a b : F) :
    pinnedX .E8 F α a * pinnedX .E8 F β b = pinnedX .E8 F β b * pinnedX .E8 F α a := by
  have hα2 := iform_self_isRoot_E8 hα
  have hβ2 := iform_self_isRoot_E8 hβ
  have hne : α ≠ β := fun e => by subst e; omega
  have hne' : α ≠ -β := fun e => by
    have h1 : iform (-β) β = -2 := by
      rw [show (-β : Fin (Tag.rank .E8) → ℤ) = (-1 : ℤ) • β by simp, iform_smul_left, hβ2]
      norm_num
    rw [e] at h
    omega
  have hnot : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot .E8 (a • α + b • β) := by
    intro a b ha hb hr
    have h1 := iform_self_isRoot_E8 hr
    rw [iform_nsmul_add_nsmul, hα2, hβ2, h] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  exact commute_of_forall_not_isRoot hα hβ hne hne' hnot F _
    (Subgroup.subset_closure ⟨a, rfl⟩) _ (Subgroup.subset_closure ⟨b, rfl⟩)

theorem iform_single_eq_zero_of_mem {j : Fin (Tag.rank .E8)} (hj : j ∈ JE8) :
    iform (Pi.single j 1) thetaE8 = 0 := by
  rw [iform_comm]
  exact iform_thetaE8_single_of_mem hj

theorem iform_neg_single_eq_zero_of_mem {j : Fin (Tag.rank .E8)} (hj : j ∈ JE8) :
    iform (-Pi.single j 1) thetaE8 = 0 := by
  rw [show (-Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
    iform_smul_left, iform_single_eq_zero_of_mem hj, mul_zero]

end Commute

section Levi

variable {F : Type} [Field F]

theorem conj_rootSL2_thetaE8_of_commute {g : ModGL .E8 F}
    (hu : ∀ a : F, g * pinnedX .E8 F thetaE8 a = pinnedX .E8 F thetaE8 a * g)
    (hv : ∀ a : F, g * pinnedX .E8 F (-thetaE8) a = pinnedX .E8 F (-thetaE8) a * g) :
    (∀ z : F, g * rootSL2 .E8 F thetaE8 (uSL z) * g⁻¹ = rootSL2 .E8 F thetaE8 (uSL z)) ∧
      ∀ z : F, g * rootSL2 .E8 F thetaE8 (vSL z) * g⁻¹ = rootSL2 .E8 F thetaE8 (vSL z) := by
  obtain ⟨η, -, hη⟩ := exists_rootSL2_vSL_eq (K := F) isRoot_thetaE8
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [rootSL2_uSL_eq, mul_inv_eq_iff_eq_mul]
    exact hu _
  · rw [hη, mul_inv_eq_iff_eq_mul]
    exact hv _

theorem exists_levi_conj_rootSL2_thetaE8 {n : ModGL .E8 F} (hn : n ∈ parabolicLevi .E8 F JE8) :
    ∃ l : Fˣ,
      (∀ z : F, n * rootSL2 .E8 F thetaE8 (uSL z) * n⁻¹ =
        rootSL2 .E8 F thetaE8 (uSL ((l : F) * z))) ∧
      ∀ z : F, n * rootSL2 .E8 F thetaE8 (vSL z) * n⁻¹ =
        rootSL2 .E8 F thetaE8 (vSL (((l⁻¹ : Fˣ) : F) * z)) := by
  classical
  have hcl : parabolicLevi .E8 F JE8 = Subgroup.closure
      (Set.range (fun p : Fin (Tag.rank .E8) × Fˣ => torusElt .E8 F p.1 p.2) ∪
        {g | ∃ j ∈ JE8, ∃ c : F, g = xUnit .E8 F j c ∨ g = yUnit .E8 F j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hcl] at hn
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨rootChar (fun j => t ^ Tag.cartan .E8 i j) thetaE8, fun z => ?_, fun z => ?_⟩
      · have e := torusElt_eq_rootDiagUnit (τ := .E8) (K := F) i t
        show torusElt .E8 F i t * _ * (torusElt .E8 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E8 i j) isRoot_thetaE8 z).1
      · have e := torusElt_eq_rootDiagUnit (τ := .E8) (K := F) i t
        show torusElt .E8 F i t * _ * (torusElt .E8 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E8 i j) isRoot_thetaE8 z).2
    · have hxu : xUnit .E8 F j c = pinnedX .E8 F (Pi.single j 1) c := (pinnedX_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE8_of_commute (g := xUnit .E8 F j c)
        (fun a => by
          rw [hxu]
          exact pinnedX_commute_of_iform_eq_zero_E8 (isRoot_single _ j) isRoot_thetaE8
            (iform_single_eq_zero_of_mem hj) _ _)
        (fun a => by
          rw [hxu]
          refine pinnedX_commute_of_iform_eq_zero_E8 (isRoot_single _ j)
            (IsRoot.neg isRoot_thetaE8) ?_ _ _
          rw [show (-thetaE8 : Fin (Tag.rank .E8) → ℤ) = (-1 : ℤ) • thetaE8 by simp,
            iform_smul_right, iform_single_eq_zero_of_mem hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
    · have hyu : yUnit .E8 F j c = pinnedX .E8 F (-Pi.single j 1) c :=
        (pinnedX_neg_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE8_of_commute (g := yUnit .E8 F j c)
        (fun a => by
          rw [hyu]
          exact pinnedX_commute_of_iform_eq_zero_E8 (IsRoot.neg (isRoot_single _ j))
            isRoot_thetaE8 (iform_neg_single_eq_zero_of_mem hj) _ _)
        (fun a => by
          rw [hyu]
          refine pinnedX_commute_of_iform_eq_zero_E8 (IsRoot.neg (isRoot_single _ j))
            (IsRoot.neg isRoot_thetaE8) ?_ _ _
          rw [show (-thetaE8 : Fin (Tag.rank .E8) → ℤ) = (-1 : ℤ) • thetaE8 by simp,
            iform_smul_right, iform_neg_single_eq_zero_of_mem hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
  | one => exact ⟨1, fun z => by simp, fun z => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨l₁, hu₁, hv₁⟩ := ihg
    obtain ⟨l₂, hu₂, hv₂⟩ := ihh
    refine ⟨l₁ * l₂, fun z => ?_, fun z => ?_⟩
    · calc g * h * rootSL2 .E8 F thetaE8 (uSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E8 F thetaE8 (uSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hu₂, hu₁, Units.val_mul, mul_assoc]
    · calc g * h * rootSL2 .E8 F thetaE8 (vSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E8 F thetaE8 (vSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hv₂, hv₁, mul_inv, Units.val_mul, mul_assoc]
  | inv g _ ih =>
    obtain ⟨l, hu, hv⟩ := ih
    refine ⟨l⁻¹, fun z => ?_, fun z => ?_⟩
    · have h1 := hu (((l⁻¹ : Fˣ) : F) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E8 F thetaE8 (uSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E8 F thetaE8 (uSL (((l⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group
    · have h1 := hv (((l⁻¹ : Fˣ)⁻¹ : Fˣ) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E8 F thetaE8 (vSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E8 F thetaE8 (vSL ((((l⁻¹ : Fˣ)⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group

theorem exists_levi_conj_rootSL2_eq {n : ModGL .E8 F} (hn : n ∈ parabolicLevi .E8 F JE8)
    (A : SL2 F) : ∃ A' : SL2 F, n * rootSL2 .E8 F thetaE8 A * n⁻¹ = rootSL2 .E8 F thetaE8 A' := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE8 hn
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨uSL ((l : F) * c), hu c⟩
    · exact ⟨vSL (((l⁻¹ : Fˣ) : F) * c), hv c⟩
  | one => exact ⟨1, by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨A₁, h₁⟩ := ihg
    obtain ⟨A₂, h₂⟩ := ihh
    refine ⟨A₁ * A₂, ?_⟩
    simp only [map_mul]
    rw [← h₁, ← h₂]
    group
  | inv g _ ih =>
    obtain ⟨A₁, h₁⟩ := ih
    refine ⟨A₁⁻¹, ?_⟩
    simp only [map_inv]
    rw [← h₁]
    group

end Levi

section SL2

variable {F : Type} [Field F]

theorem exists_eq_HSL_of_conj_uSL_vSL {A : SL2 F} {l : Fˣ}
    (hu : A * uSL (1 : F) = uSL (l : F) * A)
    (hv : A * vSL (1 : F) = vSL (((l⁻¹ : Fˣ)) : F) * A) : ∃ a : Fˣ, A = HSL a := by
  have det1 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  have e1 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have e3 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e1 e3
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at e1 e3
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e1
  have h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := e3
  have hd : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    simpa [h10, h01] using det1
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hd
  refine ⟨Units.mkOfMulEqOne _ _ hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, h10, h01, h11]

theorem eq_one_or_HSL_neg_one_of_forall_commute {A : SL2 F} (hA : ∀ B : SL2 F, A * B = B * A) :
    A = 1 ∨ A = HSL (-1) := by
  have det1 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  have e1 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) (hA (uSL 1))
  have e2 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) (hA (uSL 1))
  have e3 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) (hA (vSL 1))
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e1 e2 e3
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e1
  have h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := e3
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    rw [h01] at e2
    simp only [add_zero, zero_add] at e2
    exact e2.symm
  have hsq : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [h10, h01, h11] at det1
    simpa using det1
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01, h11, h]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HSL, h10, h01, h11, h]

end SL2

section Torus

variable {F : Type} [Field F]

theorem rootTorusSL2_thetaE8 (c : Fˣ) :
    rootTorusSL2 .E8 F thetaE8 c = rootDiagUnit .E8 (thetaDiag thetaE8 c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E8 F isRoot_thetaE8
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E8 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E8 a : ModGL .E8 F) : Module.End F (RootModule .E8 F))
      (rootVec .E8 F (Pi.single i 1))) = ((a i : Fˣ) : F) • rootVec .E8 F (Pi.single i 1) := by
    change rootDiag a (rootVec .E8 F (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E8 i), hs]
  rw [h2] at h1
  have hne : rootVec .E8 F (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E8 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective F hne h1
  have h4 : 2 * iform thetaE8 (Pi.single i 1) / iform thetaE8 thetaE8 =
      iform thetaE8 (Pi.single i 1) := by
    rw [iform_self_isRoot_E8 isRoot_thetaE8]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

end CFSG.ClassicalInvolution.ModelFacts.Levi
