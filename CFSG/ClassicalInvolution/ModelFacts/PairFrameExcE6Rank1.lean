module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Descent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Commute

variable {F : Type} [Field F]

theorem pinnedX_commute_of_iform_eq_zero_E6 {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (h : iform α β = 0) (a b : F) :
    pinnedX .E6 F α a * pinnedX .E6 F β b = pinnedX .E6 F β b * pinnedX .E6 F α a := by
  have hα2 := iform_self_isRoot_E6 hα
  have hβ2 := iform_self_isRoot_E6 hβ
  have hne : α ≠ β := fun e => by subst e; omega
  have hne' : α ≠ -β := fun e => by
    have h1 : iform (-β) β = -2 := by
      rw [show (-β : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • β by simp, iform_smul_left, hβ2]
      norm_num
    rw [e] at h
    omega
  have hnot : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot .E6 (a • α + b • β) := by
    intro a b ha hb hr
    have h1 := iform_self_isRoot_E6 hr
    rw [iform_nsmul_add_nsmul, hα2, hβ2, h] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  exact commute_of_forall_not_isRoot hα hβ hne hne' hnot F _
    (Subgroup.subset_closure ⟨a, rfl⟩) _ (Subgroup.subset_closure ⟨b, rfl⟩)

theorem iform_single_eq_zero_of_mem_E6 {j : Fin (Tag.rank .E6)} (hj : j ∈ JE6) :
    iform (Pi.single j 1) thetaE6 = 0 := by
  rw [iform_comm]
  exact iform_thetaE6_single_of_mem hj

theorem iform_neg_single_eq_zero_of_mem_E6 {j : Fin (Tag.rank .E6)} (hj : j ∈ JE6) :
    iform (-Pi.single j 1) thetaE6 = 0 := by
  rw [show (-Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
    iform_smul_left, iform_single_eq_zero_of_mem_E6 hj, mul_zero]

end Commute

section Levi

variable {F : Type} [Field F]

theorem conj_rootSL2_thetaE6_of_commute {g : ModGL .E6 F}
    (hu : ∀ a : F, g * pinnedX .E6 F thetaE6 a = pinnedX .E6 F thetaE6 a * g)
    (hv : ∀ a : F, g * pinnedX .E6 F (-thetaE6) a = pinnedX .E6 F (-thetaE6) a * g) :
    (∀ z : F, g * rootSL2 .E6 F thetaE6 (uSL z) * g⁻¹ = rootSL2 .E6 F thetaE6 (uSL z)) ∧
      ∀ z : F, g * rootSL2 .E6 F thetaE6 (vSL z) * g⁻¹ = rootSL2 .E6 F thetaE6 (vSL z) := by
  obtain ⟨η, -, hη⟩ := exists_rootSL2_vSL_eq (K := F) isRoot_thetaE6
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [rootSL2_uSL_eq, mul_inv_eq_iff_eq_mul]
    exact hu _
  · rw [hη, mul_inv_eq_iff_eq_mul]
    exact hv _

theorem exists_levi_conj_rootSL2_thetaE6 {n : ModGL .E6 F} (hn : n ∈ parabolicLevi .E6 F JE6) :
    ∃ l : Fˣ,
      (∀ z : F, n * rootSL2 .E6 F thetaE6 (uSL z) * n⁻¹ =
        rootSL2 .E6 F thetaE6 (uSL ((l : F) * z))) ∧
      ∀ z : F, n * rootSL2 .E6 F thetaE6 (vSL z) * n⁻¹ =
        rootSL2 .E6 F thetaE6 (vSL (((l⁻¹ : Fˣ) : F) * z)) := by
  classical
  have hcl : parabolicLevi .E6 F JE6 = Subgroup.closure
      (Set.range (fun p : Fin (Tag.rank .E6) × Fˣ => torusElt .E6 F p.1 p.2) ∪
        {g | ∃ j ∈ JE6, ∃ c : F, g = xUnit .E6 F j c ∨ g = yUnit .E6 F j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hcl] at hn
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨rootChar (fun j => t ^ Tag.cartan .E6 i j) thetaE6, fun z => ?_, fun z => ?_⟩
      · have e := torusElt_eq_rootDiagUnit (τ := .E6) (K := F) i t
        show torusElt .E6 F i t * _ * (torusElt .E6 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E6 i j) isRoot_thetaE6 z).1
      · have e := torusElt_eq_rootDiagUnit (τ := .E6) (K := F) i t
        show torusElt .E6 F i t * _ * (torusElt .E6 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E6 i j) isRoot_thetaE6 z).2
    · have hxu : xUnit .E6 F j c = pinnedX .E6 F (Pi.single j 1) c := (pinnedX_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE6_of_commute (g := xUnit .E6 F j c)
        (fun a => by
          rw [hxu]
          exact pinnedX_commute_of_iform_eq_zero_E6 (isRoot_single _ j) isRoot_thetaE6
            (iform_single_eq_zero_of_mem_E6 hj) _ _)
        (fun a => by
          rw [hxu]
          refine pinnedX_commute_of_iform_eq_zero_E6 (isRoot_single _ j)
            (IsRoot.neg isRoot_thetaE6) ?_ _ _
          rw [show (-thetaE6 : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • thetaE6 by simp,
            iform_smul_right, iform_single_eq_zero_of_mem_E6 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
    · have hyu : yUnit .E6 F j c = pinnedX .E6 F (-Pi.single j 1) c :=
        (pinnedX_neg_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE6_of_commute (g := yUnit .E6 F j c)
        (fun a => by
          rw [hyu]
          exact pinnedX_commute_of_iform_eq_zero_E6 (IsRoot.neg (isRoot_single _ j))
            isRoot_thetaE6 (iform_neg_single_eq_zero_of_mem_E6 hj) _ _)
        (fun a => by
          rw [hyu]
          refine pinnedX_commute_of_iform_eq_zero_E6 (IsRoot.neg (isRoot_single _ j))
            (IsRoot.neg isRoot_thetaE6) ?_ _ _
          rw [show (-thetaE6 : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • thetaE6 by simp,
            iform_smul_right, iform_neg_single_eq_zero_of_mem_E6 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
  | one => exact ⟨1, fun z => by simp, fun z => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨l₁, hu₁, hv₁⟩ := ihg
    obtain ⟨l₂, hu₂, hv₂⟩ := ihh
    refine ⟨l₁ * l₂, fun z => ?_, fun z => ?_⟩
    · calc g * h * rootSL2 .E6 F thetaE6 (uSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E6 F thetaE6 (uSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hu₂, hu₁, Units.val_mul, mul_assoc]
    · calc g * h * rootSL2 .E6 F thetaE6 (vSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E6 F thetaE6 (vSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hv₂, hv₁, mul_inv, Units.val_mul, mul_assoc]
  | inv g _ ih =>
    obtain ⟨l, hu, hv⟩ := ih
    refine ⟨l⁻¹, fun z => ?_, fun z => ?_⟩
    · have h1 := hu (((l⁻¹ : Fˣ) : F) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E6 F thetaE6 (uSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E6 F thetaE6 (uSL (((l⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group
    · have h1 := hv (((l⁻¹ : Fˣ)⁻¹ : Fˣ) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E6 F thetaE6 (vSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E6 F thetaE6 (vSL ((((l⁻¹ : Fˣ)⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group

theorem exists_levi_conj_rootSL2_eq_E6 {n : ModGL .E6 F} (hn : n ∈ parabolicLevi .E6 F JE6)
    (A : SL2 F) : ∃ A' : SL2 F, n * rootSL2 .E6 F thetaE6 A * n⁻¹ = rootSL2 .E6 F thetaE6 A' := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE6 hn
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


section Torus

variable {F : Type} [Field F]

theorem rootTorusSL2_thetaE6 (c : Fˣ) :
    rootTorusSL2 .E6 F thetaE6 c = rootDiagUnit .E6 (thetaDiag thetaE6 c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E6 F isRoot_thetaE6
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E6 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E6 a : ModGL .E6 F) : Module.End F (RootModule .E6 F))
      (rootVec .E6 F (Pi.single i 1))) = ((a i : Fˣ) : F) • rootVec .E6 F (Pi.single i 1) := by
    change rootDiag a (rootVec .E6 F (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E6 i), hs]
  rw [h2] at h1
  have hne : rootVec .E6 F (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E6 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective F hne h1
  have h4 : 2 * iform thetaE6 (Pi.single i 1) / iform thetaE6 thetaE6 =
      iform thetaE6 (Pi.single i 1) := by
    rw [iform_self_isRoot_E6 isRoot_thetaE6]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

end CFSG.ClassicalInvolution.ModelFacts.Levi
