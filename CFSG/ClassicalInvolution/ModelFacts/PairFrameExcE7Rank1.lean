module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Descent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Commute

variable {F : Type} [Field F]

theorem pinnedX_commute_of_iform_eq_zero_E7 {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α)
    (hβ : IsRoot .E7 β) (h : iform α β = 0) (a b : F) :
    pinnedX .E7 F α a * pinnedX .E7 F β b = pinnedX .E7 F β b * pinnedX .E7 F α a := by
  have hα2 := iform_self_isRoot_E7 hα
  have hβ2 := iform_self_isRoot_E7 hβ
  have hne : α ≠ β := fun e => by subst e; omega
  have hne' : α ≠ -β := fun e => by
    have h1 : iform (-β) β = -2 := by
      rw [show (-β : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • β by simp, iform_smul_left, hβ2]
      norm_num
    rw [e] at h
    omega
  have hnot : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot .E7 (a • α + b • β) := by
    intro a b ha hb hr
    have h1 := iform_self_isRoot_E7 hr
    rw [iform_nsmul_add_nsmul, hα2, hβ2, h] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  exact commute_of_forall_not_isRoot hα hβ hne hne' hnot F _
    (Subgroup.subset_closure ⟨a, rfl⟩) _ (Subgroup.subset_closure ⟨b, rfl⟩)

theorem iform_single_eq_zero_of_mem_E7 {j : Fin (Tag.rank .E7)} (hj : j ∈ JE7) :
    iform (Pi.single j 1) thetaE7 = 0 := by
  rw [iform_comm]
  exact iform_thetaE7_single_of_mem hj

theorem iform_neg_single_eq_zero_of_mem_E7 {j : Fin (Tag.rank .E7)} (hj : j ∈ JE7) :
    iform (-Pi.single j 1) thetaE7 = 0 := by
  rw [show (-Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
    iform_smul_left, iform_single_eq_zero_of_mem_E7 hj, mul_zero]

end Commute

section Levi

variable {F : Type} [Field F]

theorem conj_rootSL2_thetaE7_of_commute {g : ModGL .E7 F}
    (hu : ∀ a : F, g * pinnedX .E7 F thetaE7 a = pinnedX .E7 F thetaE7 a * g)
    (hv : ∀ a : F, g * pinnedX .E7 F (-thetaE7) a = pinnedX .E7 F (-thetaE7) a * g) :
    (∀ z : F, g * rootSL2 .E7 F thetaE7 (uSL z) * g⁻¹ = rootSL2 .E7 F thetaE7 (uSL z)) ∧
      ∀ z : F, g * rootSL2 .E7 F thetaE7 (vSL z) * g⁻¹ = rootSL2 .E7 F thetaE7 (vSL z) := by
  obtain ⟨η, -, hη⟩ := exists_rootSL2_vSL_eq (K := F) isRoot_thetaE7
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [rootSL2_uSL_eq, mul_inv_eq_iff_eq_mul]
    exact hu _
  · rw [hη, mul_inv_eq_iff_eq_mul]
    exact hv _

theorem exists_levi_conj_rootSL2_thetaE7 {n : ModGL .E7 F} (hn : n ∈ parabolicLevi .E7 F JE7) :
    ∃ l : Fˣ,
      (∀ z : F, n * rootSL2 .E7 F thetaE7 (uSL z) * n⁻¹ =
        rootSL2 .E7 F thetaE7 (uSL ((l : F) * z))) ∧
      ∀ z : F, n * rootSL2 .E7 F thetaE7 (vSL z) * n⁻¹ =
        rootSL2 .E7 F thetaE7 (vSL (((l⁻¹ : Fˣ) : F) * z)) := by
  classical
  have hcl : parabolicLevi .E7 F JE7 = Subgroup.closure
      (Set.range (fun p : Fin (Tag.rank .E7) × Fˣ => torusElt .E7 F p.1 p.2) ∪
        {g | ∃ j ∈ JE7, ∃ c : F, g = xUnit .E7 F j c ∨ g = yUnit .E7 F j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hcl] at hn
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨rootChar (fun j => t ^ Tag.cartan .E7 i j) thetaE7, fun z => ?_, fun z => ?_⟩
      · have e := torusElt_eq_rootDiagUnit (τ := .E7) (K := F) i t
        show torusElt .E7 F i t * _ * (torusElt .E7 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E7 i j) isRoot_thetaE7 z).1
      · have e := torusElt_eq_rootDiagUnit (τ := .E7) (K := F) i t
        show torusElt .E7 F i t * _ * (torusElt .E7 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .E7 i j) isRoot_thetaE7 z).2
    · have hxu : xUnit .E7 F j c = pinnedX .E7 F (Pi.single j 1) c := (pinnedX_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE7_of_commute (g := xUnit .E7 F j c)
        (fun a => by
          rw [hxu]
          exact pinnedX_commute_of_iform_eq_zero_E7 (isRoot_single _ j) isRoot_thetaE7
            (iform_single_eq_zero_of_mem_E7 hj) _ _)
        (fun a => by
          rw [hxu]
          refine pinnedX_commute_of_iform_eq_zero_E7 (isRoot_single _ j)
            (IsRoot.neg isRoot_thetaE7) ?_ _ _
          rw [show (-thetaE7 : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • thetaE7 by simp,
            iform_smul_right, iform_single_eq_zero_of_mem_E7 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
    · have hyu : yUnit .E7 F j c = pinnedX .E7 F (-Pi.single j 1) c :=
        (pinnedX_neg_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaE7_of_commute (g := yUnit .E7 F j c)
        (fun a => by
          rw [hyu]
          exact pinnedX_commute_of_iform_eq_zero_E7 (IsRoot.neg (isRoot_single _ j))
            isRoot_thetaE7 (iform_neg_single_eq_zero_of_mem_E7 hj) _ _)
        (fun a => by
          rw [hyu]
          refine pinnedX_commute_of_iform_eq_zero_E7 (IsRoot.neg (isRoot_single _ j))
            (IsRoot.neg isRoot_thetaE7) ?_ _ _
          rw [show (-thetaE7 : Fin (Tag.rank .E7) → ℤ) = (-1 : ℤ) • thetaE7 by simp,
            iform_smul_right, iform_neg_single_eq_zero_of_mem_E7 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
  | one => exact ⟨1, fun z => by simp, fun z => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨l₁, hu₁, hv₁⟩ := ihg
    obtain ⟨l₂, hu₂, hv₂⟩ := ihh
    refine ⟨l₁ * l₂, fun z => ?_, fun z => ?_⟩
    · calc g * h * rootSL2 .E7 F thetaE7 (uSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E7 F thetaE7 (uSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hu₂, hu₁, Units.val_mul, mul_assoc]
    · calc g * h * rootSL2 .E7 F thetaE7 (vSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .E7 F thetaE7 (vSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hv₂, hv₁, mul_inv, Units.val_mul, mul_assoc]
  | inv g _ ih =>
    obtain ⟨l, hu, hv⟩ := ih
    refine ⟨l⁻¹, fun z => ?_, fun z => ?_⟩
    · have h1 := hu (((l⁻¹ : Fˣ) : F) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E7 F thetaE7 (uSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E7 F thetaE7 (uSL (((l⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group
    · have h1 := hv (((l⁻¹ : Fˣ)⁻¹ : Fˣ) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .E7 F thetaE7 (vSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .E7 F thetaE7 (vSL ((((l⁻¹ : Fˣ)⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group

theorem exists_levi_conj_rootSL2_eq_E7 {n : ModGL .E7 F} (hn : n ∈ parabolicLevi .E7 F JE7)
    (A : SL2 F) : ∃ A' : SL2 F, n * rootSL2 .E7 F thetaE7 A * n⁻¹ = rootSL2 .E7 F thetaE7 A' := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE7 hn
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

theorem rootTorusSL2_thetaE7 (c : Fˣ) :
    rootTorusSL2 .E7 F thetaE7 c = rootDiagUnit .E7 (thetaDiag thetaE7 c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E7 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E7 a : ModGL .E7 F) : Module.End F (RootModule .E7 F))
      (rootVec .E7 F (Pi.single i 1))) = ((a i : Fˣ) : F) • rootVec .E7 F (Pi.single i 1) := by
    change rootDiag a (rootVec .E7 F (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E7 i), hs]
  rw [h2] at h1
  have hne : rootVec .E7 F (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E7 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective F hne h1
  have h4 : 2 * iform thetaE7 (Pi.single i 1) / iform thetaE7 thetaE7 =
      iform thetaE7 (Pi.single i 1) := by
    rw [iform_self_isRoot_E7 isRoot_thetaE7]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

end CFSG.ClassicalInvolution.ModelFacts.Levi
