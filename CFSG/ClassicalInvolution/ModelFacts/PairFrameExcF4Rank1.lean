module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Descent

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Commute

variable {F : Type} [Field F]

theorem pinnedX_commute_of_iform_eq_zero_F4 {α β : Fin (Tag.rank .F4) → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (hl : iform β β = 4) (h : iform α β = 0) (a b : F) :
    pinnedX .F4 F α a * pinnedX .F4 F β b = pinnedX .F4 F β b * pinnedX .F4 F α a := by
  have hα2 := iform_self_isRoot_F4 hα
  have hne : α ≠ β := fun e => by subst e; omega
  have hne' : α ≠ -β := fun e => by
    have h1 : iform (-β) β = -4 := by
      rw [show (-β : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • β by simp, iform_smul_left, hl]
      norm_num
    rw [e] at h
    omega
  have hnot : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot .F4 (a • α + b • β) := by
    intro a b ha hb hr
    have h1 := iform_self_isRoot_F4 hr
    rw [iform_nsmul_add_nsmul, hl, h] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    rcases hα2 with h2 | h2 <;> rw [h2] at h1 <;> rcases h1 with h1 | h1 <;> nlinarith
  exact commute_of_forall_not_isRoot hα hβ hne hne' hnot F _
    (Subgroup.subset_closure ⟨a, rfl⟩) _ (Subgroup.subset_closure ⟨b, rfl⟩)

theorem iform_single_eq_zero_of_mem_F4 {j : Fin (Tag.rank .F4)} (hj : j ∈ JF4) :
    iform (Pi.single j 1) thetaF4 = 0 := by
  rw [iform_comm]
  exact iform_thetaF4_single_of_mem hj

theorem iform_neg_single_eq_zero_of_mem_F4 {j : Fin (Tag.rank .F4)} (hj : j ∈ JF4) :
    iform (-Pi.single j 1) thetaF4 = 0 := by
  rw [show (-Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
    iform_smul_left, iform_single_eq_zero_of_mem_F4 hj, mul_zero]

theorem isRoot_neg_thetaF4 : IsRoot .F4 (-thetaF4) := IsRoot.neg isRoot_thetaF4

theorem iform_neg_thetaF4_self : iform (-thetaF4) (-thetaF4) = 4 := by
  rw [show (-thetaF4 : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • thetaF4 by simp, iform_smul_left,
    iform_smul_right, iform_thetaF4_self]
  norm_num

end Commute

section Levi

variable {F : Type} [Field F]

theorem conj_rootSL2_thetaF4_of_commute {g : ModGL .F4 F}
    (hu : ∀ a : F, g * pinnedX .F4 F thetaF4 a = pinnedX .F4 F thetaF4 a * g)
    (hv : ∀ a : F, g * pinnedX .F4 F (-thetaF4) a = pinnedX .F4 F (-thetaF4) a * g) :
    (∀ z : F, g * rootSL2 .F4 F thetaF4 (uSL z) * g⁻¹ = rootSL2 .F4 F thetaF4 (uSL z)) ∧
      ∀ z : F, g * rootSL2 .F4 F thetaF4 (vSL z) * g⁻¹ = rootSL2 .F4 F thetaF4 (vSL z) := by
  obtain ⟨η, -, hη⟩ := exists_rootSL2_vSL_eq (K := F) isRoot_thetaF4
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [rootSL2_uSL_eq, mul_inv_eq_iff_eq_mul]
    exact hu _
  · rw [hη, mul_inv_eq_iff_eq_mul]
    exact hv _

theorem exists_levi_conj_rootSL2_thetaF4 {n : ModGL .F4 F} (hn : n ∈ parabolicLevi .F4 F JF4) :
    ∃ l : Fˣ,
      (∀ z : F, n * rootSL2 .F4 F thetaF4 (uSL z) * n⁻¹ =
        rootSL2 .F4 F thetaF4 (uSL ((l : F) * z))) ∧
      ∀ z : F, n * rootSL2 .F4 F thetaF4 (vSL z) * n⁻¹ =
        rootSL2 .F4 F thetaF4 (vSL (((l⁻¹ : Fˣ) : F) * z)) := by
  classical
  have hcl : parabolicLevi .F4 F JF4 = Subgroup.closure
      (Set.range (fun p : Fin (Tag.rank .F4) × Fˣ => torusElt .F4 F p.1 p.2) ∪
        {g | ∃ j ∈ JF4, ∃ c : F, g = xUnit .F4 F j c ∨ g = yUnit .F4 F j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hcl] at hn
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨rootChar (fun j => t ^ Tag.cartan .F4 i j) thetaF4, fun z => ?_, fun z => ?_⟩
      · have e := torusElt_eq_rootDiagUnit (τ := .F4) (K := F) i t
        show torusElt .F4 F i t * _ * (torusElt .F4 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .F4 i j) isRoot_thetaF4 z).1
      · have e := torusElt_eq_rootDiagUnit (τ := .F4) (K := F) i t
        show torusElt .F4 F i t * _ * (torusElt .F4 F i t)⁻¹ = _
        rw [e]
        exact (rootDiagUnit_conj_rootSL2 (fun j => t ^ Tag.cartan .F4 i j) isRoot_thetaF4 z).2
    · have hxu : xUnit .F4 F j c = pinnedX .F4 F (Pi.single j 1) c := (pinnedX_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaF4_of_commute (g := xUnit .F4 F j c)
        (fun a => by
          rw [hxu]
          exact pinnedX_commute_of_iform_eq_zero_F4 (isRoot_single _ j) isRoot_thetaF4
            iform_thetaF4_self (iform_single_eq_zero_of_mem_F4 hj) _ _)
        (fun a => by
          rw [hxu]
          refine pinnedX_commute_of_iform_eq_zero_F4 (isRoot_single _ j) isRoot_neg_thetaF4
            iform_neg_thetaF4_self ?_ _ _
          rw [show (-thetaF4 : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • thetaF4 by simp,
            iform_smul_right, iform_single_eq_zero_of_mem_F4 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
    · have hyu : yUnit .F4 F j c = pinnedX .F4 F (-Pi.single j 1) c :=
        (pinnedX_neg_single _ F j c).symm
      obtain ⟨hu, hv⟩ := conj_rootSL2_thetaF4_of_commute (g := yUnit .F4 F j c)
        (fun a => by
          rw [hyu]
          exact pinnedX_commute_of_iform_eq_zero_F4 (IsRoot.neg (isRoot_single _ j))
            isRoot_thetaF4 iform_thetaF4_self (iform_neg_single_eq_zero_of_mem_F4 hj) _ _)
        (fun a => by
          rw [hyu]
          refine pinnedX_commute_of_iform_eq_zero_F4 (IsRoot.neg (isRoot_single _ j))
            isRoot_neg_thetaF4 iform_neg_thetaF4_self ?_ _ _
          rw [show (-thetaF4 : Fin (Tag.rank .F4) → ℤ) = (-1 : ℤ) • thetaF4 by simp,
            iform_smul_right, iform_neg_single_eq_zero_of_mem_F4 hj, mul_zero])
      exact ⟨1, fun z => by simpa using hu z, fun z => by simpa using hv z⟩
  | one => exact ⟨1, fun z => by simp, fun z => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨l₁, hu₁, hv₁⟩ := ihg
    obtain ⟨l₂, hu₂, hv₂⟩ := ihh
    refine ⟨l₁ * l₂, fun z => ?_, fun z => ?_⟩
    · calc g * h * rootSL2 .F4 F thetaF4 (uSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .F4 F thetaF4 (uSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hu₂, hu₁, Units.val_mul, mul_assoc]
    · calc g * h * rootSL2 .F4 F thetaF4 (vSL z) * (g * h)⁻¹ =
          g * (h * rootSL2 .F4 F thetaF4 (vSL z) * h⁻¹) * g⁻¹ := by group
        _ = _ := by rw [hv₂, hv₁, mul_inv, Units.val_mul, mul_assoc]
  | inv g _ ih =>
    obtain ⟨l, hu, hv⟩ := ih
    refine ⟨l⁻¹, fun z => ?_, fun z => ?_⟩
    · have h1 := hu (((l⁻¹ : Fˣ) : F) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .F4 F thetaF4 (uSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .F4 F thetaF4 (uSL (((l⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group
    · have h1 := hv (((l⁻¹ : Fˣ)⁻¹ : Fˣ) * z)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      calc g⁻¹ * rootSL2 .F4 F thetaF4 (vSL z) * g⁻¹⁻¹ =
          g⁻¹ * (g * rootSL2 .F4 F thetaF4 (vSL ((((l⁻¹ : Fˣ)⁻¹ : Fˣ) : F) * z)) * g⁻¹) * g := by
            rw [h1, inv_inv]
        _ = _ := by group

theorem exists_levi_conj_rootSL2_eq_F4 {n : ModGL .F4 F} (hn : n ∈ parabolicLevi .F4 F JF4)
    (A : SL2 F) : ∃ A' : SL2 F, n * rootSL2 .F4 F thetaF4 A * n⁻¹ = rootSL2 .F4 F thetaF4 A' := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaF4 hn
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

theorem rootTorusSL2_thetaF4 (c : Fˣ) :
    rootTorusSL2 .F4 F thetaF4 c = rootDiagUnit .F4 (corootDiagF4 thetaF4 c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .F4 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .F4 a : ModGL .F4 F) : Module.End F (RootModule .F4 F))
      (rootVec .F4 F (Pi.single i 1))) = ((a i : Fˣ) : F) • rootVec .F4 F (Pi.single i 1) := by
    change rootDiag a (rootVec .F4 F (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .F4 i), hs]
  rw [h2] at h1
  have hne : rootVec .F4 F (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .F4 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective F hne h1
  have h4 : 2 * iform thetaF4 (Pi.single i 1) / iform thetaF4 thetaF4 =
      iform thetaF4 (Pi.single i 1) / 2 := by
    rw [iform_thetaF4_self]
    omega
  rw [h4] at h3
  exact Units.ext h3

end Torus

end CFSG.ClassicalInvolution.ModelFacts.Levi
