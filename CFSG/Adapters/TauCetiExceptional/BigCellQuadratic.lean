module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.ChevalleyPinned
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def stringsLeTwoAt (τ : Tag) (i : Fin τ.rank) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (τ.stringData.up k i ≤ 2 ∧ τ.stringData.down k i ≤ 2)

theorem stringsLeTwoAt_G2_zero : stringsLeTwoAt .G2 ⟨0, by decide⟩ = true := by
  decide +kernel

theorem not_isRoot_add_three_smul_of
    {i : Fin τ.rank} (h : stringsLeTwoAt τ i = true)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    ¬IsRoot τ (α + (3 : ℤ) • Pi.single i 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  simp only [stringsLeTwoAt, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hu, -⟩ := h k hk
  have hs := (StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk i
    h₁ h₂).2
  intro hr
  have := ((hs 3).1 hr).2
  omega

theorem xCoeff_three_eq_zero_of
    {R : Type*} [CommRing R] {i : Fin τ.rank}
    (h : stringsLeTwoAt τ i = true) : xCoeff τ R i 3 = 0 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rcases b with j | ⟨α, hα⟩
  · exact (xCoeff_hVec i j 3).trans (by simp)
  · rw [← rootVec_eq_single_of_isRoot' hα]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [xCoeff_rootVec_single]
      simp
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [xCoeff_rootVec_neg_single]
      simp
    rw [xCoeff_rootVec_of_ne i 3 hα h₁ h₂, Nat.cast_ofNat,
      rootVec_eq_zero_of_not_isRoot' (not_isRoot_add_three_smul_of h hα h₁ h₂), smul_zero]

@[expose] def HasQuadraticNode (τ : Tag) : Prop :=
  ∃ i : Fin τ.rank, ∀ (R : Type) [CommRing R], xCoeff τ R i 3 = 0

theorem hasQuadraticNode_of_ne_G2
    (hτ : τ ≠ .G2) : HasQuadraticNode τ :=
  ⟨⟨0, τ.rank_pos⟩, fun _ _ => xCoeff_three_eq_zero hτ _⟩

theorem hasQuadraticNode_G2 :
    HasQuadraticNode .G2 :=
  ⟨⟨0, by decide⟩, fun _ _ => xCoeff_three_eq_zero_of stringsLeTwoAt_G2_zero⟩

end CFSG.TauCetiBridge.BigCell
