module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
  CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Lang.E6Descent

section Certs

variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

theorem eBarTuple_apply {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (j : Fin Tag.E6.rank) :
    eBarTuple ω j = if j = 3 then ω ^ 2 else 1 := by
  have h3z : ω ^ (3 : ℤ) = 1 := by simpa using hω3
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ' ω 2, show (2:ℕ) + 1 = 3 by norm_num, hω3]
  have hz2 : (ω ^ 2 : Ωˣ) = ω ^ (2 : ℤ) := (_root_.zpow_natCast ω 2).symm
  have hz : ∀ k : ℤ, (ω ^ 2 : Ωˣ) ^ k = ω ^ (2 * k) := by
    intro k
    rw [hz2, ← _root_.zpow_mul]
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [eBarTuple_eq hω3, Pi.mul_apply]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Tag.E6.cartan 4 (0 : Fin Tag.E6.rank) = 0 by decide,
      show Tag.E6.cartan 5 (0 : Fin Tag.E6.rank) = 0 by decide]
    simp
  · rw [show Tag.E6.cartan 4 (1 : Fin Tag.E6.rank) = 0 by decide,
      show Tag.E6.cartan 5 (1 : Fin Tag.E6.rank) = 0 by decide]
    simp
  · rw [show Tag.E6.cartan 4 (2 : Fin Tag.E6.rank) = 0 by decide,
      show Tag.E6.cartan 5 (2 : Fin Tag.E6.rank) = 0 by decide]
    simp
  · rw [show Tag.E6.cartan 4 (3 : Fin Tag.E6.rank) = -1 by decide,
      show Tag.E6.cartan 5 (3 : Fin Tag.E6.rank) = 0 by decide, _root_.zpow_zero, mul_one,
      _root_.zpow_neg, _root_.zpow_one]
    simpa using hωinv
  · rw [show Tag.E6.cartan 4 (4 : Fin Tag.E6.rank) = 2 by decide,
      show Tag.E6.cartan 5 (4 : Fin Tag.E6.rank) = -1 by decide, hz, ← _root_.zpow_add,
      show (2 : ℤ) + 2 * (-1) = 0 by norm_num, _root_.zpow_zero]
    simp
  · rw [show Tag.E6.cartan 4 (5 : Fin Tag.E6.rank) = -1 by decide,
      show Tag.E6.cartan 5 (5 : Fin Tag.E6.rank) = 2 by decide, hz, ← _root_.zpow_add,
      show (-1 : ℤ) + 2 * 2 = 3 by norm_num]
    rw [h3z]
    simp

theorem rootChar_eBarTuple_eq_one_iff {ω : Ωˣ} (hω : orderOf ω = 3)
    (α : Fin Tag.E6.rank → ℤ) :
    rootChar (eBarTuple ω) α = 1 ↔ (3 : ℤ) ∣ α (3 : Fin Tag.E6.rank) := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω3z : ω ^ (3 : ℤ) = 1 := by simpa using hω3
  have hprod : rootChar (eBarTuple ω) α = (ω ^ 2) ^ α (3 : Fin Tag.E6.rank) := by
    rw [rootChar, Finset.prod_eq_single (3 : Fin Tag.E6.rank)]
    · rw [eBarTuple_apply hω3]
      simp
    · intro b _ hb
      rw [eBarTuple_apply hω3]
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hprod, ← orderOf_dvd_iff_zpow_eq_one (x := ω ^ 2) (i := α (3 : Fin Tag.E6.rank)),
    orderOf_sq_of_orderOf_eq_three hω]
  norm_num

private theorem kernel_roots_orthogonal_check :
    ∀ α ∈ rootFinset Tag.E6, (3 : ℤ) ∣ α (3 : Fin Tag.E6.rank) →
      (∃ i, i ≠ e6Index 4 ∧ i ≠ e6Index 5 ∧ α i ≠ 0) →
      iform α (Pi.single (e6Index 4) 1) = 0 ∧
      iform α (Pi.single (e6Index 5) 1) = 0 ∧
      (α + Pi.single (e6Index 4) 1) ∉ rootFinset Tag.E6 ∧
      (α + (-Pi.single (e6Index 4) 1)) ∉ rootFinset Tag.E6 ∧
      (α + Pi.single (e6Index 5) 1) ∉ rootFinset Tag.E6 ∧
      (α + (-Pi.single (e6Index 5) 1)) ∉ rootFinset Tag.E6 := by
  decide +kernel

theorem parabolicRoots_support56_subset_kernelRoots {ω : Ωˣ} :
    parabolicRoots Tag.E6 support56 ⊆ rootCharKernel (eBarTuple ω) := by
  rintro α ⟨hα, hsupp⟩
  exact ⟨hα, (rootChar_eBar_of_mem_support56 (ω := ω) ⟨hα, hsupp⟩)⟩

theorem torusGroup_le_normalizer_subsystemGroup (A : Set (Fin Tag.E6.rank)) :
    torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 Ω A : Set (ModGL Tag.E6 Ω)) := by
  have hconj : ∀ b : Fin Tag.E6.rank → Ωˣ, ∀ g ∈ subsystemGroup Tag.E6 Ω A,
      rootDiagUnit Tag.E6 b * g * (rootDiagUnit Tag.E6 b)⁻¹ ∈ subsystemGroup Tag.E6 Ω A := by
    intro b g hg
    have hle : subsystemGroup Tag.E6 Ω A ≤ (subsystemGroup Tag.E6 Ω A).comap
        (MulAut.conj (rootDiagUnit Tag.E6 b)).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, hi, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (root_diagonal_conjugation Tag.E6 Ω b).1 i c]
        exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (root_diagonal_conjugation Tag.E6 Ω b).2.1 i c]
        exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
    exact hle hg
  have hb_inv : ∀ b : Fin Tag.E6.rank → Ωˣ, rootDiagUnit Tag.E6 b⁻¹ = (rootDiagUnit Tag.E6 b)⁻¹ :=
    fun b => map_inv (rootDiagUnitHom Tag.E6 Ω) b
  intro h hh
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact hconj b g
  · intro hg
    have h1 := hconj b⁻¹ _ hg
    rw [hb_inv b] at h1
    rwa [show (rootDiagUnit Tag.E6 b)⁻¹ * (rootDiagUnit Tag.E6 b * g *
      (rootDiagUnit Tag.E6 b)⁻¹) * ((rootDiagUnit Tag.E6 b)⁻¹)⁻¹ = g by group] at h1

theorem toralRootGroup_le_normalizer_subsystemGroup56 {ω : Ωˣ} (hω : orderOf ω = 3) :
    toralRootGroup Tag.E6 Ω (eBarTuple ω) ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
  rw [toralRootGroup, sup_le_iff]
  refine ⟨torusGroup_le_normalizer_subsystemGroup support56, ?_⟩
  rw [rootSpan]
  refine iSup₂_le fun α hα => ?_
  by_cases hpar : α ∈ parabolicRoots Tag.E6 support56
  · have hle : rootSubgroup Tag.E6 Ω α ≤ subsystemGroup Tag.E6 Ω support56 := by
      rw [subsystemGroup_eq_rootSpan, rootSpan]
      exact le_iSup₂_of_le α hpar le_rfl
    exact hle.trans Subgroup.le_normalizer
  · have hout : ∃ i, i ≠ e6Index 4 ∧ i ≠ e6Index 5 ∧ α i ≠ 0 := by
      by_contra h
      refine hpar ⟨hα.1, fun i hi => ?_⟩
      have hi4 : i ≠ e6Index 4 := fun h' => hi ((mem_support56 i).2 (Or.inl h'))
      have hi5 : i ≠ e6Index 5 := fun h' => hi ((mem_support56 i).2 (Or.inr h'))
      by_contra hne
      exact h ⟨i, hi4, hi5, hne⟩
    obtain ⟨hif4, hif5, hn4, hn4', hn5, hn5'⟩ :=
      kernel_roots_orthogonal_check α (mem_rootFinset.2 hα.1)
        ((rootChar_eBarTuple_eq_one_iff hω α).1 hα.2) hout
    have hcommGen : ∀ x ∈ Set.range (pinnedX Tag.E6 Ω α),
        ∀ y ∈ {g : ModGL Tag.E6 Ω | ∃ j ∈ support56, ∃ c : Ω,
          g = xUnit Tag.E6 Ω j c ∨ g = yUnit Tag.E6 Ω j c}, x * y = y * x := by
      rintro _ ⟨c, rfl⟩ _ ⟨j, hj, d, rfl | rfl⟩
      · rw [← pinnedX_single]
        rcases (mem_support56 j).1 hj with rfl | rfl
        · exact pinnedX_commute_of_iform_eq_zero Ω hα.1 (IsRoot.basis _) hif4
            (fun h => hn4 (mem_rootFinset.2 h)) c d
        · exact pinnedX_commute_of_iform_eq_zero Ω hα.1 (IsRoot.basis _) hif5
            (fun h => hn5 (mem_rootFinset.2 h)) c d
      · rw [← pinnedX_neg_single]
        rcases (mem_support56 j).1 hj with rfl | rfl
        · refine pinnedX_commute_of_iform_eq_zero Ω hα.1 (IsRoot.neg (IsRoot.basis _)) ?_
            (fun h => hn4' (mem_rootFinset.2 h)) c d
          rw [iform_neg_right, hif4, neg_zero]
        · refine pinnedX_commute_of_iform_eq_zero Ω hα.1 (IsRoot.neg (IsRoot.basis _)) ?_
            (fun h => hn5' (mem_rootFinset.2 h)) c d
          rw [iform_neg_right, hif5, neg_zero]
    have hcent : rootSubgroup Tag.E6 Ω α ≤
        Subgroup.centralizer (subsystemGroup Tag.E6 Ω support56 : Set (ModGL Tag.E6 Ω)) := by
      have hAB := closure_commute hcommGen
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hAB x hx y hy).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)

end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
