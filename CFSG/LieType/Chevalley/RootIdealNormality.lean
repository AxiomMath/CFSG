module

public import CFSG.LieType.Chevalley.RootOps.RingComm
public import CFSG.LieType.Chevalley.PinnedBridge

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem rootSubgroup_eq_ringRootSubgroup
    (R : Type) [CommRing R] {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    rootSubgroup τ R α = (rootOperatorFamily τ).ringRootSubgroup R ⟨α, hα⟩ := by
  ext g
  rw [mem_rootSubgroup, RootOperatorFamily.mem_ringRootSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, ((rootOperatorFamily τ).pinnedX_eq_eltUnit R hα c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨((rootOperatorFamily τ).pinnedFamilySign α : R) * c, ?_⟩
    rw [(rootOperatorFamily τ).pinnedX_eq_eltUnit R hα, ← mul_assoc,
      (rootOperatorFamily τ).pinnedFamilySign_mul_self, one_mul]

theorem positive_root_ideal_normality
    (τ : Tag) (R : Type) [CommRing R]
    {J S : Set (Fin τ.rank → ℤ)} (hJS : J ⊆ S) (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ J) :
    rootSpan τ R J ≤ rootSpan τ R S ∧ ((rootSpan τ R J).subgroupOf (rootSpan τ R S)).Normal := by
  set F := rootOperatorFamily τ
  have hle : rootSpan τ R J ≤ rootSpan τ R S :=
    iSup₂_le fun β hβ => le_iSup₂_of_le β (hJS hβ) le_rfl
  have hroot_le : ∀ β ∈ J, rootSubgroup τ R β ≤ rootSpan τ R J := fun β hβ =>
    le_iSup₂_of_le β hβ le_rfl
  have key : ∀ α ∈ S, ∀ (c : R), ∀ β ∈ J, ∀ d : R,
      pinnedX τ R α c * pinnedX τ R β d * (pinnedX τ R α c)⁻¹ ∈ rootSpan τ R J := by
    intro α hα c β hβ d
    by_cases hab : α = β
    · subst hab
      have h : pinnedX τ R α c * pinnedX τ R α d * (pinnedX τ R α c)⁻¹ = pinnedX τ R α d := by
        rw [mul_inv_eq_iff_eq_mul, ← pinnedX_add, ← pinnedX_add, add_comm]
      rw [h]
      exact hroot_le α hβ (Subgroup.subset_closure ⟨_, rfl⟩)
    obtain ⟨hαr, hαp⟩ := hS α hα
    obtain ⟨hβr, hβp⟩ := hS β (hJS hβ)
    have hne : (⟨α, hαr⟩ : Root τ) ≠ ⟨β, hβr⟩ := fun h => hab (congrArg Subtype.val h)
    have hcomm := ringCommContained_pos R ⟨α, hαr⟩ ⟨β, hβr⟩ hαp hβp hne
    have hx : pinnedX τ R α c ∈ F.ringRootSubgroup R ⟨α, hαr⟩ := by
      rw [← rootSubgroup_eq_ringRootSubgroup R hαr]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have hy : pinnedX τ R β d ∈ F.ringRootSubgroup R ⟨β, hβr⟩ := by
      rw [← rootSubgroup_eq_ringRootSubgroup R hβr]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have hmem := hcomm _ hx _ hy
    have hcone : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α + b • β),
        F.ringRootSubgroup R γ) ≤ rootSpan τ R J := by
      refine iSup₂_le fun γ ⟨a, b, ha, hb, hγ⟩ => ?_
      rw [← rootSubgroup_eq_ringRootSubgroup R γ.2]
      refine hroot_le γ.1 ?_
      rw [hγ]
      exact hclosed α hα β hβ a b ha hb (hγ ▸ γ.2)
    have h1 := hcone hmem
    have h2 := mul_mem h1 (hroot_le β hβ (Subgroup.subset_closure ⟨d, rfl⟩))
    rwa [inv_mul_cancel_right] at h2
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_⟩
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  have hmap : ∀ c : R, rootSpan τ R J ≤
      (rootSpan τ R J).comap (MulAut.conj (pinnedX τ R α c)).toMonoidHom := fun c =>
    iSup₂_le fun β hβ => (Subgroup.closure_le _).2 (by
      rintro _ ⟨d, rfl⟩
      exact key α hα c β hβ d)
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap c hy, fun hy => ?_⟩
  have h := hmap (-c) hy
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  convert h using 1
  rw [← pinnedX_neg]
  group

end CFSG.LieType.Chevalley
