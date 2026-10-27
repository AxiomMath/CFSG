module

public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

@[expose] def alphaOrbit (M F : Subgroup X) : Set (Subgroup X) :=
  {γ | ∃ f ∈ F, conjugate M f = γ}

@[expose] def Cor713Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ F : Subgroup X, F ≠ ⊤ → ¬ F ≤ M → (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty →
    ¬ zHull Z F ≤ M ∧
    ((Group.IsSolvable ↥(zHull Z F) ∧ ∃ u ∈ Z, Z ∩ ((F ⊓ M : Subgroup X) : Set X) = {u} ∧
        F ⊓ M = F ⊓ centralizer ({u} : Set X)) ∨
      (pPrimeCoreIn (zHull Z F) = (center ↥(zHull Z F)).map (zHull Z F).subtype ∧
        CFSG.BenderSuzuki.IsBenderGroup (↥(zHull Z F) ⧸ center ↥(zHull Z F)) ∧
        (∀ β₁ ∈ alphaOrbit M F, ∀ γ₁ ∈ alphaOrbit M F, β₁ ≠ γ₁ →
          ∀ β₂ ∈ alphaOrbit M F, ∀ γ₂ ∈ alphaOrbit M F, β₂ ≠ γ₂ →
            ∃ g ∈ zHull Z F, conjugate β₁ g = β₂ ∧ conjugate γ₁ g = γ₂) ∧
        ∀ β ∈ alphaOrbit M F, β ≠ M →
          (F : Set X) = (zHull Z F : Set X) * ((F ⊓ M ⊓ β : Subgroup X) : Set X)))

@[expose] def Cor713Extra (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ F : Subgroup X, F ≠ ⊤ → ¬ F ≤ M → (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty →
    ¬ Group.IsSolvable ↥(zHull Z F) →
      (∃ T : Sylow 2 (↥(zHull Z F) ⧸ center ↥(zHull Z F)),
        (M.comap (zHull Z F).subtype).map (QuotientGroup.mk' (center ↥(zHull Z F))) =
          normalizer ((T : Subgroup (↥(zHull Z F) ⧸ center ↥(zHull Z F))) :
            Set (↥(zHull Z F) ⧸ center ↥(zHull Z F)))) ∧
      (∀ y ∈ zHull Z F, orderOf y = 2 → y ∈ Z) ∧
      ∃ n : ℕ, 2 ≤ n ∧ (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).ncard = 2 ^ n - 1

section Setup

variable {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor713_isStronglyEmbedded_zHull
    (S : ZDSetup X Z M) {F : Subgroup X} (hF : F ≠ ⊤)
    (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty) :
    IsStronglyEmbedded ((M ⊓ zHull Z F).subgroupOf (zHull Z F)) :=
  S.prop44 benderFacts (S.no_solvable_normal benderFacts) hF hFM hne

omit [Finite X] in
theorem Cor713.zHull_le {Z : Set X} (F : Subgroup X) : zHull Z F ≤ F :=
  (Subgroup.closure_le _).mpr Set.inter_subset_right

omit [Finite X] in
theorem Cor713.mem_zHull_of_mem {Z : Set X} {F : Subgroup X} {z : X} (hz : z ∈ Z) (hzF : z ∈ F) :
    z ∈ zHull Z F :=
  Subgroup.subset_closure ⟨hz, hzF⟩

theorem ZDSetup.cor713_exists_mul_eq (S : ZDSetup X Z M) {F : Subgroup X} (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty) {f : X} (hf : f ∈ F) :
    ∃ m ∈ F ⊓ M, ∃ l ∈ zHull Z F, f = m * l := by
  obtain ⟨z₁, hz₁, hz₁FM⟩ := hne
  have hz₁F : z₁ ∈ F := (Subgroup.mem_inf.mp hz₁FM).1
  have hz₁M : z₁ ∈ M := (Subgroup.mem_inf.mp hz₁FM).2
  have hyZ : f⁻¹ * z₁ * f ∈ Z := S.invariant.2 z₁ hz₁ f
  have hyF : f⁻¹ * z₁ * f ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hf) hz₁F) hf
  obtain ⟨l, hl, hlz⟩ := S.exists_conj_zHull hFM ⟨z₁, hz₁, hz₁FM⟩ hz₁ hz₁F hz₁M hyZ hyF
  have hcomm : z₁ * (f * l⁻¹) = (f * l⁻¹) * z₁ := by
    calc z₁ * (f * l⁻¹) = f * (f⁻¹ * z₁ * f) * l⁻¹ := by group
      _ = f * (l⁻¹ * z₁ * l) * l⁻¹ := by rw [hlz]
      _ = (f * l⁻¹) * z₁ := by group
  have hmM : f * l⁻¹ ∈ M :=
    S.prodDisc.centralizer_le_of_mem hz₁ hz₁M
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm)
  have hlF : l ∈ F := Cor713.zHull_le F hl
  refine ⟨f * l⁻¹, Subgroup.mem_inf.mpr ⟨F.mul_mem hf (F.inv_mem hlF), hmM⟩, l, hl, ?_⟩
  group

theorem ZDSetup.cor713_exists_eq_mul (S : ZDSetup X Z M) {F : Subgroup X} (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty) {f : X} (hf : f ∈ F) :
    ∃ l ∈ zHull Z F, ∃ m ∈ F ⊓ M, f = l * m := by
  obtain ⟨m, hm, l, hl, hf'⟩ := S.cor713_exists_mul_eq hFM hne (F.inv_mem hf)
  refine ⟨l⁻¹, (zHull Z F).inv_mem hl, m⁻¹, (F ⊓ M).inv_mem hm, ?_⟩
  have : f = (f⁻¹)⁻¹ := (inv_inv f).symm
  rw [this, hf']
  group

theorem ZDSetup.cor713_alphaOrbit_eq (S : ZDSetup X Z M) {F : Subgroup X} (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty) :
    alphaOrbit M F = {γ | ∃ l ∈ zHull Z F, conjugate M l = γ} := by
  ext γ
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨m, hm, l, hl, rfl⟩ := S.cor713_exists_mul_eq hFM hne hf
    refine ⟨l, hl, ?_⟩
    have hmM : conjugate M m = M :=
      conjugate_eq_iff_mem_normalizer.mpr (by
        rw [S.prodDisc.normalizer_eq_self]
        exact (Subgroup.mem_inf.mp hm).2)
    rw [← conjugate_conjugate, hmM]
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Cor713.zHull_le F hl, rfl⟩

end Setup

end CFSG.GH74.Uniqueness
