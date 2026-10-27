module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Defs

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

set_option linter.unusedSectionVars false


theorem e6_form_of_stabU {F : Type} [Field F] [Finite F] {α : MulAut (C6 F)} (hα : α ∈ stabU F) :
    ∃ (g : C6 F) (a : Fin Tag.E6.rank → Fˣ) (ρ : F ≃+* F) (ε : ℕ),
      (g : ModGL Tag.E6 F) ∈ borelGroup Tag.E6 F ∧
        α = MulAut.conj g * exactNormalAut .E6 F a ρ ε := by
  obtain ⟨g, a, ρ, ε, hαe⟩ := exists_conj_mul_exactNormalAut (τ := .E6) (K := F) (Or.inl rfl) α
  have hNmem : exactNormalAut .E6 F a ρ ε ∈ stabU F :=
    mem_stabU_iff_map.2 (exactNormalAut_mem (τ := .E6) (K := F) a ρ ε).1
  have hconj : MulAut.conj g ∈ stabU F := by
    have e : MulAut.conj g = α * (exactNormalAut .E6 F a ρ ε)⁻¹ := by
      rw [hαe, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hα (inv_mem hNmem)
  have hstab : ∀ y : C6 F, MulAut.conj g y ∈ U6 F ↔ y ∈ U6 F := mem_stabU_iff.1 hconj
  have hnorm : (g : ModGL Tag.E6 F) ∈
      Subgroup.normalizer (posUnipotent Tag.E6 F : Set (ModGL Tag.E6 F)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhA : h ∈ adjointGroup Tag.E6 F :=
        posUnipotent_le_adjointGroup (τ := Tag.E6) (K := F) hh
      have hy : MulAut.conj g (⟨h, hhA⟩ : C6 F) ∈ U6 F :=
        (hstab ⟨h, hhA⟩).2 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 hy
    · intro hgh
      have hgA : (g : ModGL Tag.E6 F) * h * (g : ModGL Tag.E6 F)⁻¹ ∈ adjointGroup Tag.E6 F :=
        posUnipotent_le_adjointGroup (τ := Tag.E6) (K := F) hgh
      have hhA : h ∈ adjointGroup Tag.E6 F := by
        have h1 := mul_mem (mul_mem (inv_mem g.2) hgA) g.2
        have e : (g : ModGL Tag.E6 F)⁻¹ * ((g : ModGL Tag.E6 F) * h * (g : ModGL Tag.E6 F)⁻¹)
            * (g : ModGL Tag.E6 F) = h := by group
        rw [e] at h1
        exact h1
      have hy : (⟨h, hhA⟩ : C6 F) ∈ U6 F :=
        (hstab ⟨h, hhA⟩).1 (Subgroup.mem_subgroupOf.2 hgh)
      exact Subgroup.mem_subgroupOf.1 hy
  have hmem : (g : ModGL Tag.E6 F) ∈
      adjointGroup Tag.E6 F ⊓ Subgroup.normalizer (posUnipotent Tag.E6 F : Set (ModGL Tag.E6 F)) :=
    ⟨g.2, hnorm⟩
  rw [(borel_self_normalizers Tag.E6 F).1] at hmem
  exact ⟨g, a, ρ, (ε : ℕ), hmem, hαe⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
