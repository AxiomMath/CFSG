module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSect
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BlockStabPerfect

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv CFSG.AGLEmbedding.A15Local.Sect

variable {Ω : Type} [DecidableEq Ω] [Fintype Ω]

theorem sectionsOrder60_of_perfect_of_preserves {B : Finset Ω} (hB : B.card = 5)
    (hO : 2 * B.card = Fintype.card Ω) {V : Subgroup (Perm Ω)} (hV : ⁅V, V⁆ = V)
    (hpres : ∀ y ∈ V, (∀ i ∈ B, y i ∈ B) ∨ ∀ i ∈ B, y i ∉ B) :
    SectionsOrder60 ↥V := by
  obtain ⟨f, hf⟩ := exists_injective_alternatingGroup_prod_of_perfect hV fun y hy =>
    mem_blockStab_of_forall_mem_or_forall_not_mem hO (hpres y hy)
  have hA : ∀ (α : Type) [Fintype α] [DecidableEq α], Nat.card α = 5 →
      SectionsOrder60 ↥(alternatingGroup α) := fun α _ _ h =>
    sectionsOrder60_alternatingGroup_fin_five.of_injective
      (Finite.equivFinOfCardEq h).altCongrHom.toMonoidHom (MulEquiv.injective _)
  have h₁ : Nat.card {x // x ∈ B} = 5 := by simp [hB]
  have h₂ : Nat.card {x // x ∉ B} = 5 := by
    rw [hB] at hO
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hB]
    omega
  exact ((hA _ h₁).prod (hA _ h₂)).of_injective f hf

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
