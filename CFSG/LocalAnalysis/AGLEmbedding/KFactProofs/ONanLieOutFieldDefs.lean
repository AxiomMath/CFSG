module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne.Sec66T (fixSub fixRes mem_fixSub)
open CFSG.RankThree.PartOne.FieldFix (FixedFacts fixRes_le_fixSub)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open scoped commutatorElement

theorem commutator_eq_self_of_isPerfect {G : Type*} [Group G] (N : Subgroup G)
    (h : Group.IsPerfect ↥N) : ⁅N, N⁆ = N := by
  have hN : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  calc ⁅N, N⁆ = ⁅(⊤ : Subgroup ↥N).map N.subtype, (⊤ : Subgroup ↥N).map N.subtype⁆ := by
        rw [hN]
    _ = Subgroup.map N.subtype ⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ :=
        (Subgroup.map_commutator _ _ _).symm
    _ = Subgroup.map N.subtype (commutator ↥N) := rfl
    _ = N := by rw [h.commutator_eq_top, hN]

@[expose] def FixesNonLocalized {T : Type} [Group T] (α : MulAut T) : Prop :=
  ∃ N₀ : Subgroup T, ⁅N₀, N₀⁆ = N₀ ∧ (∀ y ∈ N₀, α y = y) ∧ NonLocalized N₀

theorem FixesNonLocalized.of_fixedFacts {T : Type} [Group T] [Finite T] {p : ℕ} {α : MulAut T}
    (h : FixedFacts p α) : FixesNonLocalized α :=
  ⟨fixRes α, commutator_eq_self_of_isPerfect _
    (CFSG.RankThree.PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _),
    fun _ hy => mem_fixSub.1 (fixRes_le_fixSub α hy), h.nonLocalized⟩

end CFSG.AGLEmbedding.LieOut
