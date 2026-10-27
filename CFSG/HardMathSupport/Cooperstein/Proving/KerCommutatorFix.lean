module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.AGLEmbedding (blockV)
open CFSG.HardMathSupport.Cooperstein.Coordinator (blockVCommGroup sup_le_normalizer_blockV)
open scoped commutatorElement
open Module

variable {G : Type} [Group G]

theorem commutator_blockV_le (S L : Subgroup G) : ⁅blockV S L, L⁆ ≤ blockV S L := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlN : l ∈ Subgroup.normalizer ((blockV S L : Subgroup G) : Set G) :=
    sup_le_normalizer_blockV S L ((le_sup_left : L ≤ L ⊔ S) hl)
  have h1 : l * v * l⁻¹ ∈ blockV S L := (Subgroup.mem_normalizer_iff.1 hlN v).1 hv
  have hexp : ⁅v, l⁆ = v * (l * v * l⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [hexp]
  exact mul_mem hv (inv_mem h1)

theorem mul_comm_commutator_blockV (S L : Subgroup G) {x y : G}
    (hx : x ∈ ⁅blockV S L, L⁆) (hy : y ∈ ⁅blockV S L, L⁆) : x * y = y * x := by
  let _ := blockVCommGroup S L
  exact congrArg Subtype.val
    (mul_comm (⟨x, commutator_blockV_le S L hx⟩ : ↥(blockV S L))
      ⟨y, commutator_blockV_le S L hy⟩)

instance commGroupCommutatorBlockV (S L : Subgroup G) : CommGroup ↥⁅blockV S L, L⁆ :=
  { (inferInstance : Group ↥⁅blockV S L, L⁆) with
    mul_comm := fun a b => Subtype.ext (mul_comm_commutator_blockV S L a.2 b.2) }

theorem sq_eq_one_commutator_blockV (S L : Subgroup G) (w : ↥⁅blockV S L, L⁆) : w ^ 2 = 1 :=
  Subtype.ext (by
    show (w : G) ^ 2 = 1
    exact (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf
      (CFSG.Open.pCoreOf 2 (L ⊔ S))).2 _ (commutator_blockV_le S L w.2))

instance commutatorBlockVModule (S L : Subgroup G) :
    Module (ZMod 2) (Additive ↥⁅blockV S L, L⁆) :=
  AddCommGroup.zmodModule (n := 2) fun x =>
    congrArg Additive.ofMul (sq_eq_one_commutator_blockV S L (Additive.toMul x))

end CFSG.HardMathSupport.Cooperstein.Proving
end
