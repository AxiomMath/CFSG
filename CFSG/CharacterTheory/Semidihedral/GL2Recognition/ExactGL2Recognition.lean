module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2CentralizerOrderAlternatives
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2RecognitionSupport
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order7920FourTransitiveAction

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.GL2ThreeCharacters

theorem exact_GL2_three_involution_centralizer_recognition
    {G : Type} [Group G] [Finite G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3))) :
    commutator G = ⊤ ∧
      Xor (Nat.card G = 5616 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1)
        (Nat.card G = 7920 ∧ Nonempty (G ≃* CFSG.Open.StatedM11) ∧
          Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)) := by
  have := Fintype.ofFinite G
  obtain ⟨φ⟩ := hC
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  obtain ⟨-, -, -, -, φ', -, -, hφ'val, -⟩ := GL2_three_ordinary_character_table_construction
    basisH a0 GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center
  let φc : Fin 8 → G23 → ℂ := fun i => (basisH.representation (φ' i)).character
  have hφirr : ∀ i, φc i ∈ CFSG.BlocksIrr G23 := fun i =>
    GL2Columns.label_mem_blocksIrr basisH (φ' i)
  obtain ⟨hperf, hxor⟩ := exact_GL2_centralizer_produces_order_alternatives hinv t ht φ a0
    GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center φc hφirr hφ'val
  refine ⟨hperf, ?_⟩
  rcases hxor with ⟨⟨hG, -⟩, -⟩ | ⟨⟨hG, hmodel, -⟩, -⟩
  ·
    obtain ⟨-, -, -, -, -, χ, hχ, hχ1, hχt, -⟩ :=
      order7920_local_profile_and_degree_ten_character hG hinv t ht ⟨φ⟩
    obtain ⟨P, F, Q, -, -, -, -, -, -, -, hidx, -, hsharp, -⟩ :=
      order7920_produces_sharply_four_transitive_action hG hinv t ht ⟨φ⟩ χ hχ hχ1 hχt
    obtain ⟨-, hM11, hM11'⟩ :=
      sharply_four_transitive_GL2_centralizer_exact_M11 hinv ht φ hidx hsharp
    exact Or.inr ⟨⟨hG, hM11, hM11'⟩, fun h => absurd (h.1.symm.trans hG) (by norm_num)⟩
  ·
    exact Or.inl ⟨⟨hG, hmodel⟩, fun h => absurd (h.1.symm.trans hG) (by norm_num)⟩

end CFSG.Semidihedral.GL2Recognition
