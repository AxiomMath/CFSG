module

public import CFSG.Open.LocalVocabulary
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.LieType.BorelTits

private def HullSet_rhl {G : Type*} [Group G] (p : ℕ) (L A X H : Subgroup G) : Prop :=
  X ≤ H ∧ H ≤ L ∧ IsPGroup p H ∧ A ≤ normalizer (H : Set G) ∧
    L ⊓ normalizer (X : Set G) ≤ normalizer (H : Set G)

theorem exists_pCoreOf_inf_normalizer_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {L A X : Subgroup G} (hA : A ≤ normalizer (L : Set G)) (hXL : X ≤ L) (hX : IsPGroup p X)
    (hAX : A ≤ normalizer (X : Set G)) :
    ∃ H : Subgroup G, X ≤ H ∧ H ≤ L ∧ pCoreOf p (L ⊓ normalizer (H : Set G)) = H ∧
      A ≤ normalizer (H : Set G) ∧ L ⊓ normalizer (X : Set G) ≤ normalizer (H : Set G) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H, hXH, hmax⟩ := Finite.exists_le_maximal (p := HullSet_rhl p L A X) (a := X)
    ⟨le_rfl, hXL, hX, hAX, inf_le_right⟩
  have hHmem : HullSet_rhl p L A X H := hmax.1
  unfold HullSet_rhl at hHmem
  obtain ⟨hXH', hHL, hHp, hAH, hLXH⟩ := hHmem
  have hHle : H ≤ L ⊓ normalizer (H : Set G) := le_inf hHL le_normalizer
  have hHH' : H ≤ pCoreOf p (L ⊓ normalizer (H : Set G)) :=
    le_pCoreOf_of_le_normalizer p hHle inf_le_right hHp
  have hH'mem : HullSet_rhl p L A X (pCoreOf p (L ⊓ normalizer (H : Set G))) := by
    unfold HullSet_rhl
    refine ⟨hXH'.trans hHH', (pCoreOf_le p _).trans inf_le_left, pCoreOf_isPGroup p _, ?_, ?_⟩
    · have hNL : A ≤ normalizer (L : Set G) := hA
      have hNN : A ≤ normalizer (normalizer (H : Set G) : Set G) := hAH.trans le_normalizer
      exact (le_inf hNL hNN).trans (Subgroup.inf_normalizer_le_normalizer_inf.trans
        (normalizer_le_normalizer_pCoreOf p _))
    · exact (le_inf inf_le_left hLXH).trans (le_normalizer_pCoreOf p _)
  have hH'H : pCoreOf p (L ⊓ normalizer (H : Set G)) ≤ H := hmax.2 hH'mem hHH'
  exact ⟨H, hXH, hHL, le_antisymm hH'H hHH', hAH, hLXH⟩

end CFSG.GroupTheory
