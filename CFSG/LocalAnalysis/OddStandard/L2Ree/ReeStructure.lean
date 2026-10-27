module

public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureSylow
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureSylowTwo
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureCentralizer
public import CFSG.LocalAnalysis.OddStandard.L2Ree.ReeStructureOddIndex

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard

section Ree


theorem exists_ree_structure {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}
    (h : StdHyp G L) (hm : LieModel (L ⧸ center L) .twistedG2 0 3 f) (hZ : center L = ⊥)
    {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    ∃ E M : Subgroup G, E ≤ L ∧ Nat.card E = 8 ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
        ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom) ∧
      centralizer (E : Set G) ⊓ L = E ∧
      Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168 ∧
      L ≤ M ∧ (L.subgroupOf M).Normal ∧ Odd (L.relIndex M) ∧
      centralizer ({t} : Set G) = M ⊔ zpowers t ∧ Disjoint M (zpowers t) ∧
      (∀ P : Subgroup G, P ≤ M → IsPGroup 2 P →
        ∃ g ∈ M, P ≤ E.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨E, hEL, hE8, hE2, hEsyl, hEC, hEN⟩ := exists_sylow_of_ree hm hZ
  have hK := kBase_of_lieModel_twistedG2 hm
  obtain ⟨M, hLM, hMN, hModd, hMC, hMd⟩ := exists_centralizer_eq_prod_of_odd_out h
    (card_sylow_centralizer_eq_two h hm) ht ht2 (odd_index_conj_range_of_kBase hK) hZ
  exact ⟨E, M, hEL, hE8, hE2, hEsyl, hEC, hEN, hLM, hMN, hModd, hMC, hMd,
    exists_conj_le_of_odd_relIndex hLM hMN hModd hEsyl⟩

end Ree

end CFSG.OddStandard.L2Ree
