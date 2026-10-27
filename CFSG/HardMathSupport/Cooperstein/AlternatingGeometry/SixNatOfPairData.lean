module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairModelCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NormalizerFromAction
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec19 Equiv Equiv.Perm

variable {G : Type} [Group G]

def PairBlockData (X S L : Subgroup G) (n : ℕ) : Prop :=
  ∃ φ : ↥(barM X L) ≃* AltB (Fin n),
    ((barM X (S ⊓ L)).subgroupOf (barM X L)).map φ.toMonoidHom = EA (Fin n) ∧
    ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM X L)).map
      φ.toMonoidHom = NA (Fin n)

theorem nineThreeSixNat_of_pairBlockData {X S L : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (hirr : HasIrreducibleCommutatorQuotient L (blockV S L)) (D : PairBlockData X S L n) :
    NineThreeSixNat X S L := by
  have hAB : barM X (S ⊓ L) ≤ barM X (Subgroup.normalizer (S : Set G) ⊓ L) :=
    barM_mono (inf_le_inf_right _ Subgroup.le_normalizer)
  have hBC : barM X (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM X L :=
    barM_mono inf_le_right
  obtain ⟨φ, hS, hN⟩ := D
  obtain ⟨h1, h2, h3, h4⟩ := pairModel_core hAB hBC hn φ hS hN
  refine ⟨hirr, n, hn, ?_, h1, h2, h3, h4⟩
  have e : Fin n × Bool ≃ Fin (2 * n) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, mul_comm])
  exact ⟨φ.trans (Equiv.altCongrHom e)⟩

theorem pairBlockData_of_action [Finite G] {X S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hyp : Asc81bHyp X S)
    (φ : ↥(barM X L) ≃* AltB (Fin n))
    (hS : ((barM X (S ⊓ L)).subgroupOf (barM X L)).map φ.toMonoidHom = EA (Fin n))
    (hSL : barM X S ≤ Subgroup.normalizer ((barM X L : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _))
    (hact : ∀ s ∈ barM X S, ∃ σ ∈ blockFix (Fin n), ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = s * l * s⁻¹ →
      ((φ l' : AltB (Fin n)) : Perm (Fin n × Bool)) =
        σ * ((φ l : AltB (Fin n)) : Perm (Fin n × Bool)) * σ⁻¹) :
    PairBlockData X S L n := by
  have hSX : S ≤ X := hyp.twoRadical.1
  have hO2 := pCore_le_of_isTwoRadicalIn hyp.twoRadical
  have hS' : (((barM X S) ⊓ (barM X L)).subgroupOf (barM X L)).map φ.toMonoidHom = EA (Fin n) := by
    rw [← barM_inf hO2]; exact hS
  refine ⟨φ, hS, ?_⟩
  rw [barM_normalizer_inf hSX hO2]
  have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using hn
  exact map_normalizer_eq_NA hcard φ hS' hSL hact

theorem nineThreeSixNat_of_action [Finite G] {X S L : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (hyp : Asc81bHyp X S)
    (hirr : HasIrreducibleCommutatorQuotient L (blockV S L))
    (φ : ↥(barM X L) ≃* AltB (Fin n))
    (hS : ((barM X (S ⊓ L)).subgroupOf (barM X L)).map φ.toMonoidHom = EA (Fin n))
    (hSL : barM X S ≤ Subgroup.normalizer ((barM X L : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _))
    (hact : ∀ s ∈ barM X S, ∃ σ ∈ blockFix (Fin n), ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = s * l * s⁻¹ →
      ((φ l' : AltB (Fin n)) : Perm (Fin n × Bool)) =
        σ * ((φ l : AltB (Fin n)) : Perm (Fin n × Bool)) * σ⁻¹) :
    NineThreeSixNat X S L :=
  nineThreeSixNat_of_pairBlockData hn hirr
    (pairBlockData_of_action (by omega) hyp φ hS hSL hact)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
