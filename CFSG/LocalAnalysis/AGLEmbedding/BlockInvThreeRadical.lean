module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem not_isPGroup_blockPL (h86 : Asc81bEightSix) (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) :
    ¬ IsPGroup 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  intro h2bar
  have h2 := isPGroup_of_isPGroup_barM (inf_le_right.trans hL.le) h2bar
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hL.toIsTwoPrimeComponent.le_normalizer (h86 G M S hK hA _ hL.component) hA.twoRadical.1
  have hrad := hA.twoCore_eq_pCoreOf_normalizer_sup hL.toIsTwoPrimeComponent hSL
  have hT2 : IsPGroup 2 ((L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
    refine (h2.to_sup_of_normal_right' hS2 inf_le_left).to_le ?_
    rintro t ⟨htLS, htN⟩
    have htLS' : t ∈ ((L ⊔ S : Subgroup G) : Set G) := htLS
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L S hSL] at htLS'
    obtain ⟨l, hl, s, hs, rfl⟩ := htLS'
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have := (Subgroup.normalizer (S : Set G)).mul_mem htN
        (Subgroup.le_normalizer (S.inv_mem hs))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hlN, hl⟩ hs
  have hNS : (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    le_of_two_radical le_sup_right hrad inf_le_left hT2 Subgroup.le_normalizer
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowTwoOf S (L ⊔ S) :=
    ⟨le_sup_right, hS2, not_dvd_index_of_normalizer_inf_le_self le_sup_right hS2 hNS⟩
  exact hS (CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hsyl le_sup_left
    (sup_le Subgroup.le_normalizer hSL))

end CFSG.AGLEmbedding
