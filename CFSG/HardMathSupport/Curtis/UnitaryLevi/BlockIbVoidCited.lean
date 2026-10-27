module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbVoidCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}

theorem not_isSylowTwoOf_of_blockThreeIbHyp (h85 : Asc81bEightFive)
    (h : BlockThreeIbHyp M S L D x) : ¬ IsSylowTwoOf (S ⊓ L) L := by
  obtain ⟨hK, hA, hL, -, hX, -⟩ := id h
  exact fun hsyl => hX (h85 G M S L hK hA hL.toIsTwoPrimeComponent hsyl)

theorem false_of_nineThreeFive_of_cited (h85 : Asc81bEightFive) (h7 : CitedBlockAltSevenPL)
    (h : BlockThreeIbHyp M S L D x) (h5 : NineThreeFive M L) : False := by
  have hS := not_isSylowTwoOf_of_blockThreeIbHyp h85 h
  obtain ⟨hK, hA, hL, -, hX, -⟩ := id h
  exact false_of_isSolvable_blockPL ‹BlockThreeIbHyp M S L D x› <|
    isSolvable_of_card_dvd_seventyTwo (h7 G M S L hK hA hL hX hS h5)

theorem false_of_nineThreeFive (h85 : Asc81bEightFive)
    (h : BlockThreeIbHyp M S L D x) (h5 : NineThreeFive M L) : False :=
  false_of_nineThreeFive_of_cited h85 citedBlockAltSevenPL_holds h h5

theorem isSolvable_blockPL_of_nineThreeThree (hT : CitedBlockTransvectionPLType)
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h3 : NineThreeThree M S L)
    (hcyc : CycPerfect 3 (blockPL M S L)) : Group.IsSolvable (blockPL M S L) := by
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hT G M S L hK hA hL hX hS h3
  have hval : ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      (d.1 = .D m q ∨ d.1 = .twistedD m q) → 4 ≤ m := by
    intro m d q hd
    have h := d.2
    rcases hd with hd | hd <;> rw [hd] at h <;>
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
  have hsp : ∀ (m : ℕ) (d' : TauCeti.ValidLieTypeIndex), 4 ≤ m →
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) →
      Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃*
        (TauCeti.CFSGIndex.lie d').Group) → Group.IsSolvable (blockPL M S L) := by
    rintro m d' hm hd' ⟨φ⟩
    exact (false_of_cyc_of_surjective hcyc (φ.toMonoidHom.comp (QuotientGroup.mk' _))
      (φ.surjective.comp (QuotientGroup.mk'_surjective _)) (B := ⊤)
      (by rw [← commutator_def, kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds (m - 1) d'
        (by omega) hd'])
      (hasE9_top (hasE9_sp (by omega) hd'))).elim
  have hsix : Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin 6)) →
      Group.IsSolvable (blockPL M S L) := by
    rintro ⟨e6⟩
    obtain ⟨hp, hE⟩ := alternatingGroup_perfect_hasE9 (m := 6) (by norm_num)
    exact (false_of_cyc_of_surjective hcyc e6.toMonoidHom e6.surjective
      (B := alternatingGroup (Fin 6)) hp hE).elim
  have hsmall : ∀ n : ℕ, (n = 3 ∨ n = 4) →
      Nonempty (↥(blockPL M S L) ≃* Equiv.Perm (Fin n)) → Group.IsSolvable (blockPL M S L) := by
    rintro n hn ⟨e⟩
    apply isSolvable_of_card_dvd_seventyTwo
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
      Fintype.card_fin]
    rcases hn with rfl | rfl <;> decide
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      exact hsp m d' (hval m d q (Or.inl hd)) hd' hφ
    · obtain ⟨d', hd', hφ⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      exact hsp m d' (hval m d q (Or.inr hd)) hd' hφ
    · exact hsix (hU4 d ⟨q, hq, hd⟩ ⟨e⟩)
  · rcases hn with rfl | rfl | rfl
    · exact hsmall 3 (Or.inl rfl) (hA5 ⟨e⟩)
    · exact hsmall 4 (Or.inr rfl) (hA6 ⟨e⟩)
    · exact hsix (hA8 ⟨e⟩)

theorem false_of_nineThreeThree (h85 : Asc81bEightFive) (hT : CitedBlockTransvectionPLType)
    (h : BlockThreeIbHyp M S L D x) (h3 : NineThreeThree M S L) : False := by
  have hS := not_isSylowTwoOf_of_blockThreeIbHyp h85 h
  obtain ⟨hK, hA, hL, -, hX, -, -, hcyc, -⟩ := id h
  exact false_of_isSolvable_blockPL ‹BlockThreeIbHyp M S L D x›
    (isSolvable_blockPL_of_nineThreeThree hT hK hA hL hX hS h3 hcyc)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
