module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbVoidCore

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open
open scoped commutatorElement

section Generic

variable {Y : Type*} [Group Y] [Finite Y]

theorem isSolvable_of_quotient_perm_le_four {J : Subgroup Y} {n : ℕ}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) (hn : n ≤ 4) : Group.IsSolvable J := by
  have h2 : Group.IsSolvable (CFSG.pCore 2 ↥J) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥J) := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).isNilpotent
    infer_instance
  have hq : Group.IsSolvable (↥J ⧸ CFSG.pCore 2 ↥J) :=
    have : Group.IsSolvable (Equiv.Perm (Fin n)) := Equiv.Perm.isSolvable (by simpa using hn)
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥J).subtype (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
    (by
      intro g hg
      rw [QuotientGroup.ker_mk'] at hg
      exact ⟨⟨g, hg⟩, rfl⟩)

end Generic

section Void

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}

theorem false_of_quotient_perm_of_ne_five (h : BlockThreeIbHyp M S L D x) {n : ℕ} (hn : n ≠ 5)
    (e : ↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃* Equiv.Perm (Fin n)) : False := by
  by_cases h4 : n ≤ 4
  · exact false_of_isSolvable_blockPL h (isSolvable_of_quotient_perm_le_four e h4)
  · obtain ⟨-, -, -, -, -, -, -, hcyc, -⟩ := id h
    obtain ⟨hp, hE⟩ := alternatingGroup_perfect_hasE9 (m := n) (by omega)
    exact false_of_cyc_of_surjective (hcyc : CycPerfect 3 (blockPL M S L))
      (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (B := alternatingGroup (Fin n)) hp hE

theorem nineThreeSix_five (h : BlockThreeIbHyp M S L D x) (h6 : NineThreeSix M S L) :
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 10)) ∧
      Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h6
  have hn : n = 5 := by
    by_contra hn
    exact false_of_quotient_perm_of_ne_five h hn e2
  subst hn
  exact ⟨⟨e1⟩, ⟨e2⟩⟩

theorem nineThreeSeven_five (h : BlockThreeIbHyp M S L D x) (h7 : NineThreeSeven M S L) :
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 20)) ∧
      Nonempty (↥(blockPL M S L) ⧸ CFSG.pCore 2 ↥(blockPL M S L) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h7
  have hn : n = 5 := by
    by_contra hn
    exact false_of_quotient_perm_of_ne_five h hn e2
  subst hn
  exact ⟨⟨e1⟩, ⟨e2⟩⟩

end Void

end CFSG.HardMathSupport.Curtis.UnitaryLevi
