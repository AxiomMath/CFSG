module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduce
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeThree barM blockPL)
open CFSG.HardMathSupport.Cooperstein.StructureLie
  (nonempty_commutator_bilinIsometryGroup_alt_six)

@[expose] def BlockShape (X P : Type) [Group X] [Group P] : Prop :=
  (Nonempty (X ≃* alternatingGroup (Fin 6)) ∧ Nonempty (P ≃* Equiv.Perm (Fin 4))) ∨
  (∃ k : ℕ, (Nat.card X).factorization 2 = k * (k - 1) ∧
    Nonempty (P ≃* ↥(CFSG.Open.StatedSp (k - 1) (ZMod 2)))) ∨
  ∃ m : ℕ, 5 ≤ m ∧ Nonempty (X ≃* alternatingGroup (Fin m)) ∧
    Nonempty (P ≃* Equiv.Perm (Fin (m - 2)))

theorem block_shape (hO : OrthTransvectionCent)
    (hSym : SymTransvectionCent) (hSp : SpFourTransvectionCent) (h2 : OrthTwoPart)
    {G : Type} [Group G] [Finite G] {M S L : Subgroup G} (hK : CFSG.Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (h3 : NineThreeThree M S L)
    (hZ : Subgroup.center ↥(barM M L) = ⊥) :
    BlockShape ↥(barM M L) ↥(blockPL M S L) := by
  obtain ⟨W, _, _, _, H, t, hmodel, ⟨e1⟩, ⟨e2⟩⟩ := exists_transvectionModel hK hA hL h3 hZ
  obtain ⟨htH, htr, htn, hidx, hperf, hne, hshape⟩ := hmodel
  rcases hshape with ⟨h4, f, hnd, halt, hH⟩ | ⟨Q, hQ, hH⟩ | ⟨heven, hheart⟩
  · subst hH
    obtain ⟨eA⟩ := nonempty_commutator_bilinIsometryGroup_alt_six hnd halt h4
    obtain ⟨eC⟩ := hSp W f h4 hnd halt t htH htr htn
    exact Or.inl ⟨⟨e1.trans eA⟩, ⟨e2.trans eC⟩⟩
  · subst hH
    obtain ⟨k, hk, ⟨eC⟩⟩ := hO W Q hQ hidx t htH htr htn
    refine Or.inr (Or.inl ⟨k, ?_, ⟨e2.trans eC⟩⟩)
    rw [Nat.card_congr e1.toEquiv]
    exact h2 W Q hQ hidx k hk
  · obtain ⟨m, hm, ⟨eA⟩, ⟨eC⟩⟩ := hSym W H heven hheart hperf hne t htH htr htn
    exact Or.inr (Or.inr ⟨m, hm, ⟨e1.trans eA⟩, ⟨e2.trans eC⟩⟩)

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
