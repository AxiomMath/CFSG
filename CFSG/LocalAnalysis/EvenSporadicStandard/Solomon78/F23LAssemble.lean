module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

section Conj

variable {G : Type} [Group G]

theorem isElemAbelian_map_conj {p : ℕ} {E : Subgroup G} (h : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (E.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map h _

theorem card_map_conj (E : Subgroup G) (g : G) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end Conj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

end CFSG.EvenSporadicStandard.Solomon78
