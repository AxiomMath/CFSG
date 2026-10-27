module

public import CFSG.Assembly.Defs

public section

namespace CFSG

theorem Open.pCore_eq_pCore (p : ℕ) (G : Type*) [Group G] :
    Open.pCore p G = CFSG.pCore p G :=
  rfl

theorem Assembly.pCore_eq_pCore (p : ℕ) (G : Type*) [Group G] :
    Assembly.pCore p G = CFSG.pCore p G :=
  Open.pCore_eq_pCore p G

theorem Assembly.pCoreOf_eq_map_pCore (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    Assembly.pCoreOf p H = (CFSG.pCore p H).map H.subtype :=
  rfl

end CFSG
