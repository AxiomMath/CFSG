module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas

public section

namespace CFSG

theorem subgroupOf_le_pPrimeCore_map {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p (↥H)).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    natCard_subgroupOf_eq K H hKH
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p (↥H) := le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

end CFSG
