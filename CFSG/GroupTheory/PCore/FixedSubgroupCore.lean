module

public import CFSG.Assembly.Defs
public import CFSG.Open.GLADefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG

open CFSG.Open

variable {G : Type*} [Group G]

theorem gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore {p : ℕ} {H : Subgroup G} :
    GLAPPrimeCoreOf p H = ⊥ ↔ pPrimeCore p ↥H = ⊥ := by
  unfold GLAPPrimeCoreOf GLAPPrimeCore
  exact Subgroup.map_eq_bot_iff_of_injective (H := pPrimeCore p ↥H) (Subgroup.subtype_injective H)

theorem pPrimeCore_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (p : ℕ) (e : G ≃* H)
    (h : pPrimeCore p G = ⊥) : pPrimeCore p H = ⊥ := by
  rw [← pPrimeCore_map_iso p e, h, Subgroup.map_bot]

theorem odd_card_gLAPPrimeCoreOf_of_odd_card [Finite G] (p : ℕ) {H : Subgroup G}
    (h : Odd (Nat.card H)) : Odd (Nat.card (GLAPPrimeCoreOf p H)) := by
  unfold GLAPPrimeCoreOf GLAPPrimeCore
  exact h.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le (pPrimeCore p ↥H)))

end CFSG
