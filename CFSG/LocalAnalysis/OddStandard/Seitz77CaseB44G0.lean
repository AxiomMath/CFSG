module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Loc
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Qmax
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Defs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Sylow

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure CrossData {G : Type} [Group G] (M₁ M₂ N₁ N₂ : Subgroup G) : Prop where
  comm : ⁅M₁ ⊔ N₁, M₂ ⊔ N₂⁆ = ⊥
  model : LieModel ((M₁ ⊔ N₁ : Subgroup G) ⧸ center (M₁ ⊔ N₁ : Subgroup G)) .PSL 3 2 2

section G0

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)}

theorem caseBG0_of_cross (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)
    (hR : Radicals d.V V₁ V₂) (hZ₁ : c₁.OddCoreCentral) (hZ₂ : c₂.OddCoreCentral)
    (X : CrossData M₁ M₂ N₁ N₂) :
    CaseBG0 d (M₁ ⊔ N₁) (M₂ ⊔ N₂) S c₁.W c₂.W where
  swap := fun x => by
    have : M₂ ⊔ N₂ = cs d.t (M₁ ⊔ N₁) := by rw [cs_sup, ← CS.M₂_eq, ← CS.N₂_eq]
    rw [this, mem_cs]
  comm := X.comm
  perfect := perfect_sup CS.F₁.perfect₁ CS.F₂.perfect₁
  model := X.model
  odd_centralizer := CS.odd_centralizer
  S₀_le := CS.S_le_G₀
  card_S₀ := CS.card_S
  W₁_le := CS.W₁_le_S
  W₂_le := CS.W₂_le_S
  W₁_elem := c₁.W_elem
  W₂_elem := c₂.W_elem
  card_W₁ := c₁.W_card
  card_W₂ := c₂.W_card
  W_sup := CS.W_sup
  G₀_eq := by
    show M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) = c₁.Ninf ⊔ c₂.Ninf
    rw [CS.ninf₁, CS.ninf₂, sup_sup_sup_comm]
  P_le := CS.P_le hR hZ₁ hZ₂
  qmax₁ := CS.qmax₁ hZ₁
  qmax₂ := CS.qmax₂ hZ₂
  loc := CS.loc hZ₁ hZ₂

end G0

end CFSG.OddStandard.Seitz77
