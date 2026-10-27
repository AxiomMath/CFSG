module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Proper

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem centralizer_ne_top (hc : P23Cfg n Y R S t K' W u e g) {V : Subgroup Y} (hV : V ≠ ⊥) :
    Subgroup.centralizer (V : Set Y) ≠ ⊤ := by
  intro htop
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hc.std.perp.core.simple hc.std.perp.core.nonab
  apply hV
  rw [eq_bot_iff]
  intro v hv
  have hvc : v ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ Subgroup.centralizer (V : Set Y) := htop ▸ Subgroup.mem_top y
    exact ((Subgroup.mem_centralizer_iff.mp hy) v hv).symm
  rw [hZ] at hvc
  exact hvc

theorem rLayerSub_ne_top (hc : P23Cfg n Y R S t K' W u e g) {V : Subgroup Y} (hV : V ≠ ⊥) :
    rLayerSub (Om R) V ≠ ⊤ := fun h =>
  centralizer_ne_top hc hV (eq_top_iff.mpr (h ▸ F7C.rLayerSub_le_centralizer (Ω := Om R) V))

theorem card_secQuot_lt (hc : P23Cfg n Y R S t K' W u e g) {V : Subgroup Y} (hV : V ≠ ⊥) :
    Nat.card (SecQuot (rLayerSub (Om R) V)) < n := by
  have h1 : Nat.card (SecQuot (rLayerSub (Om R) V)) ≤ Nat.card ↥(rLayerSub (Om R) V) :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : Nat.card ↥(rLayerSub (Om R) V) < Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr (rLayerSub_ne_top hc hV))
  have h3 : Nat.card Y = n := hc.std.perp.core.card
  omega

end Proper

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
