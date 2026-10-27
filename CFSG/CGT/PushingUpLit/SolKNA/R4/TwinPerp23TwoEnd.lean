module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoCent
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpMainR

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Two

section End

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem sup_centralizer_conj_eq_top (hr : 4 ≤ r) (hE : TwinThmER r n) (h : PerpHypR r n Y R S t)
    (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) {g : Y} (hg : g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W)
    (hgt : g * t * g⁻¹ ≠ t) (hvK : g * t * g⁻¹ ∈ tightCore R ⊔ K') :
    Subgroup.centralizer ({g * t * g⁻¹} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
  obtain ⟨K'', hK'', hne'', ⟨D⟩⟩ := exists_twoFrame h h2 hW htW hS4
  have hz2 : t * t = 1 := (TwoFrame.hzK D).sq
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := Thompson.MGrp_le_normalizer _ W hg
  have hvW : g * t * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN t).mp htW
  have hv2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hv1 : g * t * g⁻¹ ≠ 1 := by
    intro h1
    apply (TwoFrame.hzK D).ne_one
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h1]; group
  exact sup_centralizer_eq_top_of_thmE hr hE h h2 hW htW hS4 hK' hne hvK hvW hv2 hv1 hgt

theorem conjInTwins_of_not_wCentral (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) {g : Y} (hg : g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W) :
    g * t * g⁻¹ ∈ tightCore R ⊔ K' := by
  obtain ⟨K'', hK'', hne'', ⟨D⟩⟩ := exists_twoFrame h h2 hW htW hS4
  have hpair : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K''} :=
    TwinPerp.twinSet_eq_pair h2 hK'' hne''
  have hK'eq : K' = K'' := by
    rw [hpair] at hK'
    rcases hK' with h1 | h1
    · exact absurd h1 hne
    · exact h1
  subst hK'eq
  exact D.conj_mem_sup h.core.hyp hW (Q3CL.T8.ctxOf h.partIHypG hW) hnc hg

theorem two23R_of_not_wCentral (hr : 4 ≤ r) (hE : TwinThmER r n) (h : PerpHypR r n Y R S t)
    (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W)
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {g : Y}
    (hg : g ∈ MGrp (CoreAssembly.conjClass (tightCore R)) W) (hgt : g * t * g⁻¹ ≠ t) :
    Subgroup.centralizer ({g * t * g⁻¹} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
  obtain ⟨K', hK', hne, -⟩ := exists_twoFrame h h2 hW htW hS4
  exact sup_centralizer_conj_eq_top hr hE h h2 hW htW hS4 hK' hne hg hgt
    (conjInTwins_of_not_wCentral h h2 hW htW hS4 hnc hK' hne hg)

end End

end Two

section Final

variable {r n : ℕ}

theorem two23R_of_thmE (hr : 4 ≤ r) (hE : TwinThmER r n) (h233 : TwinPerp233R r n) :
    Two23R r n := by
  intro Y _ _ R S t h h2 W hW htW hS4 g hg hgt
  exact Two.two23R_of_not_wCentral hr hE h h2 hW htW hS4 (h233 Y R S t h h2 W hW htW hS4) hg hgt

end Final

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
