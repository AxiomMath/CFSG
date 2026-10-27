module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def UMovesCond (Y : Type) [Group Y] : Prop :=
  ∀ u : Y, orderOf u = 2 → ∀ α : MulAut Y, α * α = 1 → ∃ h : Y, α (h * u * h⁻¹) = h * u * h⁻¹

theorem UMovesCond.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : UMovesCond Y) : UMovesCond Y' := by
  intro u hu α hα
  let φ : MulAut Y' → MulAut Y := fun a => (e.trans a).trans e.symm
  have hφ : ∀ (a : MulAut Y') (y : Y), φ a y = e.symm (a (e y)) := fun a y => rfl
  have hmul : ∀ a b : MulAut Y', φ (a * b) = φ a * φ b := fun a b => MulEquiv.ext fun y => by
    rw [hφ, MulAut.mul_apply, MulAut.mul_apply, hφ, hφ, MulEquiv.apply_symm_apply]
  have hone : φ 1 = 1 := MulEquiv.ext fun y => by
    rw [hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  have hu' : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
  obtain ⟨x, hx⟩ := h (e.symm u) hu' (φ α) (by rw [← hmul, hα, hone])
  refine ⟨e x, ?_⟩
  rw [hφ] at hx
  have := congrArg e hx
  simpa [map_mul, map_inv] using this

variable {G : Type} [Group G] {L : Subgroup G} {u : G}

omit [Group G] in
theorem sol78UMoves_of_cond {G : Type} [Group G] {L : Subgroup G} {u : G}
    (h : UMovesCond L) (hu : orderOf u = 2) (huL : u ∈ L) : Sol78UMoves L u := by
  intro s hs hss _
  have hu' : orderOf (⟨u, huL⟩ : L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hαα : L.normalizerMonoidHom ⟨s, hs⟩ * L.normalizerMonoidHom ⟨s, hs⟩ = 1 := by
    rw [← map_mul, ← map_one L.normalizerMonoidHom]
    congr 1
    exact Subtype.ext hss
  obtain ⟨x, hx⟩ := h ⟨u, huL⟩ hu' _ hαα
  refine ⟨x, x.2, ?_⟩
  have e1 := congrArg Subtype.val hx
  rw [normalizerMonoidHom_coe] at e1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1
  calc (x * u * (x : G)⁻¹ : G) * s = (s * ((x : G) * u * (x : G)⁻¹) * s⁻¹) * s := by rw [e1]
    _ = s * ((x : G) * u * (x : G)⁻¹) := by group

variable [Finite G]

theorem outer2_row_not_standard (s : TauCeti.SporadicName) (hchain : Sol78Chain s)
    (hI : ∀ (Y : Type) [Group Y], IsSporadic Y s → HypothesisOne Y)
    (hfours : ∀ (Y : Type) [Group Y], IsSporadic Y s → CFSG.EvenSmallLie.FoursGroupCondition Y)
    (hacc : ∀ (Y : Type) [Group Y], IsSporadic Y s → AutCenterCond Y)
    (humv : ∀ (Y : Type) [Group Y], IsSporadic Y s → UMovesCond Y)
    (L : Subgroup G) (hStd : StdHyp G L) : ¬ IsSporadic L s := by
  intro hL
  obtain ⟨L', K, t, u, hStd', hL', h⟩ := hchain G L hStd hL
  obtain ⟨e⟩ := hL'
  have := h.simpleL
  have hZ : center L' = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have hq : IsSporadic (L' ⧸ center L') s :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hS : ∀ S : Sylow 2 (centralizer (L' : Set G)), Nat.card S = 2 := fun S =>
    hStd'.card_sylow_eq_two_of_fours (hI _ hq) (hfours _ ⟨e⟩) S
  exact solomon_closing_3_12_3 hStd' hS h
    (sol78Fusion_of_autCenter hStd' hS h (hacc _ ⟨e⟩))
    (sol78UMoves_of_cond (humv _ ⟨e⟩) h.u_order h.u_mem)

end CFSG.EvenSporadicStandard.Solomon78
