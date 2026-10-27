module

public import CFSG.LieType.Chevalley.GraphFixedSchreier
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem nonempty_mulEquiv_graphFixedRootGroup
    {G : Type} [Group G] (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (h : TwistedChevalleyModel G t (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nonempty (G ≃* graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields t hp hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hperf := (finite_fixed_root_group_perfect t hp hf K hcard σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial t K σ'
  rw [hσσ'] at hZ
  set H := twistedFixedGroup t K σ
  set C := graphFixedRootGroup t K σ
  have hZ' : Subgroup.center ↥⁅H, H⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL t.tag K) ∈ C := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL t.tag K) ∈ ⁅H, H⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg (Subtype.val : ↥⁅H, H⁆ → ModGL t.tag K)
        (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext (congrArg (Subtype.val : C → ModGL t.tag K) hcen))
  refine ⟨K, inferInstance, inferInstance, σ', ⟨?_⟩⟩
  rw [hσσ']
  exact e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
    (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))

theorem derivedSeries_outer_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {d : ℕ} (h : derivedSeries (Outer H) d = ⊥) : derivedSeries (Outer G) d = ⊥ := by
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism e
  rw [← map_derivedSeries_eq (f := E.symm.toMonoidHom) E.symm.surjective, h, Subgroup.map_bot]

theorem exceptional_diagram_fixed_model_Schreier
    (G : Type) [Group G] (p f : ℕ) :
    (ChevalleyExceptionalModel G .twistedE6 p f → derivedSeries (Outer G) 5 = ⊥) ∧
      (ChevalleyExceptionalModel G .trialityD4 p f → derivedSeries (Outer G) 3 = ⊥) ∧
      (ChevalleyExceptionalModel G .twistedE6 p f ∨ ChevalleyExceptionalModel G .trialityD4 p f →
        Group.IsSolvable (Outer G)) := by
  have hE6 : ChevalleyExceptionalModel G .twistedE6 p f → derivedSeries (Outer G) 5 = ⊥ := by
    intro h
    obtain ⟨hp, hf, -⟩ := h.1
    have hm : TwistedChevalleyModel G .E6 (p ^ f) := h.2
    obtain ⟨K, _, _, σ, ⟨e⟩⟩ := nonempty_mulEquiv_graphFixedRootGroup .E6 hp hf hm
    exact derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_fixed_root_group_Schreier .E6 K σ).1 rfl)
  have hD4 : ChevalleyExceptionalModel G .trialityD4 p f → derivedSeries (Outer G) 3 = ⊥ := by
    intro h
    obtain ⟨hp, hf, -⟩ := h.1
    have hm : TwistedChevalleyModel G .D4 (p ^ f) := h.2
    obtain ⟨K, _, _, σ, ⟨e⟩⟩ := nonempty_mulEquiv_graphFixedRootGroup .D4 hp hf hm
    exact derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_fixed_root_group_Schreier .D4 K σ).2 rfl)
  refine ⟨hE6, hD4, ?_⟩
  rintro (h | h)
  · exact ⟨⟨5, hE6 h⟩⟩
  · exact ⟨⟨3, hD4 h⟩⟩

end CFSG.LieType.Chevalley
