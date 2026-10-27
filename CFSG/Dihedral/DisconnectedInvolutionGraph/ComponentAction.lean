module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbedding
public import CFSG.Dihedral.DisconnectedInvolutionGraph.PermutationParity

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

abbrev InvolutionComponent (G : Type*) [Group G] :=
  (disconnectedInvolutionCommutingGraph G).ConnectedComponent

abbrev involutionComponent (t : Involution G) : InvolutionComponent G :=
  (disconnectedInvolutionCommutingGraph G).connectedComponentMk t

instance involutionComponentMulAction : MulAction G (InvolutionComponent G) where
  smul g component := SimpleGraph.ConnectedComponent.map (conjugationGraphHom g) component
  one_smul component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | _ t =>
      change SimpleGraph.ConnectedComponent.map (conjugationGraphHom (1 : G))
        (involutionComponent t) = involutionComponent t
      rw [SimpleGraph.ConnectedComponent.map_mk]
      exact congrArg involutionComponent (conjugateInvolution_one t)
  mul_smul g h component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | _ t =>
      change SimpleGraph.ConnectedComponent.map (conjugationGraphHom (g * h))
        (involutionComponent t) =
          SimpleGraph.ConnectedComponent.map (conjugationGraphHom g)
            (SimpleGraph.ConnectedComponent.map (conjugationGraphHom h) (involutionComponent t))
      simp only [SimpleGraph.ConnectedComponent.map_mk]
      exact congrArg involutionComponent (conjugateInvolution_mul g h t)

@[simp]
theorem smul_involutionComponent (g : G) (t : Involution G) :
    g • involutionComponent t = involutionComponent (conjugateInvolution g t) :=
  SimpleGraph.ConnectedComponent.map_mk _ _

theorem involutionComponent_surjective :
    Function.Surjective (involutionComponent (G := G)) := by
  intro component
  induction component using SimpleGraph.ConnectedComponent.ind with
  | _ t => exact ⟨t, rfl⟩

instance involutionComponentFinite [Finite G] : Finite (InvolutionComponent G) :=
  Finite.of_surjective involutionComponent involutionComponent_surjective

theorem componentStabilizer_eq_stabilizer (t : Involution G) :
    componentStabilizer t = MulAction.stabilizer G (involutionComponent t) := by
  ext g
  rw [mem_componentStabilizer_iff, MulAction.mem_stabilizer_iff, smul_involutionComponent]
  exact SimpleGraph.ConnectedComponent.eq.symm.trans eq_comm

theorem involution_components_transitive [Finite G] (t u : Involution G) :
    ∃ g : G, g • involutionComponent t = involutionComponent u := by
  rcases Nat.even_or_odd (orderOf ((t : G) * u)) with heven | hodd
  · refine ⟨1, ?_⟩
    rw [one_smul]
    exact SimpleGraph.ConnectedComponent.sound (reachable_of_even_product t u heven)
  · obtain ⟨exponent, hconj⟩ := odd_product_conjugates t u hodd
    refine ⟨((t : G) * u) ^ exponent, ?_⟩
    rw [smul_involutionComponent, hconj]

instance involutionComponentPretransitive [Finite G] :
    MulAction.IsPretransitive G (InvolutionComponent G) where
  exists_smul_eq component other := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | _ t =>
      induction other using SimpleGraph.ConnectedComponent.ind with
      | _ u => exact involution_components_transitive t u

theorem involution_fixes_component_iff [Finite G] (t u : Involution G) :
    (t : G) • involutionComponent u = involutionComponent u ↔
      involutionComponent t = involutionComponent u := by
  rw [← MulAction.mem_stabilizer_iff, ← componentStabilizer_eq_stabilizer,
    componentStabilizer_involution_iff]
  exact SimpleGraph.ConnectedComponent.eq.symm.trans eq_comm

theorem involution_unique_fixed_component [Finite G] (t : Involution G) :
    ∃! component : InvolutionComponent G, (t : G) • component = component := by
  refine ⟨involutionComponent t, (involution_fixes_component_iff t t).mpr rfl, ?_⟩
  intro component hfixed
  obtain ⟨u, rfl⟩ := involutionComponent_surjective component
  exact ((involution_fixes_component_iff t u).mp hfixed).symm

theorem componentAction_injective [Finite G] [IsSimpleGroup G]
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    Function.Injective (MulAction.toPermHom G (InvolutionComponent G)) := by
  classical
  let representation := MulAction.toPermHom G (InvolutionComponent G)
  rcases CFSG.eq_bot_or_eq_top_of_normal representation.ker
      inferInstance with hbot | htop
  · exact representation.ker_eq_bot_iff.mp hbot
  · exfalso
    obtain ⟨t, u, hnopath⟩ : ∃ t u : Involution G,
        ¬ (disconnectedInvolutionCommutingGraph G).Reachable t u := by
      change ¬ ∀ t u : Involution G,
        (disconnectedInvolutionCommutingGraph G).Reachable t u at hdisc
      push Not at hdisc
      exact hdisc
    obtain ⟨g, hmove⟩ := involution_components_transitive t u
    have hg : representation g = 1 := by
      apply (MonoidHom.mem_ker (f := representation)).mp
      rw [htop]
      trivial
    have hfixed := congrArg (fun permutation : Equiv.Perm (InvolutionComponent G) =>
      permutation (involutionComponent t)) hg
    change g • involutionComponent t = involutionComponent t at hfixed
    apply hnopath
    exact SimpleGraph.ConnectedComponent.exact (hfixed.symm.trans hmove)

theorem componentAction_faithful [Finite G] [IsSimpleGroup G]
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    FaithfulSMul G (InvolutionComponent G) := by
  constructor
  intro g h heq
  apply componentAction_injective hdisc
  apply Equiv.ext
  exact heq

theorem component_degree_odd [Finite G]
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    Odd (Nat.card (InvolutionComponent G)) := by
  classical
  obtain ⟨t, u, hnopath⟩ : ∃ t u : Involution G,
      ¬ (disconnectedInvolutionCommutingGraph G).Reachable t u := by
    change ¬ ∀ t u : Involution G,
      (disconnectedInvolutionCommutingGraph G).Reachable t u at hdisc
    push Not at hdisc
    exact hdisc
  let representation := MulAction.toPermHom G (InvolutionComponent G)
  apply odd_card_of_involution_unique_fixed_point (representation t)
  · rw [← map_pow]
    have hsquare : (t : G) ^ 2 = 1 := by
      simpa only [t.property] using pow_orderOf_eq_one (t : G)
    rw [hsquare, map_one]
  · exact involution_unique_fixed_component t

theorem component_degree_at_least_three [Finite G]
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    3 ≤ Nat.card (InvolutionComponent G) := by
  classical
  let _ := Fintype.ofFinite (InvolutionComponent G)
  obtain ⟨t, u, hnopath⟩ : ∃ t u : Involution G,
      ¬ (disconnectedInvolutionCommutingGraph G).Reachable t u := by
    change ¬ ∀ t u : Involution G,
      (disconnectedInvolutionCommutingGraph G).Reachable t u at hdisc
    push Not at hdisc
    exact hdisc
  have : Nontrivial (InvolutionComponent G) :=
    ⟨⟨involutionComponent t, involutionComponent u,
      fun heq => hnopath (SimpleGraph.ConnectedComponent.exact heq)⟩⟩
  have hlower := Fintype.one_lt_card_iff_nontrivial.mpr
    (inferInstance : Nontrivial (InvolutionComponent G))
  rw [Fintype.card_eq_nat_card] at hlower
  obtain ⟨half, hhalf⟩ := component_degree_odd hdisc
  omega

end CFSG.DisconnectedInvolutionGraph.Helpers
