module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6Rigid
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6Wit
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.le_oddCore_of_normal
  EvenCatalog.odd_card_oddCore EvenCatalog.oddCore_eq_bot_of_mulEquiv)

theorem oddCore_eq_bot_of_normal {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (h : CFSG.oddCore G = ⊥) : CFSG.oddCore N = ⊥ := by
  have hn : ((CFSG.oddCore N).map N.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hmap := CFSG.pPrimeCore_map_iso 2 (MulAut.conjNormal g : MulAut N)
    rw [← CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two'] at hmap
    have hy' : MulAut.conjNormal g y ∈ CFSG.oddCore N := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hy
    exact Subgroup.mem_map.2 ⟨_, hy', by simp [MulAut.conjNormal_apply]⟩
  have hle := EvenCatalog.le_oddCore_of_normal hn (by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact EvenCatalog.odd_card_oddCore)
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
  exact hle

theorem oddCore_inner_inf_eq_bot {C : Type*} [Group C] [Finite (MulAut C)] {x : MulAut C}
    (h : CFSG.oddCore ↥((⊤ : Subgroup (MulAut C)) ⊓ centralizer {x}) = ⊥) :
    CFSG.oddCore ↥(OuterAutomorphisms.inner C ⊓ centralizer {x}) = ⊥ := by
  have hle : OuterAutomorphisms.inner C ⊓ centralizer {x} ≤ ⊤ ⊓ centralizer {x} :=
    inf_le_inf_right _ le_top
  have : ((OuterAutomorphisms.inner C ⊓ centralizer {x}).subgroupOf
      (⊤ ⊓ centralizer {x})).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Subgroup.mem_inf.2 ⟨(inner_normal C).conj_mem _ (Subgroup.mem_inf.1 hn).1 g,
      mul_mem (mul_mem (Subgroup.mem_inf.1 g.2).2 (Subgroup.mem_inf.1 hn).2)
        (inv_mem (Subgroup.mem_inf.1 g.2).2)⟩
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)
    (oddCore_eq_bot_of_normal h)

theorem ringAut_mul_comm {K : Type} [Field K] [Finite K] (a b : RingAut K) : a * b = b * a := by
  have : IsCyclic (RingAut K) := ringAut_isCyclic
  let : CommGroup (RingAut K) := IsCyclic.commGroup
  exact mul_comm a b

theorem hypII_of_E6
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤) {m : ℕ} (hm : 1 ≤ m)
    (h : ChevalleyExceptionalModel (A ⧸ center A) .E6 2 m) (hodd : Odd (Nat.card (center A))) :
    HypII A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup TwistTag.E6.tag h.2
  have : Finite (adjointGroup TwistTag.E6.tag K) := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut (adjointGroup TwistTag.E6.tag K)) := MulEquiv.finite_left
  have ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K :=
    pinnedX_mem_adjointGroup _ _
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  refine hypII_of_secondGraph center_adjointGroup_eq_bot (ξ := e6Xi K ht) ?_ Θ
    (fun a b => Prod.ext (ringAut_mul_comm a.1 b.1) (mul_comm a.2 b.2)) ?_ ?_
    (secondGraphWitness_E6 hm hK ht) hA hodd e
  · intro α hαX hα2
    rcases rigid_or_secondGraph_E6 hm hK α hαX hα2 with h | ⟨_ht, φ, hφ⟩
    · exact Or.inl h
    · exact Or.inr ⟨φ, hφ⟩
  · intro α hα hα2
    obtain ⟨g, a, hga⟩ := (hker α).1 hα
    refine CFSG.RankThree.Chevalley.mem_inner_of_conj_mul_rootDiagAut hm K hK hα2 g a
      (MulEquiv.ext fun h => Subtype.ext ?_)
    rw [hga h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_rootDiagAut]
    group
  · intro x hx2 hx1
    have hx := orderOf_eq_prime hx2 hx1
    by_cases hxX : x ∈ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag K)
    · have h0 := even_exceptional_inner_involution_full_centralizer_odd_core.1 TwistTag.E6.tag m K
        hm hK (Or.inr (Or.inl rfl)) _ le_rfl x hxX hx
      rwa [← CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two'] at h0
    · exact oddCore_inner_inf_eq_bot
        ((CFSG.RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core
          hm).1 K hK ⊤ le_top x (mem_top x) hxX hx)

theorem hypII_of_twistedE6
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤) {m : ℕ} (hm : 1 ≤ m)
    (h : ChevalleyExceptionalModel (A ⧸ center A) .twistedE6 2 m)
    (hodd : Odd (Nat.card (center A))) : HypII A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod : TwistedChevalleyModel (A ⧸ center A) .E6 (2 ^ m) := h.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hm hmod
  have hK' : Nat.card K = (2 ^ m) ^ 2 := hK
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := MulEquiv.finite_left
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ m := hσ
  obtain ⟨ht, η, hη, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion m hm).2 K hK' σ.toRingHom hσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, -, -, -, hinv⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hm K hK' σ hσ
  have hwit := secondGraphWitness_twistedE6 hm hK' σ hσ ht η hη
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  refine hypII_of_secondGraph hZ ?_ Θ ringAut_mul_comm ?_ ?_ hwit hA hodd e
  · intro α hαX hα2
    rcases rigid_or_secondGraph_twistedE6 hm hK' σ hσ α hαX hα2 with h | ⟨_ht, η', hη', φ, hφ⟩
    · exact Or.inl h
    · have e' : η' = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη', hη])
      subst e'
      exact Or.inr ⟨φ, hφ⟩
  · intro α hα hα2
    refine (hinv α hα2).resolve_right fun hσα => ?_
    obtain ⟨d, hd⟩ := exists_ne_fixed hm hK' hσ'
    have h1 : σ = 1 := hσα.1.symm.trans hα
    exact hd (by rw [show σ.toRingHom d = σ d from rfl, h1]; rfl)
  · intro x hx2 hx1
    have hx := orderOf_eq_prime hx2 hx1
    by_cases hxX : x ∈ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    · have h0 := even_exceptional_inner_involution_full_centralizer_odd_core.2 TwistTag.E6 m K σ
        hm hK hσ _ le_rfl x hxX hx
      rwa [← CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two'] at h0
    · exact oddCore_inner_inf_eq_bot
        ((CFSG.RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core
          hm).2 K hK' σ.toRingHom hσ' ⊤ le_top x (mem_top x) hxX hx)

end CFSG.ComponentClassification.RankTwoExcHypII
