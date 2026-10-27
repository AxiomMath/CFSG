module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFooteBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSLitAssembly

public section

namespace CFSG.ComponentClassification.GSFM

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

private theorem eq_of_commute_of_isCyclic_sylow {H : Type*} [Group H] [Finite H]
    (hcyc : ∀ P : Sylow 2 H, IsCyclic (P : Subgroup H)) {s t : H} (hs : orderOf s = 2)
    (ht : orderOf t = 2) (hst : s * t = t * s) : s = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (GSLit.isPGroup_two_sup_zpowers hs ht hst).exists_le_sylow
  have hsP : s ∈ (P : Subgroup H) := hP (mem_sup_right (mem_zpowers s))
  have htP : t ∈ (P : Subgroup H) := hP (mem_sup_left (mem_zpowers t))
  have := hcyc P
  have hs' : orderOf (⟨s, hsP⟩ : (P : Subgroup H)) = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have ht' : orderOf (⟨t, htP⟩ : (P : Subgroup H)) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hcard : Nat.card (zpowers (⟨s, hsP⟩ : (P : Subgroup H))) =
      Nat.card (zpowers (⟨t, htP⟩ : (P : Subgroup H))) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hs', ht']
  have heq := IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  have htmem : (⟨t, htP⟩ : (P : Subgroup H)) ∈ zpowers (⟨s, hsP⟩ : (P : Subgroup H)) :=
    heq ▸ mem_zpowers _
  rcases UnbalancedGS.DihedralPair.mem_zpowers_eq_one_or_eq hs' htmem with h1 | h1
  · rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  · exact (congrArg Subtype.val h1).symm

variable {G : Type*} [Group G] [Finite G]

theorem not_footeStep_of_isCyclic_kernel {L K : Subgroup G}
    (hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))) :
    ¬ FooteLit.FooteStep L K := by
  rintro ⟨a, b, hL, hK, hab, hne, hbL, -⟩
  have haL : a ∈ coreActionKernel L := mem_coreActionKernel_of_le_centralizer hL.2.1
  have h := eq_of_commute_of_isCyclic_sylow hcyc (s := ⟨a, haL⟩) (t := ⟨b, hbL⟩)
    (by rw [Subgroup.orderOf_mk]; exact hL.1) (by rw [Subgroup.orderOf_mk]; exact hK.1)
    (Subtype.ext hab)
  exact hne (congrArg Subtype.val h)

theorem eq_of_footeReach_of_isCyclic_kernel {L M : Subgroup G}
    (hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L)))
    (h : FooteLit.FooteReach L M) : M = L := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨K, hLK, -⟩
  · rfl
  · exact absurd hLK (not_footeStep_of_isCyclic_kernel hcyc)

theorem footeMaximal_of_isCyclic_kernel {b : G} {L : Subgroup G} (hb : orderOf b = 2)
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))) :
    FooteLit.FooteMaximal L := by
  refine ⟨⟨b, hb, hLb, hL⟩, fun M hM => ?_⟩
  obtain rfl := eq_of_footeReach_of_isCyclic_kernel hcyc hM
  exact ⟨MulEquiv.refl _⟩

theorem footeMaximal_of_b2Setting {G : Type} [Group G] [Finite G] {a : G} {J S : Subgroup G}
    (h : B2Setting a J S) : FooteLit.FooteMaximal J :=
  ⟨⟨a, h.orderOf_eq, h.le_centralizer, h.isPComponent⟩, fun _ hM =>
    GrSLit.zStar_equiv_of_weakReach h (GrSLit.gsWeakReach_of_footeReach hM)⟩

theorem exists_footeMaximal_component_of_small_types
    (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hGF : GloballyFirstRankTwoInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hsmall : ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2))
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧ GSMaximalComponent L ∧
      FooteLit.FooteMaximal L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) := by
  obtain ⟨a, x, J, hJ, hbound⟩ :=
    exists_maximal_unbalancing_triple_bounded hTB hSA hGF hnonab hK hz hU htriple
  have htype := unbalancing_component_type_of_small hTB hSA hnonab hK hz hU hsmall hJ.1
  suffices hmax : GSMaximalComponent J ∧ FooteLit.FooteMaximal J from
    ⟨a, x, J, hJ, hmax.1, hmax.2, htype⟩
  rcases hB X hnonab hK hz hU a x J hJ hbound (htype.imp id Or.inl) with
    ⟨-, b, L, ρ, e, hb, hLb, hL, hρ, hρ2, he, hLie, hbK, hP⟩ | ⟨hiso, hcentral⟩
  · refine absurd ⟨b, L, hb, hLb, hL, gsMaximalComponent_of_cyclic_kernel hb hLb hL hP,
      ⟨ρ, 2 * e, hρ, hρ2, by omega, ?_, hLie⟩, isCyclic_sylow_of_eq_zpowers hbK hP⟩
      (hH X hnonab hK hz hU)
    have h3 : 3 ≤ ρ := by have := hρ.two_le; omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ ρ ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ ρ ^ (2 * e) := Nat.pow_le_pow_right hρ.pos (by omega)
  · exact ⟨gsMaximalComponent_of_B2 hJ.1.1 hJ.1.2.2.2.1 hJ.1.2.2.2.2.1 hiso hcentral,
      GrSLit.footeMaximal_of_B2 hJ.1.1 hJ.1.2.2.2.1 hJ.1.2.2.2.2.1 hiso hcentral⟩

end CFSG.ComponentClassification.GSFM
