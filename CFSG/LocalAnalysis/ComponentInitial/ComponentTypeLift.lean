module

public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {H : Type*} [Group H]

theorem assembly_oddCore_eq_pPrimeCore : CFSG.Assembly.oddCore H = pPrimeCore 2 H := by
  unfold CFSG.Assembly.oddCore pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem isComponent_quotient_congr {M N : Subgroup H} [M.Normal] [N.Normal] (h : M = N)
    {K : Subgroup (H ⧸ M)} (hK : CFSG.IsComponent K) :
    CFSG.IsComponent (K.map (QuotientGroup.quotientMulEquivOfEq h).toMonoidHom) :=
  (isComponent_map_iff (QuotientGroup.quotientMulEquivOfEq h) K).2 hK

theorem component_type_perfect_local_lift (G : Type*) [Group G] [Finite G] :
    (CFSG.Assembly.IsComponentType G ↔ ∃ t : G, orderOf t = 2 ∧
        ∃ L : Subgroup (centralizer ({t} : Set G)),
          Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L)) ∧
      (CFSG.Assembly.IsComponentType G → ∃ t : G, orderOf t = 2 ∧
        ∃ L : Subgroup (centralizer ({t} : Set G)),
          Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
            CFSG.IsPComponent 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hforward : CFSG.Assembly.IsComponentType G → ∃ t : G, orderOf t = 2 ∧
      ∃ L : Subgroup (centralizer ({t} : Set G)),
        Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
          CFSG.IsPComponent 2 L := by
    rintro ⟨t, ht, K, hK⟩
    have hKn := (AssemblyBPredicates.isComponentOf_top_iff_native K).1 hK
    have hK' := isComponent_quotient_congr assembly_oddCore_eq_pPrimeCore hKn
    obtain ⟨L, hL, -⟩ := exists_isPComponent_of_isComponent 2 hK'
    have hLsub : L.IsSubnormal := by
      obtain ⟨_, _, h, _⟩ := hL
      exact h
    exact ⟨t, ht, L, CatalogueBHeldSmallCore.pComponent_perfect 2 L hL, hLsub,
      CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 L hL, hL⟩
  refine ⟨⟨fun h => ?_, ?_⟩, hforward⟩
  · obtain ⟨t, ht, L, h1, h2, h3, -⟩ := hforward h
    exact ⟨t, ht, L, h1, h2, h3⟩
  · rintro ⟨t, ht, L, -, hLsub, hLq⟩
    let ϖ : Set Nat.Primes := {q | q.val ≠ 2}
    have hcoreL : pPrimeCore 2 L = piCore ϖ L := CFSG.pPrimeCore_eq_piCore (G := L) (p := 2)
    have hLq' : CFSG.IsQuasisimple (L ⧸ piCore ϖ L) :=
      (isQuasisimple_congr (QuotientGroup.quotientMulEquivOfEq hcoreL)).1 hLq
    have hcomp := (subnormal_prime_core_component_criterion ϖ hLsub).2.2 hLq'
    have hcoreX : piCore ϖ (centralizer ({t} : Set G)) =
        CFSG.Assembly.oddCore (centralizer ({t} : Set G)) := by
      rw [assembly_oddCore_eq_pPrimeCore,
        CFSG.pPrimeCore_eq_piCore (G := centralizer ({t} : Set G)) (p := 2)]
    exact ⟨t, ht, _, (AssemblyBPredicates.isComponentOf_top_iff_native _).2
      (isComponent_quotient_congr hcoreX hcomp)⟩

end CFSG.LocalAnalysis.ComponentInitial
