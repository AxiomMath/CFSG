module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitChainWeak
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem gsFixedLayer_le_footeFixed' (L : Subgroup G) (b : G) :
    gsFixedLayer L b ≤ FooteLit.footeFixed L b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [gsFixedLayer, map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  obtain ⟨-, hres, -⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 X).mp hX
  intro x hx
  have hxtop : (⟨x, hx⟩ : X) ∈ CatalogueBPrimeJoin.primeResidual 2 X := hres ▸ mem_top _
  have hle : CatalogueBPrimeJoin.primeResidual 2 X ≤
      ((FooteLit.footeFixed L b).comap (L ⊓ centralizer ({b} : Set G)).subtype).comap
        X.subtype := by
    refine sSup_le fun P hP => ?_
    intro y hy
    obtain ⟨i, hi⟩ := hP ⟨y, hy⟩
    have hyi : (((y : X) : ↥(L ⊓ centralizer ({b} : Set G))) : G) ^ 2 ^ i = 1 := by
      have := congrArg (fun z : P => (((z : X) : ↥(L ⊓ centralizer ({b} : Set G))) : G)) hi
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyi)
    exact subset_closure ⟨mem_sup_left ((y : X) : ↥(L ⊓ centralizer ({b} : Set G))).2, j, hj⟩
  exact hle hxtop

omit [Finite G] in
theorem le_conjClosure' (Y E : Subgroup G) : Y ≤ FooteLit.conjClosure Y E := fun y hy =>
  subset_closure (Set.mem_iUnion₂.mpr ⟨1, one_mem E, by rw [conjugate_one]; exact hy⟩)

theorem gsWeakCorr_of_footeStep {L K : Subgroup G} (h : FooteLit.FooteStep L K) :
    ∃ a b : G, GSWeakCorr a L b K := by
  obtain ⟨a, b, hL, hK, hab, -, hbL, hcl⟩ := h
  refine ⟨a, b, hL.1, hK.1, hab, hL.2.1, hL.2.2, hK.2.1, hK.2.2, (mem_coreActionKernel.mp hbL).1,
    (mem_coreActionKernel.mp hbL).2, ?_⟩
  rw [← hcl]
  exact (gsFixedLayer_le_footeFixed' L b).trans (le_conjClosure' _ _)

theorem gsWeakReach_of_footeReach {L M : Subgroup G} (h : FooteLit.FooteReach L M) :
    GSWeakReach L M :=
  Relation.ReflTransGen.mono (fun _ _ hst => gsWeakCorr_of_footeStep hst) _ _ h

theorem footeMaximal_of_B2 {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hiso : ∀ b : G, orderOf b = 2 → b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      ∃ K : Subgroup G, GSIsoCorr a J b K)
    (hcentral : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
      b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
      (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
      GSIsoCorr a J b K →
      ∀ S : Subgroup G, S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
        (∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
          (P : Subgroup _) =
            S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
        b ∈ S → (∀ s ∈ S, s * b = b * s) →
        S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
          ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
            (P : Subgroup _) =
              S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G))) :
    FooteLit.FooteMaximal J :=
  ⟨⟨a, ha, hJa, hJ⟩, fun _ hM =>
    zStar_equiv_of_weakReach_of_B2 ha hJa hJ hiso hcentral (gsWeakReach_of_footeReach hM)⟩

end CFSG.ComponentClassification.GrSLit
