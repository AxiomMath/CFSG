module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45d
public import CFSG.Walter.AStar.Subnormal

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem isTwoQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsTwoQuasisimple A) : IsTwoQuasisimple B := by
  obtain ⟨hp, hq⟩ := h
  have : Group.IsPerfect A := hp
  exact ⟨Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective,
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) hq⟩

theorem isTwoComponent_iff_isPComponent {G : Type*} [Group G] [Finite G] (J : Subgroup G) :
    IsTwoComponent J ↔ IsPComponent 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple]
  constructor
  · rintro ⟨hsub, hperf, hq⟩
    have : Group.IsPerfect ↥J := hperf
    exact ⟨hsub, primeResidual_eq_top_of_isPerfect, hq⟩
  · rintro ⟨hsub, hres, hq⟩
    exact ⟨hsub, CatalogueBHeldSmallCore.pComponent_perfect 2 J
      ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 J).mpr
        ⟨hsub, hres, hq⟩), hq⟩

theorem isTwoComponentIn_iff {G : Type*} [Group G] [Finite G] {J A : Subgroup G} (hJA : J ≤ A) :
    IsTwoComponentIn J A ↔ IsPComponent 2 (J.subgroupOf A) := by
  rw [← isTwoComponent_iff_isPComponent]
  constructor
  · rintro ⟨-, hsub, hq⟩
    exact ⟨hsub, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJA).symm hq⟩
  · rintro ⟨hsub, hq⟩
    exact ⟨hJA, hsub, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJA) hq⟩

theorem pPrimeCore_eq_bot_of_isSubnormal {G : Type*} [Group G] [Finite G]
    (hG : pPrimeCore 2 G = ⊥) {J : Subgroup G} (hJ : J.IsSubnormal) : pPrimeCore 2 ↥J = ⊥ := by
  have h := Walter.map_pPrimeCore_le_of_isSubnormal hJ
  rw [hG, le_bot_iff, map_eq_bot_iff_of_injective _ J.subtype_injective] at h
  exact h

theorem isTwoComponent_iff_isComponent {G : Type*} [Group G] [Finite G]
    (hG : pPrimeCore 2 G = ⊥) (J : Subgroup G) : IsTwoComponent J ↔ IsComponent J := by
  constructor
  · rintro ⟨hsub, -, hq⟩
    have hO := pPrimeCore_eq_bot_of_isSubnormal hG hsub
    refine ⟨LocalCores.isQuasisimple_of_mulEquiv ?_ hq, hsub⟩
    exact (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  · rintro ⟨hq, hsub⟩
    have hO := pPrimeCore_eq_bot_of_isSubnormal hG hsub
    refine ⟨hsub, hq.1, LocalCores.isQuasisimple_of_mulEquiv ?_ hq⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm

theorem twoLayer_eq_layer {G : Type*} [Group G] [Finite G] (hG : pPrimeCore 2 G = ⊥) :
    twoLayer G = layer G := by
  unfold twoLayer; simp only [CFSG.layer.eq_sSup]
  congr 1
  ext J
  exact isTwoComponent_iff_isComponent hG J

end CFSG.ComponentClassification.HarrisLit
