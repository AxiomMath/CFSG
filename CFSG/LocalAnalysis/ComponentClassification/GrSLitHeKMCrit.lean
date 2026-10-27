module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUComp

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.UnbalancedCorr (GSMaximalComponent)

namespace HeKMC

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_gsWeakCorr {a b : G} {J L : Subgroup G} (hC : GSWeakCorr a J b L)
    (hO : ∀ x ∈ (pPrimeCore 2 ↥J).map J.subtype, ∀ m ∈ J, x * m = m * x) :
    J ≤ centralizer ({b} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hJa, hJp, -, -, hbJ, hJb, -⟩ := hC
  have hperf : Group.IsPerfect ↥J := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJp
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJa).toMonoidHom)
      (subgroupOfEquivOfLe hJa).surjective
  have hcomm := HeUC.commute_of_commutator_central hperf.commutator_eq_top (inv_mem hbJ)
    fun m hm n hn => by
      have h := inv_mem (hJb m⁻¹ (inv_mem hm))
      rw [show (m⁻¹⁻¹ * b⁻¹ * m⁻¹ * b)⁻¹ = b⁻¹ * m * b⁻¹⁻¹ * m⁻¹ by group] at h
      exact hO _ h n hn
  intro m hm
  rw [mem_centralizer_singleton_iff]
  have h := hcomm m hm
  calc m * b = b * (b⁻¹ * m) * b := by group
    _ = b * (m * b⁻¹) * b := by rw [h]
    _ = b * m := by group

end HeKMC

end CFSG.ComponentClassification.GrSLit
