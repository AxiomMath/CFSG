module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem p1OffCharAlmostSimpleNonNormalAt_reeF4
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormalAt ⟨.reeF4 m, hv⟩ := by
  have hm := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier
    (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group 2 (2 * m + 1) hm
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := hm
  have hf3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
  obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK'
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm
    (OuterComm.of_mulEquiv E (outerComm_of_isCyclic_outer hcyc))

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
