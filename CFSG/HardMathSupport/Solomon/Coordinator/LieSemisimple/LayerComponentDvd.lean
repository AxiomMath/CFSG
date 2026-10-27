module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma

public section

namespace CFSG

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_isComponentOf_dvd_card_of_dvd_card_glaLayer {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (h : p ∣ Nat.card (GLALayer X)) :
    ∃ J : Subgroup G, IsComponentOf J X ∧ p ∣ Nat.card J := by
  classical
  have hEq : GLALayer X = (CFSG.layer ↥X).map X.subtype :=
    le_antisymm (glaLayer_le_map_layer X) (map_layer_le_glaLayer X)
  have hcard : Nat.card (GLALayer X) = Nat.card (CFSG.layer ↥X) := by
    rw [hEq, Subgroup.card_map_of_injective X.subtype_injective]
  have hdvd : p ∣ Nat.card (CFSG.layer ↥X) := hcard ▸ h
  have hdvd' : p ∣ Nat.card (∀ K : CFSG.LocalCores.ComponentIndex ↥X, K.1) := by
    have h1 : p ∣ Nat.card (CFSG.LocalCores.layerMul ↥X).range := by
      rwa [CFSG.LocalCores.layerMul_range]
    exact h1.trans (Subgroup.card_range_dvd _)
  rw [Nat.card_pi] at hdvd'
  obtain ⟨K, -, hK⟩ :=
    (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
      (fun K : CFSG.LocalCores.ComponentIndex ↥X => Nat.card K.1)).1 hdvd'
  refine ⟨K.1.map X.subtype, isComponentOf_map_subtype K.2, ?_⟩
  rwa [Subgroup.card_map_of_injective X.subtype_injective]

theorem exists_glaPComponent_dvd_card_of_dvd_card_glaLayer {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (h : p ∣ Nat.card (GLALayer X)) :
    ∃ J : Subgroup G, GLAPComponent p X J ∧ p ∣ Nat.card J := by
  obtain ⟨J, hJ, hJdvd⟩ := exists_isComponentOf_dvd_card_of_dvd_card_glaLayer hp h
  have hqn : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hJ.2.2)
  exact ⟨J, CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hJ.2.1 hJ.2.2
    (CFSG.dvd_card_quotient_center_of_quasisimple hqn hp hJdvd), hJdvd⟩

end CFSG

end
