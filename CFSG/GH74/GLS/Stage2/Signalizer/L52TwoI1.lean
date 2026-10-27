module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_goodI1 [Finite G] {H U : Subgroup G} (hU2 : IsPGroup 2 ↥U) (hUH : U ≤ H)
    (hq : ∃ q : ℕ, Odd q ∧ 3 < q ∧
      IVK.IsL2 (↥(pLayerOf 2 (centralizer (U : Set G))) ⧸ pPrimeCore 2 ↥(pLayerOf 2 (centralizer (U : Set G))))
        (fun r => r = q))
    (hcov : pLayerOf 2 (centralizer (U : Set G)) ≤
      (H ⊓ pLayerOf 2 (centralizer (U : Set G))) ⊔ pPrimeCoreOf 2 (pLayerOf 2 (centralizer (U : Set G)))) :
    ∃ I₁ : Subgroup G, GoodI1 H U I₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hqo, hq3, hS⟩ := hq
  set C : Subgroup G := centralizer (U : Set G) with hC
  set L : Subgroup G := pLayerOf 2 C with hL
  set X : Subgroup G := H ⊓ C with hX
  set B : Subgroup G := H ⊓ L with hB
  have hLC : L ≤ C := sSup_le fun K hK => hK.1
  have hCL : C ≤ normalizer (L : Set G) := by
    rw [hL, I1.pLayerOf_eq_map_pLayer]
    have hch : (pLayer ↥C 2).Characteristic :=
      ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
    exact Subgroup.le_normalizer.trans
      (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pLayer ↥C 2))
  have hXO : ∀ x ∈ X, ∀ o ∈ pPrimeCoreOf 2 L, x * o * x⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro x hx o ho
    have hx' : x ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) :=
      LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥L)
        (hCL hx.2)
    exact (Subgroup.mem_normalizer_iff.1 hx' o).1 ho
  have hXB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun x hx b hb =>
    ⟨H.mul_mem (H.mul_mem hx.1 hb.1) (H.inv_mem hx.1),
      (Subgroup.mem_normalizer_iff.1 (hCL hx.2) b).1 hb.2⟩
  have hBL : B ≤ L := inf_le_right
  have hsimple : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) := I1.isSimpleGroup_of_isL2 hq3 hS
  have hqs : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := I1.isQuasisimple_of_isL2 hq3 hS
  have heven : Even (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) :=
    ComponentClassification.Burgoyne.even_card_of_isQuasisimple hqs
  have hZ : Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ :=
    GH74.GLS.Stage2.Local.P27.S45.center_eq_bot_of_isL2 hS
  obtain ⟨I, hIB, hIperf, hIX, hIsurj⟩ := I1.exists_perfect_core (X := X) hBL hXB hqs.1 hcov
  have hIL : I ≤ L := hIB.trans hBL
  have hIH : I ≤ H := hIB.trans inf_le_left
  have hIX' : I ≤ X := le_inf hIH (hIL.trans hLC)
  refine ⟨I, hIH, fun i hi u hu => ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.1 (hLC (hIL hi)) u hu
  · have hqI := I1.isQuasisimple_image hIL hIX' hXO hIX hsimple heven hqs hIsurj
    have hlayer : I ≤ pLayerOf 2 X := I1.le_pLayerOf_of_perfect_normal hIX' hIX hIperf hqI
    exact I1.barIn_le_layer_of_le_pLayerOf (hlayer.trans (I1.pLayerOf_inf_centralizer_le hUH hU2))
  · exact I1.exists_isFourSubgroup_of_cover hqo hIL hS hIsurj
  · intro i hi hcomm
    exact I1.odd_orderOf_of_comm_mem hIL hIH hsimple heven hZ hIsurj hi hcomm

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
