module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainTargetProduction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrReach

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type*} [Group G]

@[expose] def GSWeakCorr (a : G) (J : Subgroup G) (b : G) (K : Subgroup G) : Prop :=
  orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧
    J ≤ centralizer ({a} : Set G) ∧ IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧
    K ≤ centralizer ({b} : Set G) ∧ IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G))) ∧
    b ∈ normalizer (J : Set G) ∧ (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) ∧
    UnbalancedGS.gsFixedLayer J b ≤ K ⊔ conjugate K a

@[expose] def GSWeakReach (J K : Subgroup G) : Prop :=
  Relation.ReflTransGen (fun J' K' : Subgroup G => ∃ a b : G, GSWeakCorr a J' b K') J K

theorem GSWeakCorr.of_gsCorr {a b : G} {J K : Subgroup G} (h : UnbalancedGS.GSCorr a J b K) :
    GSWeakCorr a J b K := by
  obtain ⟨ha, hb, hab, hJa, hJ, hKb, hK, hbJ, hJb, heq⟩ := h
  refine ⟨ha, hb, hab, hJa, hJ, hKb, hK, hbJ, hJb, ?_⟩
  rw [heq]
  exact (UnbalancedGS.gsFixedLayer_le_inf _ a).trans inf_le_left

theorem GSWeakReach.refl (J : Subgroup G) : GSWeakReach J J :=
  Relation.ReflTransGen.refl

theorem GSWeakReach.single {a b : G} {J K : Subgroup G} (h : GSWeakCorr a J b K) :
    GSWeakReach J K :=
  Relation.ReflTransGen.single ⟨a, b, h⟩

theorem GSWeakReach.tail {a b : G} {J K L : Subgroup G} (h : GSWeakReach J K)
    (hC : GSWeakCorr a K b L) : GSWeakReach J L :=
  Relation.ReflTransGen.tail h ⟨a, b, hC⟩

theorem GSWeakReach.trans {J K L : Subgroup G} (h₁ : GSWeakReach J K) (h₂ : GSWeakReach K L) :
    GSWeakReach J L :=
  Relation.ReflTransGen.trans h₁ h₂

theorem GSWeakReach.of_gsReach {J K : Subgroup G} (h : GSReach J K) : GSWeakReach J K :=
  Relation.ReflTransGen.mono (fun _ _ ⟨a, b, hC⟩ => ⟨a, b, GSWeakCorr.of_gsCorr hC⟩) _ _ h.2

theorem exists_gsWeakCorr_of_target {G : Type} [Group G] [Finite G]
    (hS : SchreierFor Blueprint.Catalog) (hK : Assembly.KProper Blueprint.Catalog G)
    {a x : G} {J : Subgroup G} (hU : GSUnbalancingTriple a x J) {b : G} (hb : orderOf b = 2)
    (hbZ : b ∉ center G) (hab : a * b = b * a) (hxb : x * b = b * x)
    (hbJ : b ∈ normalizer (J : Set G))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) :
    ∃ M : Subgroup G, GSWeakCorr a J b M ∧ GSUnbalancingTriple b x M ∧
      (pPrimeCore 2 J).index ≤ (pPrimeCore 2 M).index ∧
      (M ≠ conjugate M a ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 M).index →
        UnbalancedGS.GSCorr a J b M) := by
  obtain ⟨ha, -, -, hJa, hJ, -, -⟩ := gsUnbalancingTriple_iff.mp hU
  obtain ⟨M, hMb, hM, hUM, hTM, -, hidx, hcorr, -⟩ :=
    UGSChain.kProper_unbalancing_orbit_target_production_of_schreier hS hK hU hb hbZ hab hxb
      hbJ hJb
  exact ⟨M, ⟨ha, hb, hab, hJa, hJ, hMb, hM, hbJ, hJb, hTM⟩, hUM, hidx, hcorr⟩

end CFSG.ComponentClassification.GrSLit
