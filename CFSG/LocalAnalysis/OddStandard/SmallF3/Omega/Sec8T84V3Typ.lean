module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Early
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
import CFSG.Goldschmidt.BasicG
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84v_card_model_psu4 {X : Type} [Group X] (h : LieModel X .PSU 4 3 1) :
    Nat.card X = 3265920 := by
  rw [h.card_eq_lieOrd (by norm_num)]
  decide +kernel

theorem sec8t84v_om6m_false (hM : Asc82Tab6M) (hI4 : Sec8T84FactI4m) {G : Type} [Group G]
    [Finite G] {t : G} {K K0 U : Subgroup G} (hK : IsOm6M K) (ht2 : orderOf t = 2)
    (htK : t ∈ normalizer (K : Set G))
    (hK0 : IsComponentIn K0 (K ⊓ centralizer ({t} : Set G))) (hL29 : IsL29 K0)
    (hU : IsElemAb2 U 4) (hUK : U ≤ K) (htU : t ∈ normalizer (U : Set G))
    (hinner : ∀ u ∈ K ⊓ centralizer ({t} : Set G), orderOf u = 2 → InnerOn K0 u) : False := by
  have hle : K0 ≤ layerCent K t := hK0.le_layer
  rcases hM.classify G K hK t ht2 htK with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hKt : K ≤ centralizer ({t} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h1 k hk)
    have hKc : IsComponentIn K (K ⊓ centralizer ({t} : Set G)) := by
      rw [inf_eq_left.mpr hKt]
      exact isComponentIn_of_normal le_rfl hK.1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
    have heq : K0 = K := hK0.eq_of_le hKc (hK0.le.trans inf_le_left)
    subst heq
    have c1 := ff_card_isL29 hL29
    have c2 := sec8t84v_card_model_psu4 hK.2
    omega
  · have hbot : layerCent K t = ⊥ := (hM.layer_trivial G K hK t ht2 htK).mpr (Or.inl h2)
    rw [hbot] at hle
    exact hK0.ne_bot (le_bot_iff.mp hle)
  · obtain ⟨u, hu, hu2, hnot⟩ := hI4 G K hK t ht2 htK h3 K0 hK0
    exact hnot (hinner u hu hu2)
  · have hE : IsU33 (layerCent K t) := hM.layer_rho G K hK t ht2 htK h4
    have hEc : IsComponentIn (layerCent K t) (K ⊓ centralizer ({t} : Set G)) :=
      isComponentIn_layerCent (Or.inr (Or.inr (Or.inl hE)))
    have heq : K0 = layerCent K t := hK0.eq_of_le hEc hle
    rw [← heq] at hE
    exact ff_not_isU33_and_isL29 hE hL29
  · have hE : IsOmega5 (layerCent K t) := hM.layer_i1 G K hK t ht2 htK h5
    have hEc : IsComponentIn (layerCent K t) (K ⊓ centralizer ({t} : Set G)) :=
      isComponentIn_layerCent (Or.inl hE)
    have heq : K0 = layerCent K t := hK0.eq_of_le hEc hle
    rw [← heq] at hE
    exact ff_not_isOmega5_and_isL29 hE hL29
  · have hbot : layerCent K t = ⊥ := (hM.layer_trivial G K hK t ht2 htK).mpr (Or.inr h6)
    rw [hbot] at hle
    exact hK0.ne_bot (le_bot_iff.mp hle)
  · exact hM.outer_swaps G K hK t ht2 htK h7 U hUK hU htU

end CFSG.OddStandard.SmallF3.Omega
