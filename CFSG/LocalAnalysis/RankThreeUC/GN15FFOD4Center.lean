module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalElementary
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Hopf
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3009
public import Certificates.Certificate12041
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.LieType.Steinberg.CentralExt CFSG.Open

private theorem genericOrders_pomegaPlus_four_two (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 f = (1, 1) := by
  have heven : Even (2 ^ f) := by
    rw [Nat.even_pow]
    exact ⟨even_two, by omega⟩
  simp [CFSG.Blueprint.Multiplier.genericOrders, heven]

private theorem exceptionalOrders_pomegaPlus_four_two (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

private theorem genericOrders_pomegaPlus_four_one :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 1 = (1, 1) := by
  simp [CFSG.Blueprint.Multiplier.genericOrders]

private theorem exceptionalOrders_pomegaPlus_four_one :
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 1 = (2, 2) := by
  simp [CFSG.Blueprint.Multiplier.exceptionalOrders]

private theorem card_generic_pomegaPlus_four_two (f : ℕ) (hf : 2 ≤ f) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 f) = 1 := by
  have hc : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k => by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k), Nat.card_zmod]
  have hgo := genericOrders_pomegaPlus_four_two f hf
  simp [CFSG.Blueprint.Multiplier.generic, hgo]

private theorem card_generic_exceptional_pomegaPlus_four_one :
    Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .POmegaPlus 4 2 1) = 4 := by
  have hc : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k => by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k), Nat.card_zmod]
  have hgo := genericOrders_pomegaPlus_four_one
  have heo := exceptionalOrders_pomegaPlus_four_one
  simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    hgo, heo]

private theorem eq_one_of_odd_dvd_four {n : ℕ} (hodd : Odd n) (h : n ∣ 4) : n = 1 := by
  have h2 : n ∣ 2 ^ 2 := by norm_num at h ⊢; exact h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exfalso
      exact hodd.not_two_dvd_nat (by rw [hk, pow_succ]; exact dvd_mul_left 2 (2 ^ k))
  rw [hk, hk0, pow_zero]

private theorem card_center_dvd_of_griessEquiv {V : Type} [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L) {X : Type} [Group X]
    (eX : L ⧸ Subgroup.center L ≃* X) {A : Type} [Group A] [Finite A]
    (e : griessHopfMultiplier X ≃* A) :
    Nat.card (Subgroup.center L) ∣ Nat.card A := by
  have : Group.IsPerfect L := hperf
  let π : L →* X := eX.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext y
    rw [MonoidHom.mem_ker]
    change eX (QuotientGroup.mk' (Subgroup.center L) y) = 1 ↔ _
    rw [map_eq_one_iff eX eX.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i1021_card_ker_dvd π hπ hker.le
    Group.IsPerfect.commutator_eq_top e
  rwa [hker] at h

private theorem exists_mulEquiv_of_center_eq_bot {V : Type} [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f)
    (eX : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (hZ : Subgroup.center L = ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* orthElementaryGroup (quadPlus 4 K)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have e0 : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
    ⟨e0.symm.trans (eX.trans (OrthogonalSplit.statedProjOmegaPlusEquiv (r := 4) (by norm_num)))⟩⟩

theorem center_eq_bot_of_model_of_two_le {V : Type} [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨-, K, hF, hFin, hK, ⟨eX⟩⟩ := hmodel
  let : Field K := hF
  let : Finite K := hFin
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨-, ⟨em⟩⟩ := GriessClassical.of_mulEquiv eX
    (SpinPlusClosed.pomegaPlus_hopfMultiplier (n := 4) (K := K) (p := 2) (f := f)
      (by norm_num) hK hK4)
  have : Finite (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 f) := by
    unfold CFSG.Blueprint.Multiplier.generic
    rw [genericOrders_pomegaPlus_four_two f hf]
    infer_instance
  have hdvd := card_center_dvd_of_griessEquiv L hperf (MulEquiv.refl _) em
  rw [card_generic_pomegaPlus_four_two f hf] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp hdvd)

theorem center_eq_bot_of_model_one
    {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hperf : Group.IsPerfect L)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 1) :
    Subgroup.center L = ⊥ := by
  obtain ⟨-, ⟨em⟩⟩ := GriessClassical.pomegaPlus_four_two_row
    (X := L ⧸ Subgroup.center L) ⟨hmodel.1, Or.inl hmodel⟩
  have : Finite (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .POmegaPlus 4 2 1) := by
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [genericOrders_pomegaPlus_four_one, exceptionalOrders_pomegaPlus_four_one]
    infer_instance
  have hdvd := card_center_dvd_of_griessEquiv L hperf (MulEquiv.refl _) em
  rw [card_generic_exceptional_pomegaPlus_four_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _
    (eq_one_of_odd_dvd_four
      (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.odd_card_center_of_isIrrOn hV hirr) hdvd)

theorem exists_mulEquiv_of_model_of_two_le {V : Type} [CommGroup V] [Finite V]
    (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* orthElementaryGroup (quadPlus 4 K)) := by
  have hZ := center_eq_bot_of_model_of_two_le L hperf hf hmodel
  obtain ⟨-, K, hF, hFin, hK, ⟨eX⟩⟩ := hmodel
  let : Field K := hF
  let : Finite K := hFin
  exact exists_mulEquiv_of_center_eq_bot L hK eX hZ

theorem exists_mulEquiv_of_model
    {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hperf : Group.IsPerfect L) {f : ℕ}
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (L ≃* orthElementaryGroup (quadPlus 4 K)) := by
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · have hf1 : f = 1 := by
      have hfpos : 1 ≤ f := hmodel.1.2.1
      omega
    obtain rfl : f = 1 := hf1
    have hZ := center_eq_bot_of_model_one hV L hirr hperf hmodel
    obtain ⟨-, K, hF, hFin, hK, ⟨eX⟩⟩ := hmodel
    let : Field K := hF
    let : Finite K := hFin
    exact exists_mulEquiv_of_center_eq_bot L hK eX hZ
  · exact exists_mulEquiv_of_model_of_two_le L hperf hge hmodel

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
