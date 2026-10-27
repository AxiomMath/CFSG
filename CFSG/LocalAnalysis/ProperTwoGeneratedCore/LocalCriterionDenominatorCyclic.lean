module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem odd_commutative_subgroup_cyclic (W : Subgroup G)
    (hodd : Odd (Nat.card W)) (hcomm : IsMulCommutative W)
    (hSylow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G, IsCyclic P) :
    IsCyclic W := by
  let : IsMulCommutative W := hcomm
  let : IsZGroup W :=
    { isZGroup := by
        intro p hp P
        let : Fact p.Prime := ⟨hp⟩
        by_cases hp2 : p = 2
        · subst p
          have hPodd : Odd (Nat.card P) :=
            hodd.of_dvd_nat (P : Subgroup W).card_subgroup_dvd_card
          have hcard : Nat.card P = 1 :=
            P.isPGroup'.card_eq_or_dvd.resolve_right hPodd.not_two_dvd_nat
          let : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
          exact isCyclic_of_subsingleton
        · let i : W →* G := W.subtype
          let Q : Subgroup G := (P : Subgroup W).map i
          have hQp : IsPGroup p Q := P.isPGroup'.map i
          obtain ⟨R, hQR⟩ := hQp.exists_le_sylow
          let : IsCyclic R := hSylow p hp2 R
          let : IsCyclic Q := Subgroup.isCyclic_of_le hQR
          let e : P ≃* Q := Subgroup.equivMapOfInjective (P : Subgroup W) i W.subtype_injective
          exact isCyclic_of_injective e.toMonoidHom e.injective }
  infer_instance

theorem linear_model_oddSylow_cyclic {K : Type} [Field K] [Finite K]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (e : G ≃* GLAProj (GLASLGroup (Fin 2) K)) :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G, IsCyclic P := by
  exact lemma114_psl2_oddSylow_isCyclic_of_equiv hf
    (e.trans (glaSL2EquivNative f hf hcard))

theorem suzuki_model_oddSylow_cyclic {K : Type} [Field K] [Finite K]
    (a : ℕ) (ha : 1 ≤ a) (hcard : Nat.card K = 2 ^ (2 * a + 1))
    (e : G ≃* GLASzGroup a K) :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G, IsCyclic P := by
  exact lemma114_suzuki_oddSylow_isCyclic_of_equiv
    ((e.trans (glaSzEquivNative a ha hcard)).trans (suzukiCoverNativeEquiv a))

theorem pair_hull_intersection_cyclic (H : Subgroup G)
    (a b : pointRightCosetSpace H) (t v : G) (ht : orderOf t = 2)
    (hflip : pointRightCosetMul H a t = b) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({v} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({v} : Set G))).Normal)
    (htL : t ∈ L)
    (hWodd : Odd (Nat.card (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)))
    (hCtwo : IsPGroup 2 (Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)))
    (hSylow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p L, IsCyclic P) :
    IsCyclic (L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  obtain ⟨_, htW, _⟩ := pair_hull_orbit_premises H a b t v ht hflip L hLC hLnormal htL
  have hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ :=
    odd_pair_intersection_trivial_centralizer L W inf_le_left t htL hWodd hCtwo
  obtain ⟨hodd, hcomm, _⟩ :=
    normalized_subgroup_inversion_of_trivial_centralizer W t ht htW hfixed
  let U := W.subgroupOf L
  let e : U ≃* W := Subgroup.subgroupOfEquivOfLe (show W ≤ L from inf_le_left)
  have hUodd : Odd (Nat.card U) := (Nat.card_congr e.toEquiv).symm ▸ hodd
  have hUcomm : IsMulCommutative U := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    rw [map_mul, map_mul]
    exact (@IsMulCommutative.is_comm W _ hcomm).comm _ _
  let : IsCyclic U := odd_commutative_subgroup_cyclic U hUodd hUcomm hSylow
  exact isCyclic_of_surjective e e.surjective

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
