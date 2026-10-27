module

public import CFSG.Goldschmidt.StatementsG
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverInvariants
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Goldschmidt

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

namespace NewPair

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

theorem suzukiCoverDerived_additive_action (hm : 0 < m) (x : Kˣ)
    (w : Additive (commutator (suzukiCoverRoot m))) :
    (suzukiCoverDerivedEquiv m hm).toAdditiveLeft
      (Additive.ofMul (coverDerivedAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) w.toMul)) =
      (suzukiCoverNorm m x : K) * (suzukiCoverDerivedEquiv m hm).toAdditiveLeft w :=
  suzukiCoverDerived_action m hm x w.toMul

theorem suzukiCoverDerived_inverse_action (hm : 0 < m) (x : Kˣ) (c : K) :
    (suzukiCoverDerivedEquiv m hm).toAdditiveLeft.symm ((suzukiCoverNorm m x : K) * c) =
      Additive.ofMul (coverDerivedAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x)
        ((suzukiCoverDerivedEquiv m hm).toAdditiveLeft.symm c).toMul) := by
  apply (suzukiCoverDerivedEquiv m hm).toAdditiveLeft.injective
  rw [AddEquiv.apply_symm_apply, suzukiCoverDerived_additive_action, AddEquiv.apply_symm_apply]

theorem suzukiCoverMixedInvariant_eq_zero (hm : 2 ≤ m)
    (b : Additive (commutator (suzukiCoverRoot m)) →+
      Additive (Abelianization (suzukiCoverRoot m)) →+ ZMod 2)
    (hb : CoverMixedInvariant (suzukiCoverRoot m) (suzukiCoverTorus m)
      (suzukiCoverTorus_le_normalizer m) b) : b = 0 := by
  have hm0 : 0 < m := by omega
  let eD := (suzukiCoverDerivedEquiv m hm0).toAdditiveLeft
  let eA := (suzukiCoverAbelianEquiv m hm0).toAdditiveLeft
  have hf := CFSG.ProperTwoGeneratedCore.Lemma37.CoverSuzuki.suzuki_pairing_eq_zero m hm
    (fun a c => b (eD.symm c) (eA.symm a))
    (fun a a' c => by simp only [map_add])
    (fun a c c' => by simp only [map_add, AddMonoidHom.add_apply])
    (fun y hy a c => by
      let x : Kˣ := Units.mk0 y hy
      have hD : eD.symm (y * suzukiCoverTits m y * c) =
          Additive.ofMul (coverDerivedAction (suzukiCoverRoot m) (suzukiCoverTorus m)
            (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) (eD.symm c).toMul) :=
        suzukiCoverDerived_inverse_action m hm0 x c
      have hA : eA.symm (y * a) =
          Additive.ofMul (coverAbelianAction (suzukiCoverRoot m) (suzukiCoverTorus m)
            (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) (eA.symm a).toMul) :=
        suzukiCoverAbelian_inverse_action m hm0 x a
      show b (eD.symm (y * suzukiCoverTits m y * c)) (eA.symm (y * a)) =
        b (eD.symm c) (eA.symm a)
      rw [hD, hA]
      exact hb _ _ _)
  apply AddMonoidHom.ext
  intro w
  apply AddMonoidHom.ext
  intro v
  have h := hf (eA v) (eD w)
  change b (eD.symm (eD w)) (eA.symm (eA v)) = 0 at h
  simpa only [AddEquiv.symm_apply_apply, AddMonoidHom.zero_apply] using h

theorem suzukiCover_kernel_eq_bot {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (hm : 2 ≤ m) (η : E →* SuzukiMatrixGroup m) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hm0 : 0 < m := by omega
  have : Finite (SuzukiMatrixGroup m) := Finite.of_surjective η hη
  let Q : Sylow 2 (SuzukiMatrixGroup m) := suzukiCoverSylow m hm0
  let : IsElementaryAbelian 2 (commutator (Q : Subgroup (SuzukiMatrixGroup m))) :=
    (suzukiCoverRoot_layers_elementary m hm0).1
  let : IsElementaryAbelian 2 (Abelianization (Q : Subgroup (SuzukiMatrixGroup m))) :=
    (suzukiCoverRoot_layers_elementary m hm0).2
  exact central_two_cover_bilinear_Sylow_obstruction η hη hc hp Q
    (suzukiCoverRoot_structure m hm0).2.2.1.le (suzukiCoverTorus m)
    (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorus_odd m hm0)
    (suzukiCoverMixedInvariant_eq_zero m hm) (suzukiCoverAbelian_invariant_eq_zero m hm0)

theorem suzuki_center_eq_bot {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hp : IsPGroup 2 (Subgroup.center L)) {n : ℕ} (hn : 2 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* CFSG.Open.Sz n) : Subgroup.center L = ⊥ := by
  let e' := e.trans (suzukiCoverNativeEquiv n)
  let η := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : η.ker = Subgroup.center L :=
    CFSG.QuasithinUnique.RankOneRecog.ker_comp_centerQuotient e'
  have hη : Function.Surjective η := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hp' : IsPGroup 2 η.ker := by
    rw [hker]
    exact hp
  exact hker.symm.trans (suzukiCover_kernel_eq_bot n hn η hη hker.le hp')

end NewPair

theorem GNewPair : S_GNewPair := by
  intro L _ _ hL hp hne hK
  have : Group.IsPerfect L := ⟨hL.1⟩
  exfalso
  apply hne
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · exact NewPair.suzuki_center_eq_bot hp hn e
  · exact CFSG.QuasithinUnique.RankOneRecog.unitary_center_eq_bot hp hf e

end CFSG.Goldschmidt
