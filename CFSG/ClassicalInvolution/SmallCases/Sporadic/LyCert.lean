module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCheck
public import Certificates.Certificate9310
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCheck
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec

public section

namespace CFSG.ClassicalInvolution

namespace LyProof

open CFSG.Sporadic.Ly

theorem ly_involution_centralizer_facts :
    ∃ _ : LySeed, ∃ z : J, ∃ K S : Subgroup J, z * z = 1 ∧ z ≠ 1 ∧
      Subgroup.centralizer ({z} : Set J) = K ∧ CFSG.Open.IsQuasisimple K ∧
      Nat.card (Subgroup.center K) = 2 ∧ Nat.card K = 39916800 ∧
      IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ Nat.card S = 256 ∧
      (∀ s ∈ S, s * s = 1 → s ≠ 1 → ∃ C : J, s = C * z * C⁻¹) ∧
      ∃ u ∈ K, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z :=
  Certificates.certificate9310

end LyProof

end CFSG.ClassicalInvolution
