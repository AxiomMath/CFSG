module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthMain
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Spin

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem det_spinAction_eq_one [Group.IsPerfect (spinGroup Q)] (s : spinGroup Q) :
    LinearEquiv.det (spinAction Q s) = 1 := by
  have hker := Abelianization.commutator_subset_ker
    ((LinearEquiv.det : (V ≃ₗ[F] V) →* Fˣ).comp (spinAction Q))
  have hs : s ∈ commutator (spinGroup Q) := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  exact MonoidHom.mem_ker.mp (hker hs)

theorem four_dvd_finrank_minusSp_of_sq_one [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {z : spinGroup Q} (hz : z * z = 1)
    (hdet : LinearEquiv.det (spinAction Q z) = 1) :
    4 ∣ Module.finrank F (minusSp (spinAction Q z)) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set i := spinAction Q z with hi
  have hiO : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q z)
  have hii : i * i = 1 := by rw [hi, ← map_mul, hz, map_one]
  have hW : PolarNondegOn Q (minusSp i) := polarNondegOn_minusSp h2 hQ hiO hii
  have hQ' : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp i)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have heven : Even (Module.finrank F (minusSp i)) := even_finrank_minusSp h2 hii hdet
  obtain ⟨l, hlen, hlorth, hlne, hlspan, -⟩ := exists_orthogonal_list_restrict Q (minusSp i) hQ''
  obtain ⟨c, hc, hzz⟩ := spinLift_sq_and_norm hQnd hiO hii rfl hlorth (hlen ▸ heven) hlspan hlne
  have hz2' : (z : CliffordAlgebra Q) * z = 1 := by
    have := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hz
    simpa using this
  have hsign : ((-1 : F) ^ l.length.choose 2) = 1 := by
    apply algebraMap_injective' Q
    rw [← hzz, hz2', map_one]
  have hchoose : Even (l.length.choose 2) :=
    (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp hsign
  rw [← hlen]
  exact four_dvd_of_even_of_even_choose (hlen ▸ heven) hchoose

end Spin

end CFSG.ClassicalInvolution.Asc77.T7H
