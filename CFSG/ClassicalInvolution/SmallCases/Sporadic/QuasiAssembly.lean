module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Assembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAmbient

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Schreier (centralizerIn)

variable {M : Type*} [Group M]

theorem noNonsolvableClassical_of_single_class_quasisimple (H S K : Subgroup M) [Finite H]
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {z : M} (hz : z ∈ H)
    (hSz : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * z * c⁻¹)
    (hK : centralizerIn H z = K) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.card (Subgroup.center ↥K) = 2)
    (hcard : Nat.card K = 40320 ∨ Nat.card K = 39916800) : NoNonsolvableClassical H :=
  noNonsolvableClassical_of_sylow_cover_at H S hS hidx hz hSz
    (NoNonsolvableClassicalAt.of_ambient_quasisimple H ⟨z, hz⟩ K hK hq hZ hcard)

end CFSG.ClassicalInvolution
