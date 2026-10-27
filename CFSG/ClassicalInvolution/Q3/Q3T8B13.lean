module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Nbr

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_centralizes (hΩ : HypOmegaMod Ω) {K M R : Subgroup G} {u : G}
    (hK : K ∈ Ω) (hM : M ∈ Ω) (hMK : M ≠ K) (hu : IsUniqueInvolution M u) (hR : R ∈ RSet Ω)
    (hRK : R ≤ K) (hc : ∀ r ∈ R, r * u = u * r) : M ∈ omegaNbr Ω K := by
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hR
  have hRsyl : IsSylow2In R K :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK
  have hRc : R ≤ Subgroup.centralizer ({u} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc r hr)
  have hRN : R ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hM hK hMK hu hRK hRsyl.2.1 (by omega) hRc
  exact Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hM hK
    ⟨hK, hMK.symm, R, hR, hRK, hRN⟩

end Nbr

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
