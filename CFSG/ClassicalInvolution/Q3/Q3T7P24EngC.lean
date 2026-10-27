module

public import CFSG.ClassicalInvolution.Asc77.AscT7K1
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twinSet_eq_of {K K' : Subgroup G} {z : G} (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK'tw : K' ∈ twinSet Ω K) (hperp : KPerp Ω K = {K, K'}) :
    twinSet Ω K = {K, K'} := by
  ext L
  constructor
  · intro hL
    have hLperp : L ∈ KPerp Ω K :=
      mem_kPerp_of_twin hΩ hL.1 hK (isUniqueInvolution_of_mem_twinSet hz hL) hz
    rw [hperp] at hLperp
    exact hLperp
  · rintro (rfl | rfl)
    · exact mem_twinSet_self hK hz
    · exact hK'tw

theorem conj_mem_sup_of {K K' : Subgroup G} {z : G} (hΩ : HypOmegaMod Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK'tw : K' ∈ twinSet Ω K) (hKK' : K' ≠ K)
    (htw2 : twinSet Ω K = {K, K'}) {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) {x : G}
    (hx : x ∈ K ⊔ K') : c * x * c⁻¹ ∈ K ⊔ K' := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'tw
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have htw : ∀ {L : Subgroup G}, L ∈ twinSet Ω K → conjSub c L ∈ ({K, K'} : Set (Subgroup G)) := by
    intro L hL
    have hzL := isUniqueInvolution_of_mem_twinSet hz hL
    have h1 : conjSub c L ∈ twinSet Ω K := by
      refine ⟨hΩ.conjInvariant c L hL.1, z, hz, ?_⟩
      have := hzL.conj c
      rwa [hcz] at this
    rwa [htw2] at h1
  have hKK : conjSub c K ∈ ({K, K'} : Set (Subgroup G)) := htw (mem_twinSet_self hK hz)
  have hK'K : conjSub c K' ∈ ({K, K'} : Set (Subgroup G)) := htw hK'tw
  have hne : conjSub c K ≠ conjSub c K' := fun h => hKK'.symm (by
    have := congrArg (conjSub c⁻¹) h
    simpa [conjSub_inv_conjSub] using this)
  have hsup : conjSub c (K ⊔ K') = K ⊔ K' := by
    rw [T7A.conjSub_sup_eq]
    rcases hKK with h | h <;> rcases hK'K with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · rw [h, h']
    · rw [h, h', sup_comm]
    · exact absurd (h.trans h'.symm) hne
  rw [← hsup]
  exact conj_mem_conjSub hx

end T7K
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
