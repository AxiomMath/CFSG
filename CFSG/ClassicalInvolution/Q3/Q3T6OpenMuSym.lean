module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Mu

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_omegaStarNbr (hΩ : HypOmegaGen Ω) (K : Subgroup G) :
    omegaNbr Ω K ⊆ omegaStarNbr Ω K := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  obtain ⟨U, hUR, hUc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  exact ⟨hJ, hJK, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRJ, hUR.trans hRN⟩

theorem exists_wreathed_of_omegaStar (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hstar : J ∈ omegaStarNbr Ω K) (hnot : J ∉ omegaNbr Ω K) :
    ∃ V R : Subgroup G, V ≤ J ∧ j ∈ V ∧ V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
      R ∈ RSet Ω ∧ R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧ IsWreathed (R ⊔ V) ∧
        j ≠ z := by
  have hne : J ≠ K := hstar.2.1
  obtain ⟨-, -, U₀, hU₀, hU₀J, hU₀N⟩ := hstar
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU₀
  have hU₀2 : IsPGroup 2 U₀ := Sec6Gen.isPGroup_of_mem_USet hΩ hU₀
  have hjU₀ : j ∈ U₀ := Asc77.T3.mem_of_isPGroup hj hU₀J hU₀2 (by omega)
  have hU₀c : U₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    Asc77.T3.le_centralizer_of_le_normalizer' hz hU₀N
  have hnt : J ∉ twinSet Ω K := fun ht =>
    hnot (by
      obtain ⟨-, z', hz'K, hz'J⟩ := ht
      exact Q3CL.T3.twin_mem_omegaNbr hΩ hK hJ hne hz'K hz'J)
  have hjz : j ≠ z := by
    intro he
    exact hnt ⟨hJ, z, hz, he ▸ hj⟩
  obtain ⟨V, hV, hU₀V⟩ := IsSylow2In.exists_ge hU₀2 (le_inf hU₀J hU₀c)
  have hjV : j ∈ V := hU₀V hjU₀
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ hnt j hj V hV hjV with
    ⟨-, hne1⟩ | ⟨hV1, -⟩ | ⟨hVU, hVN, R, hR, hRK, hVR, hwr⟩ | ⟨hVR, hcomm⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hU₀N hjU₀)) hne1
  · exfalso
    have h1 : Nat.card V = 2 := by
      rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one]
    have h2 := Subgroup.card_le_of_le hU₀V
    omega
  · exact ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩
  · exfalso
    have hVN : V ≤ Subgroup.normalizer (K : Set G) :=
      Asc77.T3.le_normalizer_of_commutator_le' (hcomm.trans (oddCoreOf_le_self K))
    exact hnot ⟨hJ, hne, V, hVR, hVJ, hVN⟩

theorem omegaStarNbr_symm (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J ∈ omegaStarNbr Ω K) : K ∈ omegaStarNbr Ω J := by
  by_cases hnbr : J ∈ omegaNbr Ω K
  · exact omegaNbr_subset_omegaStarNbr hΩ J
      (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJ hnbr)
  · obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
    obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
    obtain ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩ :=
      exists_wreathed_of_omegaStar hΩ hK hJ hzK hzJ h hnbr
    have hRs : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
    have hzR : zK ∈ R := Asc77.T3.mem_of_isPGroup hzK hRK hRs.2.1 (by omega)
    have hzR' : IsUniqueInvolution R zK :=
      ⟨hzR, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y (hRK hy) hy2⟩
    have hquat : IsQuatSub R := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
    obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
    obtain ⟨w, hwV, hww⟩ := Asc77.T3.exists_sq_eq_of_cyclic hzJ hVJ hVc
      (Sec6Gen.isPGroup_of_mem_USet hΩ hVU) h4V
    obtain ⟨U, hUR, hUc, hrel, hUz⟩ := Asc77.T3.exists_cyclic_index_two_le_centralizer hquat
      hzR' hwr (Subgroup.mem_sup_right hwV) hww
    have hcard : Nat.card U * U.relIndex R = Nat.card R := by
      have := Subgroup.relIndex_mul_card U R
      rwa [inf_eq_left.mpr hUR, mul_comm] at this
    rw [hrel] at hcard
    have hU2 : IsPGroup 2 U := hRs.2.1.to_le hUR
    have hUN : U ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hK h.2.1 hzJ (hUR.trans hRs.1) hU2
        (by omega) hUz
    exact ⟨hK, Ne.symm h.2.1, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRs.1, hUN⟩

end CFSG.ClassicalInvolution.Q3.Q3T6.Mu
