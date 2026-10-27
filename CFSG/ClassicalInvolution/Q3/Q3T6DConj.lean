module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuSym

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.ClassicalInvolution.Disconnected.AschTight

section Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_normalizer_of_mem_omegaStarNbr (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    j ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU2 := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  exact hUN (mem_of_isPGroup hj hUJ hU2 (by omega))

theorem commute_of_mem_omegaStarNbr (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) : z * j = j * z := by
  have h1 := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp
    (mem_normalizer_of_mem_omegaStarNbr hΩ hJ hj))
  have := h1
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem exists_mem_conj_eq_mul (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hstar : J ∈ omegaStarNbr Ω K) (hnot : J ∉ omegaNbr Ω K) :
    ∃ r ∈ K, r * z * r⁻¹ = z ∧ r * j * r⁻¹ = z * j := by
  obtain ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩ :=
    Q3T6.Mu.exists_wreathed_of_omegaStar hΩ hK hJ hz hj hstar hnot
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact hRJ'.2.1
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩ hVU
  have hP2 : IsPGroup 2 ↥(R ⊔ V) := by
    have := hV2.to_sup_of_normal_right' hR2 hVR
    rwa [sup_comm] at this
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have hzR : z ∈ R := mem_of_isPGroup hz hRK hR2 (by omega)
  have hzc : ∀ x ∈ R ⊔ V, z * x = x * z := by
    have hle : R ⊔ V ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun r hr => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem (hRK hr)).symm)
        (le_centralizer_of_le_normalizer' hz hVN)
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  obtain ⟨g, hgP, hg⟩ := exists_conj_of_isWreathed hwr hP2 (Subgroup.mem_sup_left hzR) hz.sq
    hz.ne_one hzc (Subgroup.mem_sup_right hjV) hj.sq hj.ne_one hjz
  obtain ⟨r, hrR, v, hvV, rfl⟩ := exists_mul_of_mem_sup hVR hgP
  have hVc : IsCyclic ↥V := by
    obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
    exact hc
  have hvj : v * j = j * v := cyclic_comm hVc hvV hjV
  refine ⟨r, hRK hrR, ?_, ?_⟩
  · have := hz.commute_of_mem (hRK hrR)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · rw [← hg]
    calc r * j * r⁻¹ = r * (v * j * v⁻¹) * r⁻¹ := by rw [hvj]; group
      _ = r * v * j * (r * v)⁻¹ := by group

theorem exists_conj_to_z (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hstar : J ∈ omegaStarNbr Ω K) (hnot : J ∉ omegaNbr Ω K) :
    ∃ a ∈ pairNormalizers K J z j, a * j * a⁻¹ = z := by
  obtain ⟨r, hrK, hrz, hrj⟩ := exists_mem_conj_eq_mul hΩ hK hJ hz hj hstar hnot
  have hstar' : K ∈ omegaStarNbr Ω J := Q3T6.Mu.omegaStarNbr_symm hΩ hK hJ hstar
  have hnot' : K ∉ omegaNbr Ω J := fun h =>
    hnot (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hK h)
  obtain ⟨x, hxJ, hxj, hxz⟩ := exists_mem_conj_eq_mul hΩ hJ hK hj hz hstar' hnot'
  have hcomm : z * j = j * z := commute_of_mem_omegaStarNbr hΩ hstar hz hj
  set Z : Subgroup G := Subgroup.closure ({z, j} : Set G) with hZ
  have hzZ : z ∈ Z := Subgroup.subset_closure (by simp)
  have hjZ : j ∈ Z := Subgroup.subset_closure (by simp)
  have hrN : r ∈ Subgroup.normalizer (Z : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · rw [hrz]
      exact hzZ
    · rw [hrj]
      exact Z.mul_mem hzZ hjZ
  have hxN : x ∈ Subgroup.normalizer (Z : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · rw [hxz]
      exact Z.mul_mem hjZ hzZ
    · rw [hxj]
      exact hjZ
  refine ⟨x * r, Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hxJ, hxN⟩)
    (Subgroup.mem_sup_left ⟨hrK, hrN⟩), ?_⟩
  calc x * r * j * (x * r)⁻¹ = x * (r * j * r⁻¹) * x⁻¹ := by group
    _ = x * (z * j) * x⁻¹ := by rw [hrj]
    _ = (x * z * x⁻¹) * (x * j * x⁻¹) := by group
    _ = (j * z) * j := by rw [hxz, hxj]
    _ = j * (z * j) := by group
    _ = j * (j * z) := by rw [hcomm]
    _ = (j * j) * z := by group
    _ = z := by rw [hj.sq, one_mul]

theorem AViol.exists_twin (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hv : AViol Ω K J zK zJ) :
    ∃ a ∈ pairNormalizers K J zK zJ, a * zJ * a⁻¹ = zK ∧ conjSub a J ∈ Ω ∧
      IsUniqueInvolution (conjSub a J) zK ∧ conjSub a J ≠ K := by
  obtain ⟨a, ha, hac⟩ := exists_conj_to_z hΩ hK hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr
  refine ⟨a, ha, hac, hΩ.conjInvariant a J hv.mem, ?_, ?_⟩
  · have := hv.hzJ.conj a
    rwa [hac] at this
  · intro he
    refine hv.no_conj a⁻¹ (Subgroup.inv_mem _ ha) ?_
    rw [← he, conjSub_inv_conjSub]

theorem AViol.exists_swap (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hall : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M) (hv : AViol Ω K J zK zJ) :
    ∃ a ∈ pairNormalizers K J zK zJ, a * zJ * a⁻¹ = zK ∧ conjSub a J ∈ Ω ∧
      IsUniqueInvolution (conjSub a J) zK ∧ conjSub a J ≠ K ∧
      ∃ g : G, g * zK * g⁻¹ = zK ∧ conjSub g K = conjSub a J := by
  obtain ⟨a, ha, hac, hΩ', hz', hne⟩ := AViol.exists_twin hΩ hK hv
  obtain ⟨g, hg⟩ := hall _ hΩ'
  exact ⟨a, ha, hac, hΩ', hz', hne, g, exists_centralizing_of_twin hv.hzK hz' hg, hg⟩

end Conj

end CFSG.ClassicalInvolution.Q3.Q3T6D
