module

public import CFSG.ClassicalInvolution.Asc77.AscT3Sym

public section

namespace CFSG.ClassicalInvolution.Asc77.T3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_conj_to_z [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z j : G}
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hstar : J ∈ omegaStarNbr Ω K)
    (hnot : J ∉ omegaNbr Ω K) : ∃ a ∈ pairNormalizers K J z j, a * j * a⁻¹ = z := by
  obtain ⟨r, hrK, hrz, hrj⟩ := exists_mem_conj_eq_mul h62 hp hq hΩ hK hJ hz hj hstar hnot
  have hstar' : K ∈ omegaStarNbr Ω J := omegaStarNbr_symm h62 hp hq hΩ hK hJ hstar
  have hnot' : K ∉ omegaNbr Ω J := fun h => hnot (omegaNbr_symm h62 hp hq hΩ hJ hK h)
  obtain ⟨x, hxJ, hxj, hxz⟩ := exists_mem_conj_eq_mul h62 hp hq hΩ hJ hK hj hz hstar' hnot'
  have hcomm : z * j = j * z := commute_of_mem_omegaStarNbr hp hΩ hstar hz hj
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

theorem AViol.exists_twin [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hv : AViol Ω K J zK zJ) :
    ∃ a ∈ pairNormalizers K J zK zJ, a * zJ * a⁻¹ = zK ∧ conjSub a J ∈ Ω ∧
      IsUniqueInvolution (conjSub a J) zK ∧ conjSub a J ≠ K := by
  obtain ⟨a, ha, hac⟩ := exists_conj_to_z h62 hp hq hΩ hK hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr
  refine ⟨a, ha, hac, hΩ.conjInvariant a J hv.mem, ?_, ?_⟩
  · have := hv.hzJ.conj a
    rwa [hac] at this
  · intro he
    refine hv.no_conj a⁻¹ (Subgroup.inv_mem _ ha) ?_
    rw [← he, conjSub_inv_conjSub]

theorem AViol.exists_swap [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} {zK zJ : G} (hK : K ∈ Ω)
    (hall : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M) (hv : AViol Ω K J zK zJ) :
    ∃ a ∈ pairNormalizers K J zK zJ, a * zJ * a⁻¹ = zK ∧ conjSub a J ∈ Ω ∧
      IsUniqueInvolution (conjSub a J) zK ∧ conjSub a J ≠ K ∧
      ∃ g : G, g * zK * g⁻¹ = zK ∧ conjSub g K = conjSub a J := by
  obtain ⟨a, ha, hac, hΩ', hz', hne⟩ := hv.exists_twin h62 hp hq hΩ hK
  obtain ⟨g, hg⟩ := hall _ hΩ'
  exact ⟨a, ha, hac, hΩ', hz', hne, g, exists_centralizing_of_twin hv.hzK hz' hg, hg⟩

end CFSG.ClassicalInvolution.Asc77.T3
