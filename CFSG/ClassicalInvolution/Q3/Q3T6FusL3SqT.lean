module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Sq
public import CFSG.ClassicalInvolution.Q3.Q3T6FusL3Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section SqT



variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G} {hd : Sec19DataT3 K z S W L t V}
  (hF : FL3Facts hd)

namespace FL3Facts

include hF

theorem exists_conj_eq_of_comm_t3 {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) {g : G}
    (hsx : g * z * g⁻¹ * x = x * (g * z * g⁻¹))
    (hsz : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) (hst : g * z * g⁻¹ * t = t * (g * z * g⁻¹)) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = g * z * g⁻¹ := by
  have hΩ := hF.hypGen
  have hI := hd.tight.isUniqueInvolution
  have hcomm := hF.comm
  have htW : t ∈ W := hd.leW hd.memT
  have hzW := hF.hzW
  by_cases hsz' : g * z * g⁻¹ = z
  · exact ⟨1, Subgroup.one_mem _, by rw [hsz']; group⟩
  by_cases hst' : g * z * g⁻¹ = t
  · rw [hst']
    exact hF.exists_conj_eq_t3 hx
  by_cases hstz : g * z * g⁻¹ = t * z
  · rw [hstz]
    exact hF.exists_conj_eq_mul_z3 hx
  have hJ := hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K)
  have hJs := hI.conj g
  by_cases hw : ∃ w ∈ conjSub g K, orderOf w = 4 ∧ w * z = z * w
  · obtain ⟨w, hwJ, hw4, hwz⟩ := hw
    exact hF.exists_conj_eq_of_comm3 hx hJ hJs hsx hsz' hwJ hw4 hwz
  obtain ⟨e₁⟩ := ((hd.tight.member.conj g).toQ3 (by norm_num)).nonempty_equiv
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    hd.tight.centralizer_le_normalizer_member hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hsz.symm)
  have htN : t ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    hd.tight.centralizer_le_normalizer_member hJ hJs
      (Subgroup.mem_centralizer_singleton_iff.mpr hst.symm)
  have hzt : z * t = t * z := hcomm z hzW t htW
  rcases exists_orderOf_four_of_four_group3 (conjSub g K) e₁ ⟨z, hzN⟩ ⟨t, htN⟩ hI.sq hd.invL.sq
      hzt hw with ⟨w, hwJ, hw4, hwt⟩ | ⟨w, hwJ, hw4, hwzt⟩
  · obtain ⟨h₀, hh₀, he⟩ := hF.exists_conj_eq_t3 hx
    exact hF.exists_conj_eq_of_comm'3 hx hJ hJs hsx hh₀ he hst' hwJ hw4 hwt
  · obtain ⟨h₀, hh₀, he⟩ := hF.exists_conj_eq_mul_z3 hx
    have hwm : w * (t * z) = t * z * w := by
      rw [← hzt]
      exact hwzt
    exact hF.exists_conj_eq_of_comm'3 hx hJ hJs hsx hh₀ he hstz hwJ hw4 hwm

end FL3Facts

end SqT

end CFSG.ClassicalInvolution.Q3.Q3T6
