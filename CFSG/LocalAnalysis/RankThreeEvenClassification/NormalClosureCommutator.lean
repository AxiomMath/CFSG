module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ConjugateJoin

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem commutator_le_kernel_of_image_centralizes {G : Type u} {H : Type u}
    [Group G] [Group H] (homomorphism : G →* H) (first second : Subgroup G)
    (hcentral : first.map homomorphism ≤ Subgroup.centralizer (second.map homomorphism : Set H)) :
    ⁅first, second⁆ ≤ homomorphism.ker := by
  apply Subgroup.commutator_le.mpr
  intro left hleft right hright
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact (Subgroup.mem_centralizer_iff.mp
    (hcentral (Subgroup.mem_map_of_mem homomorphism hleft)) (homomorphism right)
      (Subgroup.mem_map_of_mem homomorphism hright)).symm

theorem image_centralizes_of_commutator_le_kernel {G : Type u} {H : Type u}
    [Group G] [Group H] (homomorphism : G →* H) (first second : Subgroup G)
    (hcommutator : ⁅first, second⁆ ≤ homomorphism.ker) :
    first.map homomorphism ≤ Subgroup.centralizer (second.map homomorphism : Set H) := by
  rintro left ⟨leftRepresentative, hleft, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  rintro right ⟨rightRepresentative, hright, rfl⟩
  have heq := MonoidHom.mem_ker.mp
    (hcommutator (Subgroup.commutator_mem_commutator hleft hright))
  rw [map_commutatorElement] at heq
  exact (commutatorElement_eq_one_iff_mul_comm.mp heq).symm

theorem conjugateJoin_commutator_le_normal {G : Type u} [Group G]
    (subgroup normal kernel : Subgroup G) [normal.Normal] [kernel.Normal]
    (hcommutator : ⁅subgroup, normal⁆ ≤ kernel) : ⁅conjugateJoin subgroup, normal⁆ ≤ kernel := by
  let quotient := QuotientGroup.mk' kernel
  have himageNormal : (normal.map quotient).Normal :=
    (inferInstance : normal.Normal).map quotient (QuotientGroup.mk'_surjective kernel)
  have : (normal.map quotient).Normal := himageNormal
  let preimage := (Subgroup.centralizer (normal.map quotient : Set (G ⧸ kernel))).comap quotient
  have : preimage.Normal := inferInstance
  have hkernel : ⁅subgroup, normal⁆ ≤ quotient.ker := by
    rwa [QuotientGroup.ker_mk']
  have hsubgroup : subgroup ≤ preimage :=
    Subgroup.map_le_iff_le_comap.mp (image_centralizes_of_commutator_le_kernel quotient subgroup normal hkernel)
  have hclosure : conjugateJoin subgroup ≤ preimage := conjugateJoin_le_normal subgroup preimage hsubgroup
  have himage := Subgroup.map_le_iff_le_comap.mpr hclosure
  have hresult := commutator_le_kernel_of_image_centralizes quotient (conjugateJoin subgroup) normal himage
  rwa [QuotientGroup.ker_mk'] at hresult

theorem conjugateJoin_centralizes_normal_of_abelian {G : Type u} [Group G]
    (subgroup kernel : Subgroup G) [kernel.Normal]
    (habelian : IsMulCommutative subgroup) (hkernel : kernel ≤ subgroup) :
    conjugateJoin subgroup ≤ Subgroup.centralizer (kernel : Set G) := by
  have : (Subgroup.centralizer (kernel : Set G)).Normal := inferInstance
  apply conjugateJoin_le_normal
  intro member hmember
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  exact congrArg (fun value : subgroup => (value : G))
    (isMulCommutative_iff.mp habelian ⟨element, hkernel helement⟩ ⟨member, hmember⟩)

theorem centralizer_symmetry_le {G : Type u} [Group G]
    (first second : Subgroup G) (hcentral : first ≤ Subgroup.centralizer (second : Set G)) :
    second ≤ Subgroup.centralizer (first : Set G) := by
  intro member hmember
  apply Subgroup.mem_centralizer_iff.mpr
  intro element helement
  exact (Subgroup.mem_centralizer_iff.mp (hcentral helement) member hmember).symm

end CFSG.RankThreeEvenClassification.Helpers
