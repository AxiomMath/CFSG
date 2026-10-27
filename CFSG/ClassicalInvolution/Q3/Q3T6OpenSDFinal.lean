module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainStd
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDType2
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups

section Bridge

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem TightStd3.isQuatSub_of_mem_rSet (ht : TightStd3 K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) : IsQuatSub R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨r, hr, ⟨e⟩⟩ := quaternion_sylow_of_isClassicalMember3'
    ((ht.member.conj g).toQ3 (by norm_num)) P
  exact ⟨r - 2, by omega,
    ⟨(Subgroup.equivMapOfInjective _ _ (conjSub g K).subtype_injective).symm.trans e⟩⟩

theorem TightStd3.setup194Three (ht : TightStd3 K z) : SD.Setup194Three K z where
  uniqueInvolutionNormal := ht.uniqueInvolutionNormal
  nonabelian := ht.nonabelian
  normEq := ht.normEq
  quat := fun hR => ht.isQuatSub_of_mem_rSet hR
  sylow_eq := fun Q _ hS hQS _ hgS => ht.conjSubgroup_sylow_eq Q hS hQS hgS

theorem c19_4Three_of_b3 (hB3 : GoldschmidtB3Tmp) (hS3 : MuS3OfShape3) : C19_4Three := by
  intro G _ _ _ Ω K S R z hstd W hW _ hZ
  have hs := hstd.stand
  have hP : Q3CL.PartIHypG Ω := Q3CL.partIHypG_of_modU hs.hyp hs.aEmpty
  have hst := SD.omegaStarNbr_eq_empty_of_muIsoZ2 hS3 hP hW hstd.edgeless hZ
  have ht := hstd.tight.setup194Three
  obtain rfl := hstd.eq_conjClass
  have hA := SD.allTypeTwo_of_omegaStarNbr_eq_empty hP.hyp hstd.edgeless hst hstd.hz
  exact Or.inr (SD.twoSubgroupsFourGenerated_of_allTypeTwo hB3 ht hA)

end Bridge

end CFSG.ClassicalInvolution.Q3.Q3T6
