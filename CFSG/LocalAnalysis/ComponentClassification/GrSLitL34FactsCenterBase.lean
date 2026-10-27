
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Inputs47
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.PSL3Four.Native

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_T0
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S) (hs2 : s * s = 1) :
    ∃ g ∈ S, g⁻¹ * s * g ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s' : S := ⟨s, hs⟩
  have hs'2 : s' * s' = 1 := Subtype.ext hs2
  have hp : IsPGroup 2 (zpowers s') := by
    rintro ⟨h, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hs'2, one_zpow]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0 Q
  have hmem : s' ∈ (Q : Subgroup S) := hQ (mem_zpowers s')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hy, hys⟩ := hmem
  refine ⟨g, g.2, ?_⟩
  rw [coe_sylowT0] at hy
  have hy' : (y : Equiv.Perm (Fin 42)) ∈ T0 := Subgroup.mem_subgroupOf.mp hy
  have hval : (g : Equiv.Perm (Fin 42)) * y * (g : Equiv.Perm (Fin 42))⁻¹ = s := by
    have := congrArg Subtype.val hys
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have e : (y : Equiv.Perm (Fin 42)) = (g : Equiv.Perm (Fin 42))⁻¹ * s * g := by
    rw [← hval]
    group
  rwa [← e]

end CFSG.ComponentClassification.GrSLit.L34Facts
