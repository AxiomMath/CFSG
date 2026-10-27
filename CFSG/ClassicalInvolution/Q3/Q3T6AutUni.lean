module

public import CFSG.ClassicalInvolution.Uniform.UBranch
public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

variable {G : Type} [Group G] {K : Subgroup G} {z : G}

theorem nonempty_equiv_of_memberU (h : IsClassicalMemberU (.sl2 3 1) K z) :
    Nonempty (K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) :=
  h.nonempty_equiv_sl2Three (by norm_num [MemberType.IsSolvableType])

theorem nonempty_equiv_satU [Finite G] (h : IsClassicalMemberU (.sl2 3 1) K z) :
    Nonempty (satU (.sl2 3 1) K z ⧸ classicalInvolutionOddCore (satU (.sl2 3 1) K z) ≃*
      SL(2, ZMod 3)) :=
  nonempty_equiv_of_memberU h.satU_member

theorem normalizerQuotientTwoGeneratedStar_of_memberU
    (h : IsClassicalMemberU (.sl2 3 1) K z) : NormalizerQuotientTwoGeneratedStar K :=
  normalizerQuotientTwoGeneratedStar_three (nonempty_equiv_of_memberU h).some

theorem normalizerQuotientTwoGeneratedStar_satU [Finite G]
    (h : IsClassicalMemberU (.sl2 3 1) K z) :
    NormalizerQuotientTwoGeneratedStar (satU (.sl2 3 1) K z) :=
  normalizerQuotientTwoGeneratedStar_of_memberU h.satU_member

theorem centSylow_three_of_memberU [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ∀ K ∈ Ω, ∃ z : G, IsClassicalMemberU (.sl2 3 1) K z) :
    Asc77.AscL62.CentSylow Ω :=
  centSylow_three fun K hK => (hΩ K hK).elim fun _ hz => nonempty_equiv_of_memberU hz

theorem centSylow_three_conjClass_satU [Finite G] (h : IsClassicalMemberU (.sl2 3 1) K z) :
    Asc77.AscL62.CentSylow (Generic.CoreAssembly.conjClass (satU (.sl2 3 1) K z)) := by
  refine centSylow_three_of_memberU fun J hJ => ?_
  obtain ⟨g, rfl⟩ := hJ
  exact ⟨g * z * g⁻¹, h.satU_member.conj g⟩

section Branch


theorem normalizerQuotientTwoGeneratedStar_of_dBranchU [Finite G] (D : DBranchU 3 1 K z) :
    NormalizerQuotientTwoGeneratedStar K :=
  normalizerQuotientTwoGeneratedStar_of_memberU D.member

theorem normalizerQuotientTwoGeneratedStar_satU_of_dBranchU [Finite G] (D : DBranchU 3 1 K z) :
    NormalizerQuotientTwoGeneratedStar (satU (.sl2 3 1) K z) :=
  normalizerQuotientTwoGeneratedStar_satU D.member

theorem centSylow_three_of_dBranchU [Finite G] (D : DBranchU 3 1 K z) :
    Asc77.AscL62.CentSylow (Generic.CoreAssembly.conjClass (satU (.sl2 3 1) K z)) :=
  centSylow_three_conjClass_satU D.member

end Branch

end CFSG.ClassicalInvolution.Q3.Q3T6
