module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem hyp_of_modU [Finite G] (h : HypOmegaModU (.sl2 3 1) Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h

theorem exists_chart3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ φ : ↥K →* SL(2, ZMod 3), Function.Surjective φ ∧
      ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2Three (by norm_num [MemberType.IsSolvableType])
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_orderOf_eq_four_of_mem_RSet [Finite G] (hΩ : HypOmegaGen Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 := by
  obtain ⟨k, -, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  refine ⟨((e.symm (QuaternionGroup.xa 0) : ↥R) : G), (e.symm _).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]

theorem natCard_isSylow2In_member [Finite G] (hΩ : HypOmegaModU (.sl2 3 1) Ω) {K P : Subgroup G}
    (hK : K ∈ Ω) (hP : IsSylow2In P K) : Nat.card P = 8 := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2Three (by norm_num [MemberType.IsSolvableType])
  rw [natCard_isSylow2In_eq hP, Nat.card_congr e.toEquiv, natCard_sl2Three]
  have h3 : (Nat.factorization 24) 2 = 3 := by decide +kernel
  rw [h3]
  norm_num

end CFSG.ClassicalInvolution.Q3.Q3T7P25
