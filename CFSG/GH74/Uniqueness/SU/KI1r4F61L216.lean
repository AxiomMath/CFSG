module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSL2
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Mod
import CFSG.Walter.PSL2Facts.Even
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
public import Certificates.Certificate5137
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Uniqueness.SU.KI1r3FamBender
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L216M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74.KGroups Matrix

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 4080 :=
  Certificates.certificate5137.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 16320 :=
  Certificates.certificate5137.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 3 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5137.2.2.1

theorem count_ok_check : pairCountB QP 2 3 ws = 16320 :=
  Certificates.certificate5137.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 3 ws = QA.orderCertificate := by
  rw [QA_valid.2]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5137.2.2.2.1

theorem cent_ok :
    centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5137.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl
  norm_num

@[expose] def enum : Fin 16 → GF16 := fun k => GF16.ofNat' k.val

theorem enum_bij : Function.Bijective enum := by decide +kernel

@[expose] def mA : Matrix.SpecialLinearGroup (Fin 2) GF16 :=
  ⟨!![GF16.ofNat' 0, GF16.ofNat' 1; GF16.ofNat' 1, GF16.ofNat' 0], by
    rw [Matrix.det_fin_two_of]; decide +kernel⟩

@[expose] def mB : Matrix.SpecialLinearGroup (Fin 2) GF16 :=
  ⟨!![GF16.ofNat' 0, GF16.ofNat' 2; GF16.ofNat' 9, GF16.ofNat' 1], by
    rw [Matrix.det_fin_two_of]; decide +kernel⟩

theorem actA : ∀ i : Fin 17, ∃ c : GF16, c • ((mA : Matrix (Fin 2) (Fin 2) GF16) *ᵥ
    PSL2.vecP enum i) = PSL2.vecP enum (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 17, ∃ c : GF16, c • ((mB : Matrix (Fin 2) (Fin 2) GF16) *ᵥ
    PSL2.vecP enum i) = PSL2.vecP enum (pb i) := by
  decide +kernel

theorem card_GF16 : Nat.card GF16 = 2 ^ 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_psl_GF16 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF16) = 4080 := by
  have e := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField GF16 2 4 (by norm_num) card_GF16) (Fin 2)
  rw [Nat.card_congr e.toEquiv]
  have h := CFSG.Walter.psl2_even_card (f := 4) (by norm_num)
  norm_num at h
  exact h

theorem equiv_psl_P :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF16 ≃* QP.originalSubgroup) := by
  refine PSL2.psl2_equiv_closure (PSL2.ptEquiv enum enum_bij) mA mB pa pb
    (PSL2.pointwise_of_exists enum enum_bij mA pa actA)
    (PSL2.pointwise_of_exists enum enum_bij mB pb actB) QP.originalSubgroup QP_closure ?_
  rw [card_group QP QP_ok, QP_valid.2, card_psl_GF16]

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSL 2 2 4) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  obtain ⟨e1⟩ := PSL2.psl2_equiv_of_lieModel (F := GF16) 2 4 (by norm_num) card_GF16 h
  obtain ⟨e2⟩ := equiv_psl_P
  exact ⟨e1.trans e2⟩

theorem autModel {K : Type} [Group K] (h : LieModel K .PSL 2 2 4) :
    ∃ M : AutModel K (Equiv.Perm (Fin 17)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 3 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

theorem e4_check : ((elemsT QA).all fun g => !decide (g * g = 1) ||
    invP.any fun u => decide (g * u = u * g) &&
      invP.any fun v => decide (v ≠ u) && decide (g * v = v * g) && decide (u * v = v * u)) =
    true :=
  Certificates.certificate5137.2.2.2.2.2.1

theorem mem_invP {u : Equiv.Perm (Fin 17)} (hu : u ∈ invP) :
    u ∈ QP.originalSubgroup ∧ u ≠ 1 ∧ u * u = 1 := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨(mem_elemsT QP QP_ok u).1 h1, h2.1, h2.2⟩

theorem modE4 :
    ∀ g ∈ QA.originalSubgroup, g ^ 2 = 1 → ModE4 QP.originalSubgroup g := by
  intro g hg hg2
  have hg2' : g * g = 1 := by rw [← pow_two]; exact hg2
  have h1 := forall_of_all QA QA_ok e4_check g hg
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
  rcases h1 with h | h
  · exact absurd hg2' h
  · obtain ⟨u, hu, h2⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨hgu, h3⟩ := h2
    obtain ⟨v, hv, h4⟩ := List.any_eq_true.1 h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
    obtain ⟨⟨hvu, hgv⟩, huv⟩ := h4
    obtain ⟨hu1, hu2, hu3⟩ := mem_invP hu
    obtain ⟨hv1, hv2, hv3⟩ := mem_invP hv
    exact ⟨u, v, hu1, hv1, hu2, hv2, hvu.symm, by rw [pow_two]; exact hu3,
      by rw [pow_two]; exact hv3, huv, hgu, hgv⟩

end CFSG.GH74.Uniqueness.SU.K.R4.L216M

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG.Blueprint

theorem strictL216
    {K : Type} [Group K] [Finite K] (h : LieModel K .PSL 2 2 4) : StrictFix K := by
  obtain ⟨M, hMP, hMA⟩ := L216M.autModel h
  refine strictFix_of_model M fun g hg hg2 => ?_
  rw [hMA] at hg
  rw [hMP]
  exact L216M.modE4 g hg hg2

end CFSG.GH74.Uniqueness.SU.K.R4
