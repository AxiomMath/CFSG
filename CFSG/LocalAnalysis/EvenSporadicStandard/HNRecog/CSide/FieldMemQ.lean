module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpS5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpInvol
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private noncomputable def fieldmemq_mk {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (a : C) :
    ↥(Subgroup.centralizer ({a} : Set C)) →*
      ↥(Subgroup.centralizer ({(a : C ⧸ Q)} : Set (C ⧸ Q))) :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' Q).comp (Subgroup.centralizer ({a} : Set C)).subtype)
    (Subgroup.centralizer ({(a : C ⧸ Q)} : Set (C ⧸ Q)))
    (fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      show QuotientGroup.mk' Q (x : C) * QuotientGroup.mk' Q a =
        QuotientGroup.mk' Q a * QuotientGroup.mk' Q (x : C)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2])

private theorem fieldmemq_mk_ker {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (a : C) :
    (fieldmemq_mk (Q := Q) a).ker = Q.comap (Subgroup.centralizer ({a} : Set C)).subtype := by
  unfold fieldmemq_mk
  rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

private noncomputable def fieldmemq_psi {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (e : C ⧸ Q ≃* A5WrTwo) (a : C) :
    ↥(Subgroup.centralizer ({a} : Set C)) →*
      ↥(Subgroup.centralizer ({(e (a : C ⧸ Q))} : Set A5WrTwo)) :=
  (TwoHSData.centralizerMulEquiv e (a : C ⧸ Q)).toMonoidHom.comp (fieldmemq_mk a)

private theorem fieldmemq_psi_ker {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (e : C ⧸ Q ≃* A5WrTwo) (a : C) :
    (fieldmemq_psi e a).ker = Q.comap (Subgroup.centralizer ({a} : Set C)).subtype := by
  unfold fieldmemq_psi
  rw [MonoidHom.ker_comp_of_injective _ _
      (TwoHSData.centralizerMulEquiv e (a : C ⧸ Q)).injective,
    fieldmemq_mk_ker]

theorem cSideFacts_mem_Q_of_cent : ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → ∀ a : C, a ^ 2 = 1 →
      IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({a} : Set C)) → a ∈ Q := by
  intro C _ Q _ hE a ha2 ha
  classical
  by_contra hna
  haveI : Finite Q := hE.plus.finite
  haveI : Finite (C ⧸ Q) := by
    obtain ⟨e⟩ := hE.quotient
    exact Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite C :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Q)).symm
  obtain ⟨e⟩ := hE.quotient
  have hQp : IsPGroup 2 Q := hE.plus.isExtraspecialPGroup.isPGroup
  have hā2 : (a : C ⧸ Q) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]
  have hu2 : (e (a : C ⧸ Q)) ^ 2 = 1 := by
    rw [← map_pow, hā2, map_one]
  have hu1 : e (a : C ⧸ Q) ≠ 1 := by
    intro h
    apply hna
    have h1 : (a : C ⧸ Q) = 1 := e.injective (by rw [h, map_one])
    exact (QuotientGroup.eq_one_iff (N := Q) a).mp h1
  have hψp : IsPGroup 2 (fieldmemq_psi e a).ker := by
    rw [fieldmemq_psi_ker e a]
    exact hQp.comap_subtype
  obtain ⟨φ, hφ⟩ := CSide.cSide_cent_invol_hom (u := e (a : C ⧸ Q)) hu2 hu1
  have hcomp : IsPGroup 2 (φ.comp (fieldmemq_psi e a)).ker :=
    CSide.cSide_isPGroup_ker_comp (fieldmemq_psi e a) φ hψp hφ
  obtain ⟨N, hN, hNp, ⟨e'⟩⟩ := CSide.cSide_isShapeTwoTwoSixS5_exists ha
  haveI : N.Normal := hN
  exact CSide.cSide_noS5 N hNp e' (φ.comp (fieldmemq_psi e a)) hcomp

end CFSG.EvenSporadicStandard.HNRecog.Section3
