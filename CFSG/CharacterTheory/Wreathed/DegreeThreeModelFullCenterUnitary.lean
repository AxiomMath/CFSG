module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterUnitaryPlane
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterLinear

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix CFSG.ComponentClassification
open CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
open OddUnitaryThreeCentralizerCore OddLinearThreeCentralizerCore
open CFSG.Semidihedral.OddLinearNormals
open CFSG.Assembly.LowTwoRank

universe u v

section OriginalUnitaryThree

variable {E : Type u} [Field E] [Finite E] {V : Type v} [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V] {sigma : E ≃+* E}
variable (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

@[expose] def unitaryMatrixTargetHom (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t)
    (B : (Fin 2 → E) ≃ₗ[E] minusSpace z.val.val.toLinearMap) :
    (unitaryPlaneMatrixHom (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) B).range →*
        Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)) :=
  (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt).comp
    (unitaryPlaneMatrixEquiv (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) B).symm.toMonoidHom

theorem unitaryMatrixTargetHom_coe (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t)
    (B : (Fin 2 → E) ≃ₗ[E] minusSpace z.val.val.toLinearMap)
    (a : (unitaryPlaneMatrixHom (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) B).range) :
    (unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B a :
      specialIsometry h ⧸ D) = QuotientGroup.mk' D
        (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz
          ((unitaryPlaneMatrixEquiv (h.domRestrict₁₂
            (minusSpace z.val.val.toLinearMap)
            (minusSpace z.val.val.toLinearMap)) B).symm a)).val :=
  unitaryTargetQuotientCentralizer_coe h h2 hsym hnd hsigma hne hdim D z hz t hzt _

theorem unitaryMatrixTargetHom_surjective (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2)
    (t : specialIsometry h ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (B : (Fin 2 → E) ≃ₗ[E] minusSpace z.val.val.toLinearMap) :
    Function.Surjective (unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B) :=
  (unitaryTargetQuotientCentralizer_surjective
    h h2 hsym hnd hsigma hne hdim D hD z hz t hzt).comp
      (unitaryPlaneMatrixEquiv (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) B).symm.surjective

theorem unitaryMatrixTargetHom_ker_le_odd_scalars (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2)
    (t : specialIsometry h ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (B : (Fin 2 → E) ≃ₗ[E] minusSpace z.val.val.toLinearMap) :
    (unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B).ker ≤
      oddScalarSubgroup (unitaryPlaneMatrixHom (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) B).range := by
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  let psi := unitaryPlaneMatrixEquiv hP B
  let phi := unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  let : Finite (isometryGroup h) := isometryGroup_finite h
  have ho : Odd (Nat.card phi.ker) := by
    dsimp only [phi]
    rw [unitaryMatrixTargetHom, ← MonoidHom.comap_ker]
    have hk : Odd (Nat.card
        (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt).ker) := by
      rw [unitaryTargetQuotientCentralizer_ker,
        unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz]
      exact scalar_kernel_odd h hdim D hD
    exact hk.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ psi.symm.toMonoidHom
      psi.symm.injective)
  have hs : phi.ker ≤ (unitaryMatrixScalarHom hP B).range := by
    intro a ha
    have hk : psi.symm a ∈
        (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt).ker := ha
    rw [unitaryTargetQuotientCentralizer_ker] at hk
    obtain ⟨c, hc⟩ := unitaryQuotientKernel_le_scalars h h2 hsym hnd hsigma hne hdim D hD z hz hk
    refine ⟨c, psi.symm.injective ?_⟩
    exact (unitaryPlaneMatrixEquiv_symm_scalar hP B c).trans hc
  rw [oddScalarSubgroup_eq_map _ _ (unitaryMatrixScalarHom_injective hP B)
    (unitaryMatrixScalarHom_range hP hPnd B)]
  exact CyclicOddScalarQuotient.ker_le_oddScalarImage (unitaryMatrixScalarHom hP B)
    (unitaryMatrixScalarHom_injective hP B) phi ho hs

end OriginalUnitaryThree

section OriginalUnitaryCore

variable {E : Type u} [Field E] [Finite E] {V : Type v} [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V]

theorem unitaryMatrixTargetHom_oddCore (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t)
    (B : (Fin 2 → E) ≃ₗ[E] minusSpace z.val.val.toLinearMap) :
    let h2 := unitaryField_two_ne_zero p f hpodd hE
    let hsigma := (unitaryFieldConjugation_data p f hE).1
    let hne := (unitaryFieldConjugation_data p f hE).2.1
    let P := minusSpace z.val.val.toLinearMap
    let hP := h.domRestrict₁₂ P P
    CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) =
      (oddScalarSubgroup (unitaryPlaneMatrixHom hP B).range).map
        (unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B) := by
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (unitaryFieldConjugation_data p f hE).1
  let hne := (unitaryFieldConjugation_data p f hE).2.1
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  dsimp only
  rw [oddScalarSubgroup_eq_map _ _ (unitaryMatrixScalarHom_injective hP B)
    (unitaryMatrixScalarHom_range hP hPnd B), Subgroup.map_map]
  have he :
      (unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B).comp
        (unitaryMatrixScalarHom hP B) =
      (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt).comp
        (scalarIsometry hP) := by
    rw [unitaryMatrixTargetHom, MonoidHom.comp_assoc, unitaryPlaneMatrixEquiv_symm_comp_scalars]
  rw [he, ← Subgroup.map_map]
  exact (unitaryTargetQuotientCentralizer_core_structure p f hpodd hE h hsym hnd hdim
    D hD z hz t hzt).1

end OriginalUnitaryCore

theorem unitary_three_target_full_center_quotient_conclusions
    {E V : Type} [Field E] [Finite E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hf : 1 ≤ f) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (t : specialIsometry h ⧸ D) (ht : orderOf t = 2) :
    localQuotientConclusions p f
      (reducedFullCenter (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) := by
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let sigma := unitaryFieldConjugation p f hE
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (unitaryFieldConjugation_data p f hE).1
  let hne := (unitaryFieldConjugation_data p f hE).2.1
  obtain ⟨z, ⟨hz, hzt⟩, _⟩ := unique_involution_lift h hdim D hD t ht
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  have hPdim : Module.finrank E P = 2 := (involution_finrank h h2 hdim z hz).1
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  obtain ⟨hFcard, B, d, eSU, _, _, _, _, hinverse⟩ :=
    unitary_field_two_special_linear_isomorphism p f hE hP (hsym.domRestrict P) hPnd hPdim
  let F := CatalogueBLinearTwoDescent.fixedSubfield E sigma
  let U := (unitaryPlaneMatrixHom hP B).range
  have hSU : conjugatedImageSL F.subtype (diagonalGL d) ≤ U :=
    unitaryPlaneMatrixHom_contains_special hP B d eSU hinverse
  let phi := unitaryMatrixTargetHom h h2 hsym hnd hsigma hne hdim D z hz t hzt B
  have hphi := unitaryMatrixTargetHom_surjective h h2 hsym hnd hsigma hne hdim D hD z hz t hzt B
  have hk := unitaryMatrixTargetHom_ker_le_odd_scalars
    h h2 hsym hnd hsigma hne hdim D hD z hz t hzt B
  have hc := unitaryMatrixTargetHom_oddCore p f hpodd hE h hsym hnd hdim D hD z hz t hzt B
  have hU := card_unitaryPlaneMatrixGroup p f hE hP (hsym.domRestrict P) hPnd hPdim B
  constructor
  · intro hthree
    have hF3 : Nat.card F = 3 := hFcard.trans hthree
    let e := reducedTargetFullCenterEquivOfTwoPower F.subtype (diagonalGL d) U hSU 2
      (by rw [card_unitaryMatrixScalars p f hE hP hPnd B, hthree]; rfl) phi hphi hk hc
    obtain ⟨hsolv, horder⟩ := matrix_overgroup_scalar_quotient_three hF3
      F.subtype (diagonalGL d) U hSU hU
    let : Group.IsSolvable (U ⧸ scalarSubgroup U) := hsolv
    exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective,
      (Nat.card_congr e.symm.toEquiv).trans horder⟩
  · intro hlarge
    have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; omega
    let e := reducedTargetFullCenterEquiv hF4 F.subtype (diagonalGL d) U hSU phi hphi hk hc
    have hm := matrix_overgroup_generalizedFitting_full_conclusions p f (Fact.out : p.Prime)
      hpodd hf hlarge hFcard F.subtype (diagonalGL d) U hSU hU
    exact full_large_conclusions_of_equiv e p f (Fact.out : p.Prime) hpodd hf hlarge
      ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1⟩

end CFSG.Wreathed.DegreeThreeModelFullCenter
