module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Comp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.NoOther
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.TwoCovers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Transfer

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherComponentAction
open CFSG.ComponentClassification.AschbacherComponentInvolution
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

private theorem orderOf_a_of_centConfig (h : CentConfig X a b E Fus) : orderOf a = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by simpa [pow_two] using h.a_sq) h.a_ne

private theorem rightComponent_ne_of_not_mem_normalizer {L : Subgroup X}
    (hmoved : a ∉ normalizer (L : Set X)) : rightComponent L a ≠ L :=
  fun hh => hmoved ((rightComponent_eq_iff_normalizer L a).mp hh)

private theorem rightComponent_eq_map_conj_inv {G : Type*} [Group G] (L : Subgroup G) (g : G) :
    rightComponent L g = L.map (MulAut.conj g⁻¹).toMonoidHom := by
  unfold rightComponent UniversalOrbitBlock.conjugate
  rfl

private theorem rightComponent_one' {G : Type*} [Group G] (L : Subgroup G) :
    rightComponent L 1 = L := by
  rw [rightComponent_eq_map_conj_inv, inv_one]
  exact UniversalOrbitBlock.conjugate_one L

theorem isSp62Cover_of_diagonal (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hmoved : a ∉ normalizer (L : Set X)) (hdiag : E = diagDerived L a) :
    IsSp62Cover ↥L := by
  have ha : orderOf a = 2 := orderOf_a_of_centConfig h
  have hmovedR : rightComponent L a ≠ L := rightComponent_ne_of_not_mem_normalizer hmoved
  have hcommutes : ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
    rw [← rightComponent_involution L a h.a_sq]
    exact moved_component_commutes L a hL hmovedR
  refine ⟨hL.2.2.1, ?_⟩
  have hdiag' : E = (InvolutionDiagonal.homomorphism L (MulAut.conj a) hcommutes).range := by
    rw [hdiag]
    exact moved_component_derived_centralizer L a hL ha hmovedR hcommutes
  have hmodel : LieModel (↥E ⧸ Subgroup.center ↥E) .PSp 3 2 1 := h.E_two.2.2
  rw [hdiag'] at hmodel
  exact LieModel.of_mulEquiv
    (SwappedQuasisimpleProduct.diagonal_center_quotient_equivalence
      L hL.2.2 (MulAut.conj a) hcommutes).symm hmodel

section Certified


theorem conj_mem_pair_of_diagonal (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hmoved : a ∉ normalizer (L : Set X)) (hdiag : E = diagDerived L a)
    (g : X) :
    L.map (MulAut.conj g).toMonoidHom = L ∨
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj a).toMonoidHom := by
  by_contra hconj
  rw [not_or] at hconj
  obtain ⟨hneL, hneL'⟩ := hconj
  let L'' : Subgroup X := L.map (MulAut.conj g).toMonoidHom
  let L' : Subgroup X := L.map (MulAut.conj a).toMonoidHom
  have hL'' : IsComponentOf L'' ⊤ := (LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hL' : IsComponentOf L' ⊤ := (LocalComponents.equiv_iff (MulAut.conj a) L).mpr hL
  have hcomm : ⁅L, L''⁆ = ⊥ := LocalComponents.commute_of_ne L L'' hL hL'' (Ne.symm hneL)
  have hcomm' : ⁅L', L''⁆ = ⊥ := LocalComponents.commute_of_ne L' L'' hL' hL'' (Ne.symm hneL')
  have hmovedR : rightComponent L a ≠ L := rightComponent_ne_of_not_mem_normalizer hmoved
  have hdiag_le : diagDerived L a ≤ L ⊔ L' := by
    unfold diagDerived
    refine (Subgroup.commutator_le_self _).trans (inf_le_left.trans ?_)
    rw [moved_component_commutator L a hL h.a_sq hmovedR,
      rightComponent_involution L a h.a_sq]
  have hE_le : E ≤ L ⊔ L' := hdiag.le.trans hdiag_le
  have hE_cent : E ≤ Subgroup.centralizer (L'' : Set X) :=
    hE_le.trans (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'))
  have hKE : ⁅E, L''⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hE_cent
  have hF : FixLarge ↥L'' :=
    FixLarge.of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      (fixLarge_of_isSp62Cover (isSp62Cover_of_diagonal h hL hmoved hdiag))
  exact h.no_commuting_component hL'' hKE hF

theorem index_normalizer_of_diagonal (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hmoved : a ∉ normalizer (L : Set X)) (hdiag : E = diagDerived L a) :
    (normalizer (L : Set X)).index = 2 := by
  let N : Subgroup X := normalizer (L : Set X)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨a, fun x => ?_⟩
  by_cases hx : x ∈ N
  · right
    refine ⟨hx, fun hxa => hmoved ?_⟩
    have hxinv : x⁻¹ ∈ N := N.inv_mem hx
    have hmem : x⁻¹ * (x * a) ∈ N := N.mul_mem hxinv hxa
    simpa using hmem
  · left
    refine ⟨?_, hx⟩
    rcases conj_mem_pair_of_diagonal h hL hmoved hdiag x⁻¹ with hpair | hpair
    · exact absurd ((rightComponent_eq_iff_normalizer L x).mp (by
        rw [rightComponent_eq_map_conj_inv]; exact hpair)) hx
    · have hxright : rightComponent L x = rightComponent L a :=
        (rightComponent_eq_map_conj_inv L x).trans
          (hpair.trans (rightComponent_involution L a h.a_sq).symm)
      have hcalc : rightComponent L (x * a) = L := by
        calc rightComponent L (x * a)
            = rightComponent (rightComponent L x) a := (rightComponent_mul L x a).symm
          _ = rightComponent (rightComponent L a) a := by rw [hxright]
          _ = rightComponent L (a * a) := rightComponent_mul L a a
          _ = rightComponent L 1 := by rw [h.a_sq]
          _ = L := rightComponent_one' L
      exact (rightComponent_eq_iff_normalizer L (x * a)).mp hcalc

theorem case_diagonal (h : CentConfig X a b E Fus) {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (hmoved : a ∉ normalizer (L : Set X)) (hdiag : E = diagDerived L a) :
    TransferWitness X a Fus := by
  let N : Subgroup X := normalizer (L : Set X)
  have hNindex : N.index = 2 := index_normalizer_of_diagonal h hL hmoved hdiag
  haveI hNnormal : N.Normal := Subgroup.normal_of_index_eq_two hNindex
  refine transferWitness_of_normal N h.a_sq hmoved ?_ ?_
  · rw [hNindex]
    norm_num
  · intro w hwN hFus
    obtain ⟨hw2, _hw1, hD⟩ := h.fus w hFus
    let L' : Subgroup X := L.map (MulAut.conj a).toMonoidHom
    have hrc' : rightComponent L a = L' := rightComponent_involution L a h.a_sq
    have hwL : w ∈ normalizer (L : Set X) := hwN
    have hwL' : w ∈ normalizer (L' : Set X) := by
      rw [← rightComponent_eq_iff_normalizer]
      have haw : a * w * a⁻¹ ∈ N := hNnormal.conj_mem w hwN a
      have hrc : rightComponent L (a * w * a⁻¹) = L :=
        (rightComponent_eq_iff_normalizer L _).mpr haw
      calc rightComponent L' w
          = rightComponent (rightComponent L a) w := by rw [hrc']
        _ = rightComponent L (a * w) := rightComponent_mul L a w
        _ = rightComponent L ((a * w * a⁻¹) * a) := by
              rw [show (a * w * a⁻¹) * a = a * w from by group]
        _ = rightComponent (rightComponent L (a * w * a⁻¹)) a :=
              (rightComponent_mul L (a * w * a⁻¹) a).symm
        _ = rightComponent L a := by rw [hrc]
        _ = L' := hrc'
    have hmovedR : rightComponent L a ≠ L := rightComponent_ne_of_not_mem_normalizer hmoved
    have hcomm : ⁅L, L'⁆ = ⊥ := by
      rw [← hrc']
      exact moved_component_commutes L a hL hmovedR
    have hLcov : IsSp62Cover ↥L := isSp62Cover_of_diagonal h hL hmoved hdiag
    have hL'cov : IsSp62Cover ↥L' :=
      IsSp62Cover.of_mulEquiv
        (Subgroup.equivMapOfInjective L (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
        hLcov
    exact false_of_two_covers hcomm hLcov hL'cov hw2 hwL hwL' hD

end Certified

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
