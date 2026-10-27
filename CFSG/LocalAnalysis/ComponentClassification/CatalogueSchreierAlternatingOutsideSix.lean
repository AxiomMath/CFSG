module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating

open Equiv
open OuterAutomorphisms

@[expose] noncomputable def permutationOuterHom (n : ℕ) :
    Perm (Fin n) →* Outer (alternatingGroup (Fin n)) :=
  (QuotientGroup.mk' (inner (alternatingGroup (Fin n)))).comp
    (MulAut.conjNormal (H := alternatingGroup (Fin n)))

theorem conjugation_surjective {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Function.Surjective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) := by
  intro automorphism
  obtain ⟨permutation, hpermutation⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le hn
      automorphism
  refine ⟨permutation, ?_⟩
  apply MulEquiv.ext
  intro element
  apply Subtype.ext
  exact (MulAut.conjNormal_apply permutation element).trans (hpermutation element).symm

theorem permutationOuterHom_surjective {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Function.Surjective (permutationOuterHom n) :=
  (QuotientGroup.mk'_surjective (inner (alternatingGroup (Fin n)))).comp
    (conjugation_surjective hn)

theorem alternatingGroup_le_permutationOuterHom_ker (n : ℕ) :
    alternatingGroup (Fin n) ≤ (permutationOuterHom n).ker := by
  intro permutation hpermutation
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨⟨permutation, hpermutation⟩, ?_⟩
  apply MulEquiv.ext
  intro element
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conj_apply]
  rfl

@[expose] noncomputable def signQuotientOuterHom (n : ℕ) :
    Perm (Fin n) ⧸ alternatingGroup (Fin n) →* Outer (alternatingGroup (Fin n)) :=
  QuotientGroup.lift (alternatingGroup (Fin n)) (permutationOuterHom n)
    (alternatingGroup_le_permutationOuterHom_ker n)

theorem signQuotientOuterHom_surjective {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Function.Surjective (signQuotientOuterHom n) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (permutationOuterHom_surjective hn) _

@[expose] noncomputable def signQuotientEquivalence {n : ℕ} (hn : 2 ≤ n) :
    Perm (Fin n) ⧸ alternatingGroup (Fin n) ≃* ℤˣ := by
  letI : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
  exact QuotientGroup.liftEquiv _ (Perm.sign_surjective (Fin n))
    (alternatingGroup_eq_sign_ker)

theorem sign_quotient_card {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Perm (Fin n) ⧸ alternatingGroup (Fin n)) = 2 := by
  rw [Nat.card_congr (signQuotientEquivalence hn).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

theorem outer_card_dvd_two_outside_six {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Nat.card (Outer (alternatingGroup (Fin n))) ∣ 2 := by
  have hcard := Subgroup.card_dvd_of_surjective (f := signQuotientOuterHom n)
    (signQuotientOuterHom_surjective hn)
  rwa [sign_quotient_card (by omega)] at hcard

theorem outer_solvable_outside_six {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    Group.IsSolvable (Outer (alternatingGroup (Fin n))) := by
  let : Group.IsSolvable (Perm (Fin n) ⧸ alternatingGroup (Fin n)) :=
    Group.isSolvable_of_surjective
      (f := (signQuotientEquivalence (by omega : 2 ≤ n)).symm.toMonoidHom)
      (signQuotientEquivalence (by omega : 2 ≤ n)).symm.surjective
  exact Group.isSolvable_of_surjective (signQuotientOuterHom_surjective hn)

theorem outer_solvable_of_equiv_outside_six {G : Type*} [Group G] {n : ℕ}
    (hn : n = 5 ∨ 7 ≤ n) (equivalence : G ≃* alternatingGroup (Fin n)) :
    Group.IsSolvable (Outer G) := by
  let := outer_solvable_outside_six hn
  exact OuterAutomorphisms.solvable_of_equiv equivalence.symm

theorem outer_solvable_of_nonempty_equiv_outside_six {G : Type*} [Group G] {n : ℕ}
    (hn : n = 5 ∨ 7 ≤ n) (hequivalence : Nonempty (G ≃* alternatingGroup (Fin n))) :
    Group.IsSolvable (Outer G) := by
  obtain ⟨equivalence⟩ := hequivalence
  exact outer_solvable_of_equiv_outside_six hn equivalence

theorem outer_card_dvd_two_of_equiv_outside_six {G : Type*} [Group G] {n : ℕ}
    (hn : n = 5 ∨ 7 ≤ n) (equivalence : G ≃* alternatingGroup (Fin n)) :
    Nat.card (Outer G) ∣ 2 := by
  rw [Nat.card_congr (OuterAutomorphisms.equivalence equivalence).toEquiv]
  exact outer_card_dvd_two_outside_six hn

end CFSG.ComponentClassification.CatalogueSchreierAlternating
