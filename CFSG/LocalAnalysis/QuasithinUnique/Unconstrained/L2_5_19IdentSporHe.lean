module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporGlue
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.QuasithinUnique.Id2519.SporHe

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.HeldB CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.QuasithinUnique.Id2519.MathNoLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Orders

theorem not_kOrder_7560 : ¬ KOrder 7560 := by
  rintro (h | h | ⟨p, hp, h7, hpn⟩)
  · omega
  · omega
  · have h17 := seventeen_le_of_isFermatOrMersenne hp h7
    have hp24 : p ≤ 24 := by
      by_contra hlt
      push Not at hlt
      have h25 : 25 * (25 * 25 - 1) ≤ p * (p * p - 1) :=
        Nat.mul_le_mul hlt (Nat.sub_le_sub_right (Nat.mul_le_mul hlt hlt) 1)
      omega
    interval_cases p <;> omega

end Orders

section Commutator

variable {M : Type*} [Group M]

noncomputable def commutatorEquiv (C : Subgroup M) : ↥(commutator ↥C) ≃* ↥⁅C, C⁆ :=
  (Subgroup.equivMapOfInjective (commutator ↥C) C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]))

end Commutator

theorem heOuter_noK
    : ¬ HasKComponent ↥(heP ⊓ Subgroup.centralizer {heAutU}) := by
  obtain ⟨hD, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have e : ↥(commutator ↥heOuterC) ≃* ↥heOuterD :=
    (commutatorEquiv heOuterC).trans (MulEquiv.subgroupCongr hD.symm)
  have hq' : CFSG.IsQuasisimple ↥(commutator ↥heOuterC) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq
  have hcard : Nat.card ↥(commutator ↥heOuterC) = 7560 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_heOuterD
  have hnoK : ¬ HasKComponent ↥heOuterC :=
    not_hasKComponent_of_commutator_quasisimple hq' (by rw [hcard]; exact not_kOrder_7560)
  intro hK
  exact hnoK (hK.of_mulEquiv (MulEquiv.subgroupCongr heOuterC_eq.symm))


theorem he_nonab
    : ∃ a b : NativeSporadic.Carrier .He, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup NativeSporadic.He := CFSG.Sporadic.He.fam_he_simplicity.2.2
  let _ : CommGroup NativeSporadic.He :=
    { (inferInstance : Group NativeSporadic.He) with mul_comm := fun a b => hcon a b }
  have : Finite NativeSporadic.He := CFSG.Sporadic.He.fam_he_simplicity.1
  have hp := IsSimpleGroup.prime_card (α := NativeSporadic.He)
  rw [CFSG.Sporadic.He.card_He] at hp
  exact absurd hp (by norm_num)

noncomputable def heEquivCar
    : NativeSporadic.Carrier .He ≃* ↥heP := heEquivP

theorem he_fix_noK_of
    (hinner : ∀ t : Equiv.Perm (Fin 8330), t ∈ heP → orderOf t = 2 →
      ¬ HasKComponent ↥(heP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 8330)))))
    (α : MulAut (NativeSporadic.Carrier .He)) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ¬ HasKComponent ↥(fixSubgroup α) := by
  intro hK
  set α' : MulAut heP := MulAut.congr heEquivCar α with hα'
  have hK' : HasKComponent ↥(fixSubgroup α') :=
    hasKComponent_fixSubgroup_of_intertwine heEquivCar α α'
      (fun y => by simp [hα', MulAut.congr_apply]) hK
  have hα'2 : α' * α' = 1 := by rw [hα', ← map_mul, hα2, map_one]
  have hα'1 : α' ≠ 1 := fun h =>
    hα1 ((MulAut.congr heEquivCar).injective (by rw [map_one]; exact h))
  by_cases hin : α' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner heP
  · obtain ⟨y, hy, ⟨e⟩⟩ := fix_of_inner heP heP_center_eq_bot α' hin hα'2 hα'1
    exact hinner (y : Equiv.Perm (Fin 8330)) y.2 hy (hK'.of_mulEquiv e)
  · have hord : orderOf α' = 2 := orderOf_eq_prime (by rw [sq]; exact hα'2) hα'1
    obtain ⟨x, hx, hxP, hx2⟩ :=
      exists_heConjR_eq ctbh_full_automorphism_permutation_model.1 α' hord hin
    have hcls : ∀ x ∈ heAutGroup, x ∉ heP → orderOf x = 2 → ∃ g ∈ heP, x = g * heAutU * g⁻¹ := by
      intro x hx hxP hx2
      have h : x ∈ {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} :=
        ⟨hx, hxP, hx2⟩
      rw [ctbh_outer_involution_class_exhaustion.2.1] at h
      exact h
    obtain ⟨g, hg, hxg⟩ := hcls x x.2 hxP hx2
    have hfe : fixSubgroup α' = fixedSubgroup (heConjR x) := by
      rw [hx]
      exact Subgroup.ext fun s => mem_fixSubgroup.trans mem_fixedSubgroup.symm
    exact heOuter_noK (hK'.of_mulEquiv
      ((MulEquiv.subgroupCongr hfe).trans (fixedSubgroupEquivOfConj x hg heAutU hxg)))

theorem tabIdentFor_he_of
    (hinner : ∀ t : Equiv.Perm (Fin 8330), t ∈ heP → orderOf t = 2 →
      ¬ HasKComponent ↥(heP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 8330))))) :
    TabIdentFor (@Ident.FamSporadic .He) :=
  tabIdentFor_of_fix CFSG.Sporadic.He.fam_he_simplicity.2.2 he_nonab (he_fix_noK_of hinner)

end CFSG.QuasithinUnique.Id2519.SporHe
