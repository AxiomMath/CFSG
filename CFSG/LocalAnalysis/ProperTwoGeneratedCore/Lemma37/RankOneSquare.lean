module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneT1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal] (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
  (eP : (P : Subgroup J) ≃* QuaternionGroup 2)
  (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 5))
include h

omit [Finite G] h in
theorem action_quaternionElt (g : QuaternionGroup 2) :
    componentQuotientAction J (quaternionElt P eP g) = MulAut.conj (quaternionMap P eP g) :=
  componentQuotientAction_coe J ((eP.symm g : (P : Subgroup J)) : J)

include hP in
theorem perm_conj_four {x : EscapingQuotient z} (hxS : x ∈ escapingSylowImage S z)
    {σ : Perm (Fin 5)}
    (hσ : ∀ y, permOf e (componentQuotientAction J x y) = σ * permOf e y * σ⁻¹)
    {g : QuaternionGroup 2} (hg : quaternionMap P eP g ≠ 1) :
    σ * permOf e (quaternionMap P eP g) * σ⁻¹ = permOf e (quaternionMap P eP (.a 1)) ∨
      σ * permOf e (quaternionMap P eP g) * σ⁻¹ = permOf e (quaternionMap P eP (.xa 0)) ∨
      σ * permOf e (quaternionMap P eP g) * σ⁻¹ =
        permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) := by
  have hmem : ∀ y, y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J)) ↔ InFour P eP y := fun y =>
    (mem_sylowQuotient_iff P eP y).trans (h.inFour_iff P eP y).symm
  rw [← hσ]
  refine permOf_of_inFour P eP e ((hmem _).mp (action_mem_sylowQuotient P hP hxS
    ((hmem _).mpr ((h.inFour_iff P eP _).mpr ⟨g, rfl⟩)))) ?_
  intro h1
  exact hg ((componentQuotientAction J x).injective (h1.trans (map_one _).symm))

theorem sq_mem_centralizer_of_perm {x : EscapingQuotient z} {σ : Perm (Fin 5)}
    (hσ : ∀ y, permOf e (componentQuotientAction J x y) = σ * permOf e y * σ⁻¹)
    {g : QuaternionGroup 2}
    (hsq : σ * permOf e (quaternionMap P eP g) * (σ * permOf e (quaternionMap P eP g)) = 1) :
    x * quaternionElt P eP g * (x * quaternionElt P eP g) ∈
      Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  rw [← h.action_eq_one_iff]
  ext y
  apply permOf_injective e
  set v := permOf e (quaternionMap P eP g) with hv
  have hstep : ∀ y', permOf e (componentQuotientAction J (x * quaternionElt P eP g) y') =
      (σ * v) * permOf e y' * (σ * v)⁻¹ := by
    intro y'
    rw [map_mul, MulAut.mul_apply, hσ, action_quaternionElt, MulAut.conj_apply, permOf_mul,
      permOf_mul, permOf_inv, ← hv]
    group
  rw [map_mul, MulAut.mul_apply, hstep, hstep, MulAut.one_apply]
  have hinv : (σ * v)⁻¹ = σ * v := by
    rw [inv_eq_iff_mul_eq_one]
    exact hsq
  rw [hinv]
  calc σ * v * (σ * v * permOf e y * (σ * v)) * (σ * v) =
      (σ * v * (σ * v)) * permOf e y * ((σ * v) * (σ * v)) := by group
    _ = permOf e y := by rw [hsq, one_mul, mul_one]

theorem exists_sq_mem_centralizer
    {w₀ : EscapingQuotient z} (hw₀S : w₀ ∈ escapingSylowImage S z)
    (hw₀ : w₀ ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    ∃ w ∈ escapingSylowImage S z, w ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧
      w * w ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_alternatingGroup_five
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  obtain ⟨σ, hσ'⟩ := exists_perm_of_mulEquiv e (componentQuotientAction J w₀)
  have hσ : ∀ y, permOf e (componentQuotientAction J w₀ y) = σ * permOf e y * σ⁻¹ := hσ'
  have hsign : Perm.sign σ ≠ 1 := fun hs => hw₀ ((h.action_mem_inner_iff).mp
    ⟨e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hs⟩, by
      ext y
      apply permOf_injective e
      rw [hσ y, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv]
      simp [permOf]⟩)
  have hw₀2 : w₀ * w₀ ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    have := h.inv_mul_mem_sup_of_not_mem (u := w₀⁻¹) (v := w₀)
      (fun h1 => hw₀ (by simpa using Subgroup.inv_mem _ h1)) hw₀
    rwa [inv_inv] at this
  obtain ⟨q, hqS, hqJ, c, -, hcK, hqc⟩ :=
    h.exists_mul_eq_of_mem_sup ((escapingSylowImage S z).mul_mem hw₀S hw₀S) hw₀2
  obtain ⟨g, rfl⟩ := exists_quaternionElt_eq P hP eP hqS hqJ
  have hσσ : σ * σ = permOf e (quaternionMap P eP g) := by
    have hτ := perm_eq_one_of_forall_conj (τ := (permOf e (quaternionMap P eP g))⁻¹ * (σ * σ))
      (fun a => by
        have h1 := hσ (componentQuotientAction J w₀ (e.symm a))
        rw [hσ (e.symm a), ← MulAut.mul_apply, ← map_mul, ← hqc, map_mul,
          (h.action_eq_one_iff).mpr hcK, mul_one, action_quaternionElt, MulAut.conj_apply,
          permOf_mul, permOf_mul, permOf_inv] at h1
        simp only [permOf, MulEquiv.apply_symm_apply] at h1
        rw [mul_inv_rev, inv_inv]
        calc (permOf e (quaternionMap P eP g))⁻¹ * (σ * σ) * (a : Perm (Fin 5)) *
              (σ⁻¹ * σ⁻¹ * permOf e (quaternionMap P eP g)) =
            (permOf e (quaternionMap P eP g))⁻¹ * (σ * (σ * a * σ⁻¹) * σ⁻¹) *
              permOf e (quaternionMap P eP g) := by group
          _ = a := by
            rw [← h1]
            simp only [permOf]
            group)
    rw [inv_mul_eq_one] at hτ
    exact hτ.symm
  have hV : σ * σ = 1 ∨ σ * σ = permOf e (quaternionMap P eP (.a 1)) ∨
      σ * σ = permOf e (quaternionMap P eP (.xa 0)) ∨
      σ * σ = permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) := by
    rw [hσσ]
    rcases h.quaternionMap_mem P eP g with h1 | h1 | h1 | h1
    · exact Or.inl (by rw [h1, permOf_one])
    · exact Or.inr (Or.inl (by rw [h1]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h1])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h1, permOf_mul])))
  obtain ⟨hA, hB⟩ := h.fourGroup P eP e
  obtain ⟨hA1, hB1, -⟩ := h.quaternionMap_ne P eP
  have hnot : ∀ g' : QuaternionGroup 2,
      w₀ * quaternionElt P eP g' ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    fun g' h1 => hw₀ (by
      have := (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))).mul_mem h1
        (Subgroup.mem_sup_left (J.inv_mem (quaternionElt_mem P eP g')))
      rwa [mul_inv_cancel_right] at this)
  have hS : ∀ g' : QuaternionGroup 2, w₀ * quaternionElt P eP g' ∈ escapingSylowImage S z :=
    fun g' => (escapingSylowImage S z).mul_mem hw₀S (quaternionElt_mem_sylowImage P hP eP g')
  rcases s5_exists_mul_involution σ hsign _ hA _ ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1,
      hB.2.2.2.2, h.perm_conj_four P hP eP e hw₀S hσ hA1, h.perm_conj_four P hP eP e hw₀S hσ hB1,
      hV⟩ with h1 | h1 | h1 | h1
  · refine ⟨w₀ * quaternionElt P eP 1, hS 1, hnot 1, h.sq_mem_centralizer_of_perm P eP e hσ ?_⟩
    rw [map_one, permOf_one, mul_one]
    exact h1
  · exact ⟨_, hS _, hnot _, h.sq_mem_centralizer_of_perm P eP e hσ h1⟩
  · exact ⟨_, hS _, hnot _, h.sq_mem_centralizer_of_perm P eP e hσ h1⟩
  · refine ⟨w₀ * quaternionElt P eP (.a 1 * .xa 0), hS _, hnot _,
      h.sq_mem_centralizer_of_perm P eP e hσ ?_⟩
    rw [map_mul, permOf_mul]
    exact h1

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
