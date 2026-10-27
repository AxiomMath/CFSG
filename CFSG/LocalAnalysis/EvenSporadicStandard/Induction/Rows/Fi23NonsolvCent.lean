module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Pair
public import CFSG.Sporadic.Fi23.S12
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Solvable
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.Sporadic.Fi23.StarKernel
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Walter.JRFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian' {H : Type*} [Group H] [IsSimpleGroup H]
    (hne : ∃ a b : H, a * b ≠ b * a) : Group.IsPerfect H := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hne
    apply hab
    have : ⁅a, b⁆ ∈ commutator H := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact h

theorem isPerfect_alternatingGroup_five : Group.IsPerfect ↥(alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine isPerfect_of_simple_nonabelian'
    ⟨⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.2 (by decide)⟩,
      ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩, fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

@[expose] def p5 : Fin 12 → Prop := fun x => 6 ≤ x.val ∧ x.val < 11

instance : DecidablePred p5 := fun x => inferInstanceAs (Decidable (6 ≤ x.val ∧ x.val < 11))

@[expose] def f5 : Fin 5 ≃ Subtype p5 where
  toFun i := ⟨⟨6 + i.val, by omega⟩, by simp [p5]; omega⟩
  invFun x := ⟨x.1.val - 6, by have := x.2; simp [p5] at this; omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    have := x.2
    simp [p5] at this
    ext
    simp
    omega

@[expose] def ext5 : Perm (Fin 5) →* Perm (Fin 12) := Perm.extendDomainHom f5

theorem ext5_comm (g : Perm (Fin 5)) {σ : Perm (Fin 12)} (hσ : ∀ x : Fin 12, 6 ≤ x.val → σ x = x) :
    ext5 g * σ = σ * ext5 g := by
  refine (Equiv.Perm.Disjoint.commute fun x => ?_).eq
  by_cases hx : 6 ≤ x.val
  · exact Or.inr (hσ x hx)
  · left
    exact Perm.extendDomain_apply_not_subtype g f5 (by simp [p5]; omega)

theorem not_isSolvable_centralizer_of_a5 {J : Type*} [Group J] (ψ : Perm (Fin 12) →* J)
    (h67 : ψ (adjSwap 11 6) * ψ (adjSwap 11 7) ≠ 1) {σ : Perm (Fin 12)}
    (hσ : ∀ x : Fin 12, 6 ≤ x.val → σ x = x) :
    ¬ Group.IsSolvable ↥(centralizer ({ψ σ} : Set J)) := by
  intro hsol
  let Q : Subgroup J := (alternatingGroup (Fin 5)).map (ψ.comp ext5)
  have hQle : Q ≤ centralizer ({ψ σ} : Set J) := by
    rintro _ ⟨g, -, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ψ (ext5 g) * ψ σ = ψ σ * ψ (ext5 g)
    rw [← map_mul, ← map_mul, ext5_comm g hσ]
  have hQperf : Group.IsPerfect ↥Q := by
    have := isPerfect_alternatingGroup_five
    exact Group.IsPerfect.map _
  have hQsol : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQle)
  have hQne : ∃ q : ↥Q, q ≠ 1 := by
    refine ⟨⟨ψ (adjSwap 11 6 * adjSwap 11 7), ⟨swap 0 1 * swap 1 2, ?_, ?_⟩⟩, fun h => h67 ?_⟩
    · exact Perm.mem_alternatingGroup.2 (by decide)
    · show ψ (ext5 (swap 0 1 * swap 1 2)) = _
      have e : ext5 (swap 0 1 * swap 1 2) = adjSwap 11 6 * adjSwap 11 7 := by decide
      rw [e]
    · have := congrArg Subtype.val h
      simpa using this
  have : Nontrivial ↥Q := ⟨⟨hQne.choose, 1, hQne.choose_spec⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥Q hQsol

theorem not_isSolvable_centralizer_of_isConj {J : Type*} [Group J] {x y : J} (h : IsConj x y)
    (hx : ¬ Group.IsSolvable ↥(centralizer ({x} : Set J))) :
    ¬ Group.IsSolvable ↥(centralizer ({y} : Set J)) := by
  intro hy
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  let f : ↥(centralizer ({x} : Set J)) →* ↥(centralizer ({y} : Set J)) :=
    ((MulAut.conj c).toMonoidHom.comp (centralizer ({x} : Set J)).subtype).codRestrict
      (centralizer ({y} : Set J)) fun g => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2
        show c * (g : J) * c⁻¹ * y = y * (c * (g : J) * c⁻¹)
        rw [← hc]
        calc c * (g : J) * c⁻¹ * (c * x * c⁻¹) = c * ((g : J) * x) * c⁻¹ := by group
          _ = c * (x * (g : J)) * c⁻¹ := by rw [← hg]
          _ = c * x * c⁻¹ * (c * (g : J) * c⁻¹) := by group
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext ((MulAut.conj c).injective (congrArg Subtype.val hab))
  exact hx (Group.isSolvable_of_isSolvable_injective hf)

section Certificates

local notation "sE" => CFSG.Sporadic.Fi23.sEl
local notation "JJ" => CFSG.Sporadic.Fi23.J

theorem sEl_ne {i j : ℕ}
    (hi : i < 11) (hj : j < 11)
    (h : CFSG.Sporadic.Fi23.Native.s12Pts[i]! ≠ CFSG.Sporadic.Fi23.Native.s12Pts[j]!) :
    sE i ≠ sE j := fun e =>
  h (CFSG.Sporadic.Fi23.conjPt_inj
    (by rw [CFSG.Sporadic.Fi23.orb_size]; exact CFSG.Sporadic.Fi23.s12Pts_lt hi)
    (by rw [CFSG.Sporadic.Fi23.orb_size]; exact CFSG.Sporadic.Fi23.s12Pts_lt hj) e)

theorem adjSwap_fix {i : ℕ} (hi : i + 1 < 6) {x : Fin 12} (hx : 6 ≤ x.val) :
    adjSwap 11 i x = x := by
  rw [adjSwap_of_lt (by omega : i < 11)]
  exact swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem hom_s67_ne_one
    {ψ : Perm (Fin 12) →* JJ} (hψ : ∀ i, i < 11 → ψ (adjSwap 11 i) = sE i) :
    ψ (adjSwap 11 6) * ψ (adjSwap 11 7) ≠ 1 := by
  rw [hψ 6 (by norm_num), hψ 7 (by norm_num)]
  intro h
  exact sEl_ne (i := 6) (j := 7) (by norm_num) (by norm_num) (by decide)
    (mul_right_cancel (h.trans (CFSG.Sporadic.Fi23.sEl_sq (i := 7) (by norm_num)).symm))

theorem not_isSolvable_centralizer_s0 :
    ¬ Group.IsSolvable ↥(centralizer ({sE 0} : Set JJ)) := by
  obtain ⟨ψ, hψ⟩ := CFSG.Sporadic.Fi23.exists_hom_s12
  rw [← hψ 0 (by norm_num)]
  exact not_isSolvable_centralizer_of_a5 ψ (hom_s67_ne_one hψ) fun x hx => by
    exact adjSwap_fix (by norm_num) hx

theorem not_isSolvable_centralizer_s02 :
    ¬ Group.IsSolvable ↥(centralizer ({sE 0 * sE 2} : Set JJ)) := by
  obtain ⟨ψ, hψ⟩ := CFSG.Sporadic.Fi23.exists_hom_s12
  have hσ : ψ (adjSwap 11 0 * adjSwap 11 2) = sE 0 * sE 2 := by
    rw [map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num)]
  rw [← hσ]
  exact not_isSolvable_centralizer_of_a5 ψ (hom_s67_ne_one hψ) fun x hx => by
    rw [Perm.mul_apply, adjSwap_fix (by norm_num) hx, adjSwap_fix (by norm_num) hx]

theorem not_isSolvable_centralizer_s024 :
    ¬ Group.IsSolvable ↥(centralizer ({sE 0 * sE 2 * sE 4} : Set JJ)) := by
  obtain ⟨ψ, hψ⟩ := CFSG.Sporadic.Fi23.exists_hom_s12
  have hσ : ψ (adjSwap 11 0 * adjSwap 11 2 * adjSwap 11 4) = sE 0 * sE 2 * sE 4 := by
    rw [map_mul, map_mul, hψ 0 (by norm_num), hψ 2 (by norm_num), hψ 4 (by norm_num)]
  rw [← hσ]
  exact not_isSolvable_centralizer_of_a5 ψ (hom_s67_ne_one hψ) fun x hx => by
    rw [Perm.mul_apply, Perm.mul_apply, adjSwap_fix (by norm_num) hx,
      adjSwap_fix (by norm_num) hx, adjSwap_fix (by norm_num) hx]

theorem isConj_t2_s024 :
    IsConj CFSG.Sporadic.Fi23.t2 (sE 0 * sE 2 * sE 4) := by
  have hne : ∀ i j : ℕ, i < 11 → j < 11 → CFSG.Sporadic.Fi23.Native.s12Pts[i]! ≠
      CFSG.Sporadic.Fi23.Native.s12Pts[j]! → sE i ≠ sE j :=
    fun i j hi hj h => sEl_ne hi hj h
  refine CFSG.Sporadic.Fi23.isConj_t2_of_mem (CFSG.Sporadic.Fi23.sEl_mem (by norm_num))
    ⟨CFSG.Sporadic.Fi23.sEl_mem (by norm_num),
      (hne 0 2 (by norm_num) (by norm_num) (by decide)).symm,
      (CFSG.Sporadic.Fi23.sEl_comm (by norm_num) (by norm_num)).symm⟩
    ⟨CFSG.Sporadic.Fi23.sEl_mem (by norm_num),
      (hne 0 4 (by norm_num) (by norm_num) (by decide)).symm,
      (CFSG.Sporadic.Fi23.sEl_comm (by norm_num) (by norm_num)).symm⟩
    ⟨CFSG.Sporadic.Fi23.sEl_mem (by norm_num),
      (hne 2 4 (by norm_num) (by norm_num) (by decide)).symm,
      (CFSG.Sporadic.Fi23.sEl_comm (by norm_num) (by norm_num)).symm⟩

theorem not_isSolvable_centralizer_involution
    {t : JJ} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) : ¬ Group.IsSolvable ↥(centralizer ({t} : Set JJ)) := by
  rcases CFSG.Sporadic.Fi23.involution_cover t ht2 ht1 with h | h | h
  · exact not_isSolvable_centralizer_of_isConj
      (CFSG.Sporadic.Fi23.sEl_mem (i := 0) (by norm_num) |>.symm.trans h)
      not_isSolvable_centralizer_s0
  · exact not_isSolvable_centralizer_of_isConj
      (CFSG.Sporadic.Fi23.isConj_d_mul_d1_s2.symm.trans h) not_isSolvable_centralizer_s02
  · exact not_isSolvable_centralizer_of_isConj (isConj_t2_s024.symm.trans h)
      not_isSolvable_centralizer_s024

end Certificates

end CFSG.EvenSporadicStandard.Induction
