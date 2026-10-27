module

public import CFSG.Timmesfeld.LieEmbed.SLE6
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVRoots
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open scoped commutatorElement

@[expose] def e7A5Pos (m : Fin Tag.E7.rank) : ℕ := (![0, 0, 1, 2, 3, 4, 0] : Fin 7 → ℕ) m

@[expose] def e7A5Root (i j : Fin 6) : Fin Tag.E7.rank → ℤ := fun m =>
  if m.val = 1 ∨ m.val = 6 then 0 else
    (if i.val ≤ e7A5Pos m ∧ e7A5Pos m < j.val then 1 else 0) -
      (if j.val ≤ e7A5Pos m ∧ e7A5Pos m < i.val then 1 else 0)

theorem e7A5Root_check : ∀ i j : Fin 6, i ≠ j →
    isRootB .E7 (e7A5Root i j) = true ∧ vLevel (e7A5Root i j) = 0 := by
  decide +kernel

theorem e7A5Root_add_check : ∀ i j l : Fin 6, e7A5Root i j + e7A5Root j l = e7A5Root i l := by
  decide +kernel

theorem e7A5Root_injective_check : ∀ i j k l : Fin 6, i ≠ j →
    e7A5Root i j = e7A5Root k l → i = k ∧ j = l := by
  decide +kernel

theorem e7A5Root_add_ne_zero_check : ∀ i j k l : Fin 6,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i)) → e7A5Root i j + e7A5Root k l ≠ 0 := by
  decide +kernel

theorem not_isRoot_e7A5Root_add_check : ∀ i j k l : Fin 6,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      isRootB .E7 (e7A5Root i j + e7A5Root k l) = false := by
  decide +kernel


theorem isRoot_e7A5Root {i j : Fin 6} (h : i ≠ j) : IsRoot .E7 (e7A5Root i j) :=
  isRootB_iff.1 (e7A5Root_check i j h).1

theorem vLevel_e7A5Root {i j : Fin 6} (h : i ≠ j) : vLevel (e7A5Root i j) = 0 :=
  (e7A5Root_check i j h).2

theorem e7A5Root_add (i j l : Fin 6) : e7A5Root i j + e7A5Root j l = e7A5Root i l :=
  e7A5Root_add_check i j l

theorem e7A5Root_injective {i j k l : Fin 6} (hij : i ≠ j) (h : e7A5Root i j = e7A5Root k l) :
    i = k ∧ j = l :=
  e7A5Root_injective_check i j k l hij h

theorem e7A5Root_add_ne_zero {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) : e7A5Root i j + e7A5Root k l ≠ 0 :=
  e7A5Root_add_ne_zero_check i j k l ⟨hij, hkl, hex⟩

theorem not_isRoot_e7A5Root_add {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (hjk : j ≠ k) (hil : i ≠ l) :
    ¬ IsRoot .E7 (e7A5Root i j + e7A5Root k l) := by
  rw [← isRootB_iff, not_isRoot_e7A5Root_add_check i j k l ⟨hij, hkl, hex, hjk, hil⟩]
  exact Bool.false_ne_true

variable {K : Type} [Field K]


theorem oddDerivLacedCheck_E7 : CFSG.SeitzReduction.oddDerivLacedCheck .E7 = true :=
  CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl)))

theorem e7A5_commutator [CharP K 2] {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (c d : K) :
    ⁅pinnedX .E7 K (e7A5Root i j) c, pinnedX .E7 K (e7A5Root k l) d⁆ =
      if j = k then pinnedX .E7 K (e7A5Root i l) (c * d)
      else if i = l then pinnedX .E7 K (e7A5Root k j) (-(c * d)) else 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hα := isRoot_e7A5Root hij
  have hβ := isRoot_e7A5Root hkl
  have hne' : e7A5Root i j ≠ -e7A5Root k l := fun h =>
    e7A5Root_add_ne_zero hij hkl hex (by rw [h, neg_add_cancel])
  by_cases hjk : j = k
  · subst hjk
    have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
    rw [ite_eq_left rfl]
    have hs : e7A5Root i j + e7A5Root j l = e7A5Root i l := e7A5Root_add i j l
    have hne : e7A5Root i j ≠ e7A5Root j l := fun h => hij (e7A5Root_injective hij h).1
    rw [CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced h2 oddDerivLacedCheck_E7
      hα hβ hne hne' (hs ▸ isRoot_e7A5Root hil) c d, hs]
  · rw [ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      rw [ite_eq_left rfl]
      have hkj : k ≠ j := fun h => hjk h.symm
      have hs : e7A5Root i j + e7A5Root k i = e7A5Root k j := by
        rw [add_comm, e7A5Root_add]
      have hne : e7A5Root i j ≠ e7A5Root k i := fun h => by
        exact hij (e7A5Root_injective hij h).2.symm
      rw [CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced h2 oddDerivLacedCheck_E7
        hα hβ hne hne' (hs ▸ isRoot_e7A5Root hkj) c d, hs, CharTwo.neg_eq]
    · rw [ite_eq_right hil, commutatorElement_eq_one_iff_commute]
      exact CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hα hβ hne'
        (not_isRoot_e7A5Root_add hij hkl hex hjk hil) c d

variable (K) in
@[expose] noncomputable def e7A5Elt (i j : Fin 6) (c : K) : adjointGroup .E7 K :=
  ⟨pinnedX .E7 K (e7A5Root i j) c, pinnedX_mem_adjointGroup _ c⟩

theorem coe_e7A5Elt (i j : Fin 6) (c : K) :
    (e7A5Elt K i j c : ModGL .E7 K) = pinnedX .E7 K (e7A5Root i j) c := rfl

theorem e7A5Elt_add (i j : Fin 6) (c d : K) :
    e7A5Elt K i j c * e7A5Elt K i j d = e7A5Elt K i j (c + d) :=
  Subtype.ext (pinnedX_add .E7 K _ c d).symm

theorem e7A5Elt_neg [CharP K 2] (i j : Fin 6) (c : K) : e7A5Elt K i j (-c) = e7A5Elt K i j c := by
  rw [CharTwo.neg_eq]

theorem e7A5Elt_commutator [CharP K 2] {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (c d : K) :
    ⁅e7A5Elt K i j c, e7A5Elt K k l d⁆ =
      if j = k then e7A5Elt K i l (c * d)
      else if i = l then e7A5Elt K k j (-(c * d)) else 1 := by
  apply Subtype.ext
  have h := e7A5_commutator (K := K) hij hkl hex c d
  rw [commutatorElement_def] at h ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e7A5Elt]
  rw [h]
  split_ifs <;> rfl

theorem exists_slToAdjointE7 [Finite K] [CharP K 2] :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 6) K →* adjointGroup .E7 K,
      ∀ (i j : Fin 6) (hij : i ≠ j) (c : K),
        φ (Matrix.SpecialLinearGroup.transvection hij c) = e7A5Elt K i j c :=
  exists_hom_of_steinbergRels (m := 5) (by norm_num) (x := fun i j c => e7A5Elt K i j c)
    (fun i j _ c d => e7A5Elt_add i j c d) fun _ _ _ _ hij hkl hex c d =>
      e7A5Elt_commutator hij hkl hex c d

variable (K) in
@[expose] noncomputable def slToAdjointE7 [Finite K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 6) K →* adjointGroup .E7 K :=
  (exists_slToAdjointE7 (K := K)).choose

theorem slToAdjointE7_transvection [Finite K] [CharP K 2] {i j : Fin 6} (hij : i ≠ j) (c : K) :
    slToAdjointE7 K (Matrix.SpecialLinearGroup.transvection hij c) = e7A5Elt K i j c :=
  (exists_slToAdjointE7 (K := K)).choose_spec i j hij c

end CFSG.SeitzReduction.E7Pilot
