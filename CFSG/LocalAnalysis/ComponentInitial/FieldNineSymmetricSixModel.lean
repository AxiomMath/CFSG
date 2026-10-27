module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace FieldNine

open Equiv
open scoped Pointwise

@[expose] def mulModel (p q : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

@[expose] def normModel (q : ZMod 3 × ZMod 3) : ZMod 3 := q.1 * q.1 + q.2 * q.2

@[expose] def negInvModel (q : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (-q.1 * normModel q, q.2 * normModel q)

@[expose] def conjModel (q : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 := (q.1, -q.2)

theorem mulModel_negInvModel :
    ∀ q : ZMod 3 × ZMod 3, q ≠ 0 → mulModel q (negInvModel q) = (-1, 0) := by
  decide

theorem mulModel_mulModel_self :
    ∀ q : ZMod 3 × ZMod 3, mulModel (mulModel q q) q = conjModel q := by
  decide

theorem eq_zero_of_normModel_eq_zero : ∀ q : ZMod 3 × ZMod 3, normModel q = 0 → q = 0 := by
  decide

@[expose] def label : Option (ZMod 3 × ZMod 3) → Fin 10
  | none => 9
  | some p => ⟨p.1.val + 3 * p.2.val, by
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      simp only [ZMod.val] at *
      omega⟩

@[expose] def unlabel (x : Fin 10) : Option (ZMod 3 × ZMod 3) :=
  if x.val = 9 then none else some ((x.val % 3 : ℕ), (x.val / 3 : ℕ))

@[expose] def labelEquiv : Option (ZMod 3 × ZMod 3) ≃ Fin 10 :=
  ⟨label, unlabel, by decide, by decide⟩

@[expose] def translationModel (p : ZMod 3 × ZMod 3) : Perm (Option (ZMod 3 × ZMod 3)) :=
  Equiv.optionCongr (Equiv.addRight p)

@[expose] def inversionFun : Option (ZMod 3 × ZMod 3) → Option (ZMod 3 × ZMod 3)
  | none => some 0
  | some q => if q = 0 then none else some (negInvModel q)

theorem inversionFun_inversionFun : ∀ x, inversionFun (inversionFun x) = x := by decide

@[expose] def inversionModel : Perm (Option (ZMod 3 × ZMod 3)) :=
  Function.Involutive.toPerm inversionFun inversionFun_inversionFun

theorem inversionModel_apply (x : Option (ZMod 3 × ZMod 3)) :
    inversionModel x = inversionFun x := rfl

@[expose] def frobeniusModel : Perm (Option (ZMod 3 × ZMod 3)) :=
  Equiv.optionCongr ⟨conjModel, conjModel, by decide, by decide⟩

@[expose] def translationLabel (p : ZMod 3 × ZMod 3) : Perm (Fin 10) :=
  labelEquiv.permCongr (translationModel p)

@[expose] def inversionLabel : Perm (Fin 10) := labelEquiv.permCongr inversionModel

@[expose] def frobeniusLabel : Perm (Fin 10) := labelEquiv.permCongr frobeniusModel

theorem generators_apply :
    ⇑(translationLabel (1, 0)) = ![1, 2, 0, 4, 5, 3, 7, 8, 6, 9] ∧
      ⇑(translationLabel (0, 1)) = ![3, 4, 5, 6, 7, 8, 0, 1, 2, 9] ∧
      ⇑inversionLabel = ![9, 2, 1, 3, 7, 8, 6, 4, 5, 0] ∧
      ⇑frobeniusLabel = ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9] := by
  decide

@[expose] def involutionValues : Fin 15 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 6, 7, 8, 3, 4, 5, 9], ![0, 1, 9, 7, 6, 5, 4, 3, 8, 2],
    ![0, 2, 1, 3, 5, 4, 6, 8, 7, 9], ![0, 5, 4, 3, 2, 1, 9, 7, 8, 6],
    ![0, 8, 7, 9, 4, 5, 6, 2, 1, 3], ![0, 9, 2, 8, 4, 6, 5, 7, 3, 1],
    ![1, 0, 2, 4, 3, 5, 7, 6, 8, 9], ![2, 1, 0, 5, 4, 3, 8, 7, 6, 9],
    ![3, 4, 5, 0, 1, 2, 6, 7, 8, 9], ![4, 3, 2, 1, 0, 5, 6, 7, 9, 8],
    ![5, 1, 3, 2, 4, 0, 6, 9, 8, 7], ![6, 7, 8, 3, 4, 5, 0, 1, 2, 9],
    ![7, 6, 2, 3, 4, 9, 1, 0, 8, 5], ![8, 1, 6, 3, 9, 5, 2, 7, 0, 4],
    ![9, 1, 2, 3, 8, 7, 6, 5, 4, 0]]

theorem involutionValues_involutive : ∀ j x, involutionValues j (involutionValues j x) = x := by
  decide

@[expose] def involution (j : Fin 15) : Perm (Fin 10) :=
  Function.Involutive.toPerm (involutionValues j) (involutionValues_involutive j)

@[expose] def generator : Fin 4 → Perm (Fin 10) :=
  ![translationLabel (1, 0), translationLabel (0, 1), inversionLabel, frobeniusLabel]

@[expose] def conjugationRow : Fin 4 → Fin 15 → Fin 15 :=
  ![![0, 14, 7, 10, 13, 1, 2, 6, 8, 3, 9, 11, 4, 12, 5],
    ![11, 12, 2, 14, 3, 13, 6, 7, 0, 1, 5, 8, 9, 10, 4],
    ![0, 6, 2, 11, 8, 7, 1, 5, 4, 10, 9, 3, 13, 12, 14],
    ![0, 1, 2, 4, 3, 5, 6, 7, 11, 12, 13, 8, 9, 10, 14]]

theorem generator_conj_involution :
    ∀ k j, generator k * involution j * (generator k)⁻¹ = involution (conjugationRow k j) := by
  decide

@[expose] def fixedSet : Fin 15 → Finset (Fin 10) :=
  ![{0, 1, 2, 9}, {0, 1, 5, 8}, {0, 3, 6, 9}, {0, 3, 7, 8}, {0, 4, 5, 6}, {0, 2, 4, 7},
    {2, 5, 8, 9}, {1, 4, 7, 9}, {6, 7, 8, 9}, {2, 5, 6, 7}, {1, 4, 6, 8}, {3, 4, 5, 9},
    {2, 3, 4, 8}, {1, 3, 5, 7}, {1, 2, 3, 6}]

@[expose] def blockIndex : Fin 6 → Finset (Fin 15) :=
  ![{0, 3, 9, 10, 11}, {0, 4, 8, 12, 13}, {1, 2, 7, 9, 12}, {1, 5, 8, 11, 14},
    {2, 5, 6, 10, 13}, {3, 4, 6, 7, 14}]

@[expose] def block (i : Fin 6) : Finset (Finset (Fin 10)) := (blockIndex i).image fixedSet

theorem fixedSet_eq_filter : ∀ j, fixedSet j = Finset.univ.filter fun x => involution j x = x := by
  decide

theorem fixedSet_injective : Function.Injective fixedSet := by decide

theorem block_injective : Function.Injective block := by decide

@[expose] def blockImageOne : Perm (Fin 6) :=
  ⟨![0, 1, 5, 3, 2, 4], ![0, 1, 4, 3, 5, 2], by decide, by decide⟩

@[expose] def blockImageI : Perm (Fin 6) :=
  ⟨![3, 0, 2, 1, 4, 5], ![1, 3, 2, 0, 4, 5], by decide, by decide⟩

@[expose] def blockImageInversion : Perm (Fin 6) :=
  ⟨![0, 1, 4, 5, 2, 3], ![0, 1, 4, 5, 2, 3], by decide, by decide⟩

theorem translationLabel_smul_block : ∀ p : ZMod 3 × ZMod 3, ∀ i,
    translationLabel p • block i = block ((blockImageOne ^ p.1.val * blockImageI ^ p.2.val) i) := by
  decide

theorem inversionLabel_smul_block :
    ∀ i, inversionLabel • block i = block (blockImageInversion i) := by
  decide

theorem frobeniusLabel_smul_block : ∀ i, frobeniusLabel • block i = block (swap 0 1 i) := by
  decide

@[expose] def blockStabilizer : Subgroup (Perm (Fin 10)) where
  carrier := {g | ∃ π : Perm (Fin 6), ∀ i, g • block i = block (π i)}
  one_mem' := ⟨1, fun i => by rw [one_smul, Perm.one_apply]⟩
  mul_mem' := by
    rintro g h ⟨π, hπ⟩ ⟨ρ, hρ⟩
    exact ⟨π * ρ, fun i => by rw [mul_smul, hρ, hπ, Perm.mul_apply]⟩
  inv_mem' := by
    rintro g ⟨π, hπ⟩
    refine ⟨π⁻¹, fun i => ?_⟩
    rw [inv_smul_eq_iff, hπ, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

theorem eq_of_smul_block {g : Perm (Fin 10)} {π ρ : Perm (Fin 6)}
    (hπ : ∀ i, g • block i = block (π i)) (hρ : ∀ i, g • block i = block (ρ i)) : π = ρ :=
  Equiv.ext fun i => block_injective ((hπ i).symm.trans (hρ i))

@[expose] noncomputable def blockHom : blockStabilizer →* Perm (Fin 6) where
  toFun g := Classical.choose g.2
  map_one' := eq_of_smul_block (Classical.choose_spec (1 : blockStabilizer).2)
    fun i => by rw [OneMemClass.coe_one, one_smul, Perm.one_apply]
  map_mul' g h := eq_of_smul_block (Classical.choose_spec (g * h).2) fun i => by
    rw [MulMemClass.coe_mul, mul_smul, Classical.choose_spec h.2, Classical.choose_spec g.2,
      Perm.mul_apply]

theorem blockHom_eq {g : blockStabilizer} {π : Perm (Fin 6)}
    (h : ∀ i, (g : Perm (Fin 10)) • block i = block (π i)) : blockHom g = π :=
  eq_of_smul_block (Classical.choose_spec g.2) h

theorem translationLabel_mem (p : ZMod 3 × ZMod 3) : translationLabel p ∈ blockStabilizer :=
  ⟨_, translationLabel_smul_block p⟩

theorem inversionLabel_mem : inversionLabel ∈ blockStabilizer := ⟨_, inversionLabel_smul_block⟩

theorem frobeniusLabel_mem : frobeniusLabel ∈ blockStabilizer := ⟨_, frobeniusLabel_smul_block⟩

theorem blockImage_word_eq :
    blockImageOne * blockImageI * blockImageI * blockImageInversion * blockImageI *
        blockImageInversion * swap 0 1 = List.formPerm [0, 1, 4, 2, 5, 3] := by
  decide

theorem closure_blockImages_eq_top {H : Subgroup (Perm (Fin 6))} (h₁ : blockImageOne ∈ H)
    (hi : blockImageI ∈ H) (hι : blockImageInversion ∈ H) (hσ : swap 0 1 ∈ H) : H = ⊤ := by
  set c : Perm (Fin 6) := List.formPerm [0, 1, 4, 2, 5, 3] with hc
  have hcyc : c.IsCycle := List.isCycle_formPerm (by decide) (by decide)
  have hsupp : c.support = Finset.univ := by decide
  have hc0 : c 0 = 1 := by decide
  have htop := Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp 0
  rw [hc0] at htop
  have hcH : c ∈ H := by
    rw [hc, ← blockImage_word_eq]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem h₁ hi) hi) hι) hi)
      hι) hσ
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hcH
  · exact hσ

end FieldNine

end CFSG.LocalAnalysis.ComponentInitial
