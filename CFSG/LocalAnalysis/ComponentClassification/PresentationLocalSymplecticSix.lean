module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.ComponentClassification.PresentationLocal

open Matrix Equiv Equiv.Perm

@[expose] def antidiagGram : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) + j = 3 then 1 else 0

@[expose] def sympFour : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {h | (h : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * antidiagGram * h = antidiagGram}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at ha hb ⊢
    rw [show (↑b : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * (↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *
        antidiagGram * ((↑a : Matrix (Fin 4) (Fin 4) (ZMod 2)) * ↑b) =
        (↑b : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * ((↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *
          antidiagGram * ↑a) * ↑b by simp only [Matrix.mul_assoc], ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 : (a.inv)ᵀ * (↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ = 1 := by
      rw [← transpose_mul, a.val_inv, transpose_one]
    change (a.inv)ᵀ * antidiagGram * a.inv = antidiagGram
    rw [show (a.inv)ᵀ * antidiagGram * a.inv = (a.inv)ᵀ * ((↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *
        antidiagGram * ↑a) * a.inv by rw [ha]]
    rw [show (a.inv)ᵀ * ((↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * antidiagGram * ↑a) * a.inv =
        ((a.inv)ᵀ * (↑a : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ) * antidiagGram *
          ((↑a : Matrix (Fin 4) (Fin 4) (ZMod 2)) * a.inv) by simp only [Matrix.mul_assoc],
      h1, a.val_inv, Matrix.one_mul, Matrix.mul_one]

theorem mem_sympFour_iff (h : GL (Fin 4) (ZMod 2)) :
    h ∈ sympFour ↔ (h : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * antidiagGram * h = antidiagGram :=
  Iff.rfl

@[expose] def quadForm (a v : Fin 4 → ZMod 2) : ZMod 2 :=
  v 0 * v 3 + v 1 * v 2 + (a 0 * v 0 + a 1 * v 1 + a 2 * v 2 + a 3 * v 3)

@[expose] def omegaVec : Fin 6 → Fin 4 → ZMod 2 :=
  ![![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 0, 0, 1], ![1, 0, 1, 1], ![1, 1, 0, 1], ![1, 1, 1, 0]]

@[expose] def coeffTransform (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (a : Fin 4 → ZMod 2) :
    Fin 4 → ZMod 2 :=
  fun i => quadForm a fun l => g l i

theorem quadForm_single (a : Fin 4 → ZMod 2) (i : Fin 4) : quadForm a (Pi.single i 1) = a i := by
  fin_cases i <;> simp [quadForm]

theorem quadForm_injective : Function.Injective quadForm := fun a b h =>
  funext fun i => by rw [← quadForm_single a i, ← quadForm_single b i, h]

theorem quadForm_mulVec {g : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hg : gᵀ * antidiagGram * g = antidiagGram) (a v : Fin 4 → ZMod 2) :
    quadForm a (g *ᵥ v) = quadForm (coeffTransform g a) v := by
  have hr : ∀ i j : Fin 4, (gᵀ * antidiagGram * g) i j = antidiagGram i j := fun i j => by
    rw [hg]
  have r01 := hr 0 1
  have r02 := hr 0 2
  have r03 := hr 0 3
  have r12 := hr 1 2
  have r13 := hr 1 3
  have r23 := hr 2 3
  simp only [Matrix.mul_apply, Fin.sum_univ_four, transpose_apply, antidiagGram, of_apply]
    at r01 r02 r03 r12 r13 r23
  norm_num at r01 r02 r03 r12 r13 r23
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  have h0 := hsq (v 0)
  have h1 := hsq (v 1)
  have h2 := hsq (v 2)
  have h3 := hsq (v 3)
  simp only [quadForm, coeffTransform, mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (v 0 * v 1) * r01 + (v 0 * v 2) * r02 + (v 0 * v 3) * r03 +
    (v 1 * v 2) * r12 + (v 1 * v 3) * r13 + (v 2 * v 3) * r23 +
    (g 0 0 * g 3 0 + g 1 0 * g 2 0) * h0 + (g 0 1 * g 3 1 + g 1 1 * g 2 1) * h1 +
    (g 0 2 * g 3 2 + g 1 2 * g 2 2) * h2 + (g 0 3 * g 3 3 + g 1 3 * g 2 3) * h3

theorem coeffTransform_one (a : Fin 4 → ZMod 2) : coeffTransform 1 a = a := by
  funext i
  have : (fun l => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) l i) = Pi.single i 1 := by
    funext l
    simp [Matrix.one_apply, Pi.single_apply]
  rw [coeffTransform, this, quadForm_single]

theorem coeffTransform_mul {g₁ : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hg₁ : g₁ᵀ * antidiagGram * g₁ = antidiagGram) (g₂ : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (a : Fin 4 → ZMod 2) :
    coeffTransform (g₁ * g₂) a = coeffTransform g₂ (coeffTransform g₁ a) := by
  funext i
  have : (fun l => (g₁ * g₂) l i) = g₁ *ᵥ fun l => g₂ l i := by
    funext l
    simp [Matrix.mul_apply, mulVec, dotProduct]
  rw [coeffTransform, this, quadForm_mulVec hg₁]
  rfl

theorem card_zeros_omegaVec :
    ∀ k, (Finset.univ.filter fun v => quadForm (omegaVec k) v = 0).card = 6 := by
  decide

theorem exists_omegaVec_of_card_zeros : ∀ b : Fin 4 → ZMod 2,
    (Finset.univ.filter fun v => quadForm b v = 0).card = 6 → ∃ k, omegaVec k = b := by
  decide

theorem omegaVec_injective : Function.Injective omegaVec := by
  decide

theorem card_zeros_coeffTransform (g : GL (Fin 4) (ZMod 2)) (hg : g ∈ sympFour)
    (a : Fin 4 → ZMod 2) :
    (Finset.univ.filter fun v => quadForm (coeffTransform g a) v = 0).card =
      (Finset.univ.filter fun v => quadForm a v = 0).card := by
  refine Finset.card_nbij (fun v => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [quadForm_mulVec hg]
    exact hv
  · intro v _ w _ hvw
    have := congrArg (fun x => (g.inv : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) hvw
    simpa [mulVec_mulVec, g.inv_val] using this
  · intro w hw
    refine ⟨g.inv *ᵥ w, ?_, by simp [mulVec_mulVec]⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    rw [← quadForm_mulVec hg, mulVec_mulVec, g.val_inv, one_mulVec]
    exact hw

theorem exists_omegaVec_coeffTransform (g : GL (Fin 4) (ZMod 2)) (hg : g ∈ sympFour)
    (k : Fin 6) : ∃ k', omegaVec k' = coeffTransform g (omegaVec k) :=
  exists_omegaVec_of_card_zeros _ (by rw [card_zeros_coeffTransform g hg, card_zeros_omegaVec])

@[expose] def omegaIndex (b : Fin 4 → ZMod 2) : Fin 6 :=
  if b = omegaVec 0 then 0 else if b = omegaVec 1 then 1 else if b = omegaVec 2 then 2
  else if b = omegaVec 3 then 3 else if b = omegaVec 4 then 4 else 5

theorem omegaIndex_omegaVec : ∀ k, omegaIndex (omegaVec k) = k := by
  decide

@[expose] def omegaAct (h : sympFour) (k : Fin 6) : Fin 6 :=
  omegaIndex (coeffTransform (((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (omegaVec k))

theorem omegaVec_omegaAct (h : sympFour) (k : Fin 6) :
    omegaVec (omegaAct h k) = coeffTransform (((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) (omegaVec k) := by
  obtain ⟨k', hk'⟩ := exists_omegaVec_coeffTransform _ (h⁻¹ : sympFour).2 k
  rw [omegaAct, ← hk', omegaIndex_omegaVec]

theorem omegaAct_one (k : Fin 6) : omegaAct 1 k = k := by
  refine omegaVec_injective ?_
  rw [omegaVec_omegaAct, inv_one, OneMemClass.coe_one, Units.val_one, coeffTransform_one]

theorem omegaAct_mul (h₁ h₂ : sympFour) (k : Fin 6) :
    omegaAct (h₁ * h₂) k = omegaAct h₁ (omegaAct h₂ k) := by
  refine omegaVec_injective ?_
  rw [omegaVec_omegaAct, omegaVec_omegaAct, omegaVec_omegaAct, _root_.mul_inv_rev, Subgroup.coe_mul,
    Units.val_mul, coeffTransform_mul (h₂⁻¹ : sympFour).2]

@[expose] def omegaPerm : sympFour →* Perm (Fin 6) where
  toFun h :=
    { toFun := omegaAct h
      invFun := omegaAct h⁻¹
      left_inv := fun k => by rw [← omegaAct_mul, inv_mul_cancel, omegaAct_one]
      right_inv := fun k => by rw [← omegaAct_mul, mul_inv_cancel, omegaAct_one] }
  map_one' := Equiv.ext omegaAct_one
  map_mul' h₁ h₂ := Equiv.ext fun k => omegaAct_mul h₁ h₂ k

theorem omegaPerm_apply (h : sympFour) (k : Fin 6) : omegaPerm h k = omegaAct h k := rfl

theorem quadForm_omegaVec_omegaPerm (h : sympFour) (k : Fin 6) (v : Fin 4 → ZMod 2) :
    quadForm (omegaVec (omegaPerm h k)) v =
      quadForm (omegaVec k) ((((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
  rw [omegaPerm_apply, omegaVec_omegaAct, quadForm_mulVec (h⁻¹ : sympFour).2]

theorem omegaPerm_injective : Function.Injective omegaPerm := by
  rw [injective_iff_map_eq_one]
  intro h hh
  set g : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    (((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hg
  have hfix : ∀ k v, quadForm (omegaVec k) (g *ᵥ v) = quadForm (omegaVec k) v := by
    intro k v
    rw [← quadForm_omegaVec_omegaPerm, hh, Perm.one_apply]
  have d3 : ∀ w, quadForm (omegaVec 1) w - quadForm (omegaVec 0) w = w 3 := by
    intro w
    simp [quadForm, omegaVec]
    ring
  have d2 : ∀ w, quadForm (omegaVec 3) w - quadForm (omegaVec 2) w = w 2 := by
    intro w
    simp [quadForm, omegaVec]
    ring
  have d1 : ∀ w, quadForm (omegaVec 4) w - quadForm (omegaVec 2) w = w 1 := by
    intro w
    simp [quadForm, omegaVec]
    ring
  have d0 : ∀ w, quadForm (omegaVec 2) w - quadForm (omegaVec 0) w = w 0 - w 1 - w 2 + w 3 := by
    intro w
    simp [quadForm, omegaVec]
    ring
  have hcoord : ∀ v, g *ᵥ v = v := by
    intro v
    have e3 := d3 (g *ᵥ v)
    have e2 := d2 (g *ᵥ v)
    have e1 := d1 (g *ᵥ v)
    have e0 := d0 (g *ᵥ v)
    rw [hfix, hfix] at e3 e2 e1 e0
    rw [d3] at e3
    rw [d2] at e2
    rw [d1] at e1
    rw [d0] at e0
    funext i
    fin_cases i
    · change (g *ᵥ v) 0 = v 0
      linear_combination -e0 - e1 - e2 + e3
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm
  have hg1 : g = 1 := by
    ext i j
    have := congrFun (hcoord (Pi.single j 1)) i
    rw [mulVec_single_one, col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
  have hinv : h⁻¹ = 1 := Subtype.ext (Units.ext hg1)
  exact inv_eq_one.1 hinv

@[expose] def sympOfInvolutive (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (h1 : M * M = 1)
    (h2 : Mᵀ * antidiagGram * M = antidiagGram) : sympFour :=
  ⟨⟨M, M, h1, h1⟩, h2⟩

@[expose] def rootInvolutionA : sympFour :=
  sympOfInvolutive (1 + single 1 2 1) (by decide) (by decide)

@[expose] def rootInvolutionB : sympFour :=
  sympOfInvolutive (1 + single 2 1 1) (by decide) (by decide)

@[expose] def rootInvolutionC : sympFour :=
  sympOfInvolutive (1 + single 0 1 1 + single 2 3 1) (by decide) (by decide)

@[expose] def rootInvolutionD : sympFour :=
  sympOfInvolutive (1 + single 1 0 1 + single 3 2 1) (by decide) (by decide)

theorem omegaPerm_rootInvolutionA : omegaPerm rootInvolutionA = swap 2 3 := by
  decide

theorem omegaPerm_rootInvolutionB : omegaPerm rootInvolutionB = swap 2 4 := by
  decide

theorem omegaPerm_rootInvolutionC :
    omegaPerm rootInvolutionC = swap 0 1 * swap 2 4 * swap 3 5 := by
  decide

theorem omegaPerm_rootInvolutionD :
    omegaPerm rootInvolutionD = swap 0 5 * swap 1 4 * swap 2 3 := by
  decide

theorem omegaPerm_surjective : Function.Surjective omegaPerm := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  have ha : swap (2 : Fin 6) 3 ∈ omegaPerm.range := ⟨_, omegaPerm_rootInvolutionA⟩
  have hb : swap (2 : Fin 6) 4 ∈ omegaPerm.range := ⟨_, omegaPerm_rootInvolutionB⟩
  have hc : swap (0 : Fin 6) 1 * swap 2 4 * swap 3 5 ∈ omegaPerm.range :=
    ⟨_, omegaPerm_rootInvolutionC⟩
  have hd : swap (0 : Fin 6) 5 * swap 1 4 * swap 2 3 ∈ omegaPerm.range :=
    ⟨_, omegaPerm_rootInvolutionD⟩
  have h01 : swap (0 : Fin 6) 1 ∈ omegaPerm.range := by
    rw [show swap (0 : Fin 6) 1 = (swap 0 5 * swap 1 4 * swap 2 3) *
        (swap 0 1 * swap 2 4 * swap 3 5) * swap 2 3 * (swap 0 1 * swap 2 4 * swap 3 5) *
          (swap 0 5 * swap 1 4 * swap 2 3) by decide]
    exact mul_mem (mul_mem (mul_mem (mul_mem hd hc) ha) hc) hd
  have h12 : swap (1 : Fin 6) 2 ∈ omegaPerm.range := by
    rw [show swap (1 : Fin 6) 2 = swap 2 3 * (swap 0 5 * swap 1 4 * swap 2 3) * swap 2 4 *
        swap 2 3 * (swap 0 5 * swap 1 4 * swap 2 3) by decide]
    exact mul_mem (mul_mem (mul_mem (mul_mem ha hd) hb) ha) hd
  have h34 : swap (3 : Fin 6) 4 ∈ omegaPerm.range := by
    rw [show swap (3 : Fin 6) 4 = swap 2 3 * swap 2 4 * swap 2 3 by decide]
    exact mul_mem (mul_mem ha hb) ha
  have h45 : swap (4 : Fin 6) 5 ∈ omegaPerm.range := by
    rw [show swap (4 : Fin 6) 5 = (swap 0 1 * swap 2 4 * swap 3 5) * swap 2 3 *
        (swap 0 1 * swap 2 4 * swap 3 5) by decide]
    exact mul_mem (mul_mem hc ha) hc
  have hadj : ∀ i : Fin 5, swap i.castSucc i.succ ∈ omegaPerm.range := by
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact ha
    · exact h34
    · exact h45
  have hle : Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) ≤
      omegaPerm.range.toSubmonoid := Submonoid.closure_le.2 (by
        rintro _ ⟨i, rfl⟩
        exact hadj i)
  intro σ _
  exact hle (by rw [Perm.mclosure_swap_castSucc_succ]; trivial)

theorem commutator_sympFour : commutator sympFour = (alternatingGroup (Fin 6)).comap omegaPerm := by
  have hmap : (commutator sympFour).map omegaPerm = commutator (Perm (Fin 6)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 omegaPerm_surjective]
  rw [← alternatingGroup.commutator_perm_eq (by simp), ← hmap,
    Subgroup.comap_map_eq_self_of_injective omegaPerm_injective]

theorem map_commutator_sympFour :
    (commutator sympFour).map omegaPerm = alternatingGroup (Fin 6) := by
  rw [commutator_sympFour, Subgroup.map_comap_eq_self_of_surjective omegaPerm_surjective]

@[expose] def commutatorEquivAlternating : commutator sympFour ≃* alternatingGroup (Fin 6) :=
  ((MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩).subgroupMap
    (commutator sympFour)).trans (MulEquiv.subgroupCongr map_commutator_sympFour)

theorem centralizer_alternatingGroup_eq_bot {α : Type*} [Fintype α] [DecidableEq α]
    (hα4 : 4 ≤ Nat.card α) :
    Subgroup.centralizer (alternatingGroup α : Set (Perm α)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext a
  rw [Perm.one_apply]
  by_contra hab
  have : 2 ≤ (({a, g a} : Finset α)ᶜ).card := by
    rw [← Nat.add_le_add_iff_left, Finset.card_add_card_compl, ← Nat.card_eq_fintype_card,
      Finset.card_pair (Ne.symm hab)]
    exact hα4
  rw [← Nat.lt_iff_add_one_le, Finset.one_lt_card_iff] at this
  obtain ⟨c, d, hc, hd, hcd⟩ := this
  simp only [Finset.compl_insert, Finset.mem_erase, ← ne_eq, Finset.mem_compl,
    Finset.mem_singleton] at hc hd
  have hk : swap (g a) d * swap (g a) c ∈ alternatingGroup α := by
    simp [hc.2.symm, hd.2.symm]
  have hka : (swap (g a) d * swap (g a) c) a = a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hab) hc.1.symm,
      swap_apply_of_ne_of_ne (Ne.symm hab) hd.1.symm]
  have hkga : (swap (g a) d * swap (g a) c) (g a) = c := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hc.2 hcd]
  have hcomm : ((swap (g a) d * swap (g a) c) * g) a = (g * (swap (g a) d * swap (g a) c)) a :=
    congrArg (fun σ : Perm α => σ a) (Subgroup.mem_centralizer_iff.1 hg _ hk)
  rw [Perm.mul_apply (swap (g a) d * swap (g a) c) g, hkga, Perm.mul_apply g, hka] at hcomm
  exact hc.2 hcomm

theorem centralizer_commutator_sympFour :
    Subgroup.centralizer (commutator sympFour : Set sympFour) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  apply omegaPerm_injective
  rw [map_one]
  have hmem :
      omegaPerm c ∈ Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Perm (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    obtain ⟨x, rfl⟩ := omegaPerm_surjective τ
    have hx : x ∈ commutator sympFour := by
      rw [commutator_sympFour]
      exact hτ
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc x hx]
  rw [centralizer_alternatingGroup_eq_bot (by simp)] at hmem
  exact hmem

theorem isSimpleGroup_commutator_sympFour : IsSimpleGroup (commutator sympFour) :=
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  commutatorEquivAlternating.isSimpleGroup

theorem not_isMulCommutative_commutator_sympFour : ¬ IsMulCommutative (commutator sympFour) := by
  intro hcomm
  have : IsMulCommutative (alternatingGroup (Fin 6)) :=
    ⟨⟨fun x y => commutatorEquivAlternating.symm.injective (by
      rw [map_mul, map_mul]
      exact Std.Commutative.comm _ _)⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 this
  simp at h3

theorem isPerfect_commutator_sympFour : Group.IsPerfect (commutator sympFour) :=
  have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  Group.IsPerfect.ofSurjective (f := commutatorEquivAlternating.symm.toMonoidHom)
    commutatorEquivAlternating.symm.surjective

theorem not_mem_commutator_of_sign {h : sympFour} (hs : sign (omegaPerm h) = -1) :
    h ∉ commutator sympFour := by
  rw [commutator_sympFour, Subgroup.mem_comap, mem_alternatingGroup, hs]
  decide

theorem rootInvolutionA_not_mem : rootInvolutionA ∉ commutator sympFour :=
  not_mem_commutator_of_sign (by rw [omegaPerm_rootInvolutionA, sign_swap (by decide)])

theorem rootInvolutionB_not_mem : rootInvolutionB ∉ commutator sympFour :=
  not_mem_commutator_of_sign (by rw [omegaPerm_rootInvolutionB, sign_swap (by decide)])

theorem rootInvolutionC_not_mem : rootInvolutionC ∉ commutator sympFour :=
  not_mem_commutator_of_sign (by
    rw [omegaPerm_rootInvolutionC, map_mul, map_mul, sign_swap (by decide), sign_swap (by decide),
      sign_swap (by decide)]
    decide)

theorem rootInvolutionD_not_mem : rootInvolutionD ∉ commutator sympFour :=
  not_mem_commutator_of_sign (by
    rw [omegaPerm_rootInvolutionD, map_mul, map_mul, sign_swap (by decide), sign_swap (by decide),
      sign_swap (by decide)]
    decide)

theorem binary_symplectic_four_six_quadratic_forms_and_derived_A6 :
    (∀ (h : sympFour) (k : Fin 6) (v : Fin 4 → ZMod 2),
      quadForm (omegaVec (omegaPerm h k)) v =
        quadForm (omegaVec k) ((((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)) ∧
    Function.Bijective omegaPerm ∧
    commutator sympFour = (alternatingGroup (Fin 6)).comap omegaPerm ∧
    IsSimpleGroup (commutator sympFour) ∧ ¬ IsMulCommutative (commutator sympFour) ∧
    Group.IsPerfect (commutator sympFour) ∧
    Subgroup.centralizer (commutator sympFour : Set sympFour) = ⊥ ∧
    (((rootInvolutionA : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        1 + single 1 2 1 ∧
      ((rootInvolutionB : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        1 + single 2 1 1 ∧
      ((rootInvolutionC : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        1 + single 0 1 1 + single 2 3 1 ∧
      ((rootInvolutionD : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        1 + single 1 0 1 + single 3 2 1) ∧
    omegaPerm rootInvolutionA = swap 2 3 ∧ omegaPerm rootInvolutionB = swap 2 4 ∧
    omegaPerm rootInvolutionC = swap 0 1 * swap 2 4 * swap 3 5 ∧
    omegaPerm rootInvolutionD = swap 0 5 * swap 1 4 * swap 2 3 ∧
    rootInvolutionA ∉ commutator sympFour ∧ rootInvolutionB ∉ commutator sympFour ∧
    rootInvolutionC ∉ commutator sympFour ∧ rootInvolutionD ∉ commutator sympFour ∧
    ¬ Subgroup.closure {rootInvolutionA, rootInvolutionB} ≤ commutator sympFour ∧
    ¬ Subgroup.closure {rootInvolutionC, rootInvolutionD} ≤ commutator sympFour :=
  ⟨quadForm_omegaVec_omegaPerm, ⟨omegaPerm_injective, omegaPerm_surjective⟩,
    commutator_sympFour, isSimpleGroup_commutator_sympFour,
    not_isMulCommutative_commutator_sympFour, isPerfect_commutator_sympFour,
    centralizer_commutator_sympFour, ⟨rfl, rfl, rfl, rfl⟩, omegaPerm_rootInvolutionA,
    omegaPerm_rootInvolutionB, omegaPerm_rootInvolutionC, omegaPerm_rootInvolutionD,
    rootInvolutionA_not_mem, rootInvolutionB_not_mem, rootInvolutionC_not_mem,
    rootInvolutionD_not_mem,
    fun h => rootInvolutionA_not_mem (h (Subgroup.subset_closure (by simp))),
    fun h => rootInvolutionC_not_mem (h (Subgroup.subset_closure (by simp)))⟩

end CFSG.ComponentClassification.PresentationLocal
