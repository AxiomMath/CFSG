module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenFrame

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

theorem ofAdd_mem_closure_eVec (w : Word) :
    Multiplicative.ofAdd w ∈ Subgroup.closure (Set.range eVec) := by
  have hw : w = ind (Finset.univ.filter fun i => w i = 1) := by
    funext i
    rw [ind_apply]
    by_cases h : w i = 1
    · simp [h]
    · have : w i = 0 := by
        revert h
        generalize w i = a
        revert a
        decide
      simp [this]
  rw [hw, ind_eq_sum, ofAdd_sum]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨i, rfl⟩

section Frame


theorem fjPt_injective : Function.Injective fjPt := fun i j h => by
  by_contra hne
  exact fjPt_ne hne h

@[expose] noncomputable def ev (s : Finset (Fin 23)) : J :=
  fjHom (Multiplicative.ofAdd (ind s))

@[expose] noncomputable def evC (s : Finset (Fin 23)) : Cd := ⟨ev s, fjHom_mem_Cd _⟩

theorem evC_val (s : Finset (Fin 23)) : (evC s : J) = ev s := rfl

theorem ev_empty : ev ∅ = 1 := by
  rw [ev, ind_empty, ofAdd_zero, map_one]

theorem evC_empty : evC ∅ = 1 := Subtype.ext ev_empty

theorem ev_singleton (a : Fin 23) : ev {a} = fjPt a := by
  rw [ev, ind_singleton]
  exact fjHom_eVec a

theorem ev_insert {a : Fin 23} {s : Finset (Fin 23)} (h : a ∉ s) :
    ev (insert a s) = fjPt a * ev s := by
  rw [ev, ev, ind_eq_sum, ind_eq_sum, Finset.sum_insert h, ofAdd_add, map_mul]
  exact congrArg (· * _) (fjHom_eVec a)

theorem evC_mem (s : Finset (Fin 23)) : evC s ∈ E0 :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩

@[expose] def permW (σ : Equiv.Perm (Fin 23)) : Multiplicative Word →* Multiplicative Word where
  toFun w := Multiplicative.ofAdd fun i => Multiplicative.toAdd w (σ.symm i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem permW_eVec (σ : Equiv.Perm (Fin 23)) (i : Fin 23) : permW σ (eVec i) = eVec (σ i) := by
  show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  funext j
  simp only [eVec, toAdd_ofAdd, Pi.single_apply, Equiv.symm_apply_eq]

theorem permW_ind (σ : Equiv.Perm (Fin 23)) (s : Finset (Fin 23)) :
    permW σ (Multiplicative.ofAdd (ind s)) = Multiplicative.ofAdd (ind (s.image σ)) := by
  show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  funext i
  have : σ.symm i ∈ s ↔ i ∈ s.image σ := by
    rw [Finset.mem_image]
    constructor
    · intro h
      exact ⟨_, h, σ.apply_symm_apply i⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  simp only [toAdd_ofAdd, ind_apply, this]

theorem conj_fjHom {n : J} {σ : Equiv.Perm (Fin 23)} (h : ∀ i, n * fjPt i * n⁻¹ = fjPt (σ i))
    (w : Multiplicative Word) : n * fjHom w * n⁻¹ = fjHom (permW σ w) := by
  have key : (MulAut.conj n).toMonoidHom.comp fjHom = fjHom.comp (permW σ) := by
    refine MonoidHom.ext fun w => ?_
    have hw : w ∈ Subgroup.closure (Set.range eVec) := by
      have := ofAdd_mem_closure_eVec (Multiplicative.toAdd w)
      rwa [ofAdd_toAdd] at this
    refine MonoidHom.eqOn_closure ?_ hw
    rintro _ ⟨i, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, fjHom_eVec,
      permW_eVec]
    exact h i
  have := congrArg (fun f : Multiplicative Word →* J => f w) key
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem conj_ev {n : J} {σ : Equiv.Perm (Fin 23)} (h : ∀ i, n * fjPt i * n⁻¹ = fjPt (σ i))
    (s : Finset (Fin 23)) : n * ev s * n⁻¹ = ev (s.image σ) := by
  rw [ev, ev, conj_fjHom h, permW_ind]

theorem evC_inj {s t : Finset (Fin 23)} (hs : s.card ≤ 3) (ht : t.card ≤ 3)
    (h : evC s = evC t) : s = t := by
  have h' : ev s = ev t := by
    have := congrArg (fun x : Cd => (x : J)) h
    simpa only [evC_val] using this
  have h1 : fjHom (Multiplicative.ofAdd (ind s - ind t)) = 1 := by
    rw [ofAdd_sub, map_div, div_eq_one]
    exact h'
  have h2 := (fjHom_eq_one_iff _).1 h1
  rw [word_sub_eq_add] at h2
  exact eq_of_ind_add_mem hs ht h2

theorem exists_evC {y : Cd} (hy : y ∈ E0) : ∃ s : Finset (Fin 23), s.card ≤ 3 ∧ evC s = y := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hy)
  obtain ⟨s, hs, hsw⟩ := exists_card_le_three (coMk (Multiplicative.toAdd w))
  refine ⟨s, hs, Subtype.ext ?_⟩
  have hmem : ind s - Multiplicative.toAdd w ∈ golayCode := coMk_eq_coMk.1 hsw
  have h1 := (fjHom_eq_one_iff _).2 hmem
  rw [ofAdd_sub, map_div, div_eq_one, ofAdd_toAdd] at h1
  exact h1.trans hw

theorem evC_eq_one {s : Finset (Fin 23)} (hs : s.card ≤ 3) (h : evC s = 1) : s = ∅ :=
  evC_inj hs (by simp) (h.trans evC_empty.symm)

@[expose] def IsPerm (c : Cd) (σ : Equiv.Perm (Fin 23)) : Prop :=
  ∀ i, (c : J) * fjPt i * (c : J)⁻¹ = fjPt (σ i)

theorem IsPerm.zero {c : Cd} {σ : Equiv.Perm (Fin 23)} (h : IsPerm c σ) : σ 0 = 0 := by
  apply fjPt_injective
  rw [← h 0, fjPt_zero, mem_Cd.1 c.2, mul_inv_cancel_right]

theorem IsPerm.conj_evC {c : Cd} {σ : Equiv.Perm (Fin 23)} (h : IsPerm c σ)
    (s : Finset (Fin 23)) : c * evC s * c⁻¹ = evC (s.image σ) :=
  Subtype.ext (conj_ev h s)

theorem IsPerm.card_image {c : Cd} {σ : Equiv.Perm (Fin 23)} (_h : IsPerm c σ)
    (s : Finset (Fin 23)) : (s.image σ).card = s.card :=
  Finset.card_image_of_injective _ σ.injective

theorem IsPerm.zero_mem_image {c : Cd} {σ : Equiv.Perm (Fin 23)} (h : IsPerm c σ)
    (s : Finset (Fin 23)) : (0 : Fin 23) ∈ s.image σ ↔ (0 : Fin 23) ∈ s := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, haσ⟩
    have : a = 0 := σ.injective (haσ.trans h.zero.symm)
    exact this ▸ ha
  · intro h0
    exact ⟨0, h0, h.zero⟩

end Frame

section Normalizer



theorem conj_fjPt_mem {n : Cd} (hn : n ∈ normalizer (E0 : Set Cd)) (i : Fin 23) :
    ∃ j : Fin 23, (n : J) * fjPt i * (n : J)⁻¹ = fjPt j := by
  by_cases hi : i = 0
  · subst hi
    exact ⟨0, by rw [fjPt_zero, mem_Cd.1 n.2, mul_inv_cancel_right]⟩
  · have hmem : fjQ i ∈ E0 := Subgroup.mem_subgroupOf.2 (fjPt_mem_range i)
    have h1 := (Subgroup.mem_normalizer_iff.1 hn _).1 hmem
    rw [E0, Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hstar : (n : J) * fjPt i * (n : J)⁻¹ ∈ star := conj_mem_star n.2 (fjPt_star hi)
    obtain ⟨j, -, hj⟩ := star_mem_range hstar h1
    exact ⟨j, hj.symm⟩

theorem exists_perm {n : Cd} (hn : n ∈ normalizer (E0 : Set Cd)) :
    ∃ σ : Equiv.Perm (Fin 23), IsPerm n σ := by
  choose f hf using conj_fjPt_mem hn
  have hinj : Function.Injective f := by
    intro i j hij
    apply fjPt_injective
    have h : (n : J) * fjPt i * (n : J)⁻¹ = (n : J) * fjPt j * (n : J)⁻¹ := by
      rw [hf, hf, hij]
    exact mul_left_cancel (mul_right_cancel h)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => hf i⟩

end Normalizer

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
