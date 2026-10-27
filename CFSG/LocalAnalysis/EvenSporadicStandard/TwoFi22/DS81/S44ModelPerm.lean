module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelCd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrbAct
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ModelCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.CocodeFacts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.FrameCd

open Subgroup CFSG.Sporadic.Fi23 FrameJ Gen CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Frame


theorem fjQ_zero : fjQ 0 = dCd := Subtype.ext fjPt_zero

theorem fjQ_injective : Function.Injective fjQ := fun _ _ h =>
  fjPt_injective (congrArg Subtype.val h)

theorem fjQ_mem : ∀ i : Fin 23, fjQ i ∈ E0 := fun i =>
  Subgroup.mem_subgroupOf.2 ⟨eVec i, fjHom_eVec i⟩

theorem evC_singleton (a : Fin 23) : evC {a} = fjQ a := Subtype.ext (ev_singleton a)

theorem evC_insert {a : Fin 23} {s : Finset (Fin 23)} (h : a ∉ s) :
    evC (insert a s) = fjQ a * evC s :=
  Subtype.ext (ev_insert h)

theorem evC_mem_closure (s : Finset (Fin 23)) :
    evC s ∈ Subgroup.closure (Set.range fjQ) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [evC_empty]
    exact one_mem _
  | insert a s ha ih =>
    rw [evC_insert ha]
    exact mul_mem (subset_closure ⟨a, rfl⟩) ih

theorem closure_range_fjQ : Subgroup.closure (Set.range (fjQ : Fin 23 → Cd)) = E0 := by
  refine le_antisymm ((closure_le _).2 ?_) fun y hy => ?_
  · rintro _ ⟨i, rfl⟩
    exact fjQ_mem i
  · obtain ⟨s, -, rfl⟩ := exists_evC hy
    exact evC_mem_closure s

theorem exists_ind (w : Word) : ∃ s : Finset (Fin 23), ind s = w := by
  refine ⟨Finset.univ.filter fun i => w i = 1, ?_⟩
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

theorem ind_mem_golayCode_iff (s : Finset (Fin 23)) : ind s ∈ golayCode ↔ evC s = 1 := by
  rw [← fjHom_eq_one_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [evC_val, OneMemClass.coe_one]
    exact h
  · intro h
    have := congrArg Subtype.val h
    rw [evC_val, OneMemClass.coe_one] at this
    exact this

theorem mem_permStab_of_evC {π : Equiv.Perm (Fin 23)}
    (h : ∀ s : Finset (Fin 23), evC (s.image π) = 1 ↔ evC s = 1) :
    π ∈ permStab golayCode := by
  intro w
  obtain ⟨s, rfl⟩ := exists_ind w
  rw [permLin_ind, ind_mem_golayCode_iff, ind_mem_golayCode_iff]
  exact h s

theorem isPerm_one : IsPerm (1 : Cd) 1 := fun i => by simp

theorem isPerm_mul {n m : Cd} {σ τ : Equiv.Perm (Fin 23)} (hn : IsPerm n σ) (hm : IsPerm m τ) :
    IsPerm (n * m) (σ * τ) := by
  intro i
  have h : ((n * m : Cd) : J) * fjPt i * ((n * m : Cd) : J)⁻¹ =
      (n : J) * ((m : J) * fjPt i * (m : J)⁻¹) * (n : J)⁻¹ := by
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]
  rw [h, hm i, hn (τ i)]
  rfl

theorem isPerm_unique {n : Cd} {σ τ : Equiv.Perm (Fin 23)} (h₁ : IsPerm n σ) (h₂ : IsPerm n τ) :
    σ = τ :=
  Equiv.ext fun i => fjPt_injective ((h₁ i).symm.trans (h₂ i))

theorem conj_eq_of_isPerm_one {n : Cd} (hn : IsPerm n 1) {e : Cd} (he : e ∈ E0) :
    n * e * n⁻¹ = e := by
  obtain ⟨s, -, rfl⟩ := exists_evC he
  rw [hn.conj_evC]
  simp

theorem isPerm_mem_permStab {n : Cd} {σ : Equiv.Perm (Fin 23)} (hn : IsPerm n σ) :
    σ ∈ permStab golayCode := by
  refine mem_permStab_of_evC fun s => ?_
  rw [← hn.conj_evC, conj_eq_one_iff]

end Frame

section Perm



@[expose] noncomputable def permOf (n : normalizer (E0 : Set ↥Cd)) : Equiv.Perm (Fin 23) :=
  Classical.choose (exists_perm n.2)

theorem isPerm_permOf (n : normalizer (E0 : Set ↥Cd)) : IsPerm (n : ↥Cd) (permOf n) :=
  Classical.choose_spec (exists_perm n.2)

@[expose] noncomputable def permHom : normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23) where
  toFun := permOf
  map_one' := isPerm_unique (isPerm_permOf 1) isPerm_one
  map_mul' n m := isPerm_unique (isPerm_permOf (n * m))
    (isPerm_mul (isPerm_permOf n) (isPerm_permOf m))

theorem mem_E0_of_permHom_eq_one (R : Fi22CoverRest) {n : normalizer (E0 : Set ↥Cd)}
    (hn : permHom n = 1) : (n : ↥Cd) ∈ E0 := by
  have hp : IsPerm (n : ↥Cd) 1 := by
    have := isPerm_permOf n
    rwa [show permOf n = 1 from hn] at this
  obtain ⟨x, hx, hxn⟩ := R.aut_cent (MulAut.conj (G := ↥Cd) n.1)
    (fun e he => by rw [MulAut.conj_apply]; exact conj_eq_of_isPerm_one hp he)
  have hcen : x⁻¹ * (n : ↥Cd) ∈ Subgroup.center ↥Cd := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (n : ↥Cd) * g * (n : ↥Cd)⁻¹ = x * g * x⁻¹ := by
      have := congrArg (fun f : MulAut ↥Cd => f g) hxn
      simpa only [MulAut.conj_apply] using this
    calc g * (x⁻¹ * (n : ↥Cd)) = x⁻¹ * (x * g * x⁻¹) * (n : ↥Cd) := by group
      _ = x⁻¹ * ((n : ↥Cd) * g * (n : ↥Cd)⁻¹) * (n : ↥Cd) := by rw [h1]
      _ = x⁻¹ * (n : ↥Cd) * g := by group
  have hn' : (n : ↥Cd) = x * (x⁻¹ * (n : ↥Cd)) := by group
  rw [hn']
  exact mul_mem hx (E0_center_le hcen)

theorem card_ker_permHom_le (R : Fi22CoverRest) : Nat.card permHom.ker ≤ 2 ^ 11 := by
  rw [← R.card_E]
  refine Nat.card_le_card_of_injective
    (fun k => (⟨(k.1 : ↥Cd), mem_E0_of_permHom_eq_one R (MonoidHom.mem_ker.1 k.2)⟩ : E0)) ?_
  intro k k' h
  have h' : (k.1 : ↥Cd) = (k'.1 : ↥Cd) := congrArg (fun x : E0 => (x : ↥Cd)) h
  exact Subtype.ext (Subtype.ext h')

end Perm

section Range



theorem card_range_permHom_ge (R : Fi22CoverRest) : 443520 ≤ Nat.card permHom.range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup permHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange permHom).toEquiv,
    E0_card_normalizer] at h1
  have h3 : 443520 * 2 ^ 11 ≤ Nat.card permHom.range * 2 ^ 11 :=
    calc 443520 * 2 ^ 11 = 2 ^ 11 * 443520 := mul_comm _ _
      _ = Nat.card permHom.range * Nat.card permHom.ker := h1
      _ ≤ Nat.card permHom.range * 2 ^ 11 := Nat.mul_le_mul_left _ (card_ker_permHom_le R)
  exact Nat.le_of_mul_le_mul_right h3 (by norm_num)

theorem range_permHom_eq (R : Fi22CoverRest)
    (hAut : Nat.card ↥(permStab golayCode ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23)) ≤ 443520) :
    permHom.range =
      permStab golayCode ⊓ MulAction.stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (hAut.trans (card_range_permHom_ge R))
  rintro _ ⟨n, rfl⟩
  refine Subgroup.mem_inf.2 ⟨isPerm_mem_permStab (isPerm_permOf n), ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  exact (isPerm_permOf n).zero

end Range

end CFSG.EvenSporadicStandard.TwoFi22.DS81.FrameCd
