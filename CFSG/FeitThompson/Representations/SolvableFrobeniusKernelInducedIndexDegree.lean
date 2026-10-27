module

public import CFSG.FeitThompson.Representations.FrobeniusKernelInductionIrreducible
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open SemidirectProduct
open scoped Pointwise

section Transport

variable {M L : Type*} [Group M] [Group L]

theorem card_eq_of_forall_mem_iff (e : M ≃* L) {K : Subgroup M} {K' : Subgroup L}
    (hK : ∀ z : M, z ∈ K ↔ e z ∈ K') : Nat.card K' = Nat.card K := by
  refine Nat.card_congr (Equiv.ofBijective (fun x : K => (⟨e x, (hK x).1 x.2⟩ : K')) ?_).symm
  refine ⟨fun x y hxy => Subtype.ext (e.injective (Subtype.ext_iff.1 hxy)), fun y => ?_⟩
  exact ⟨⟨e.symm y, (hK _).2 (by simp)⟩, Subtype.ext (by simp)⟩

theorem mem_Irr_of_comp_mulEquiv (e : M ≃* L) {χ : L → ℂ} (h : χ ∘ e ∈ Irr M) : χ ∈ Irr L := by
  rw [← normalInduction_irrChars_eq_Irr] at h ⊢
  have h2 := NormalInduction.mem_irrChars_comp_mulEquiv h e.symm
  have hid : (χ ∘ (e : M → L)) ∘ (e.symm : L → M) = χ := by funext x; simp
  rwa [hid] at h2

variable [Fintype M] [Fintype L]

theorem indClassFun_comp_mulEquiv (e : M ≃* L) {K : Subgroup M} {K' : Subgroup L}
    (hK : ∀ z : M, z ∈ K ↔ e z ∈ K') {θ : K → ℂ} {θ' : K' → ℂ}
    (hθ : ∀ (x : K) (y : K'), (y : L) = e x → θ' y = θ x) :
    indClassFun K' θ' ∘ e = indClassFun K θ := by
  classical
  funext z
  rw [Function.comp_apply, indClassFun_apply, indClassFun_apply, card_eq_of_forall_mem_iff e hK]
  congr 1
  refine (Fintype.sum_bijective e e.bijective _ _ fun t => ?_).symm
  have he : e (t⁻¹ * z * t) = (e t)⁻¹ * e z * e t := by simp
  by_cases h : t⁻¹ * z * t ∈ K
  · have hmem : (e t)⁻¹ * e z * e t ∈ K' := by rw [← he]; exact (hK _).1 h
    rw [dif_pos h, dif_pos hmem]
    exact (hθ ⟨t⁻¹ * z * t, h⟩ ⟨_, hmem⟩ he.symm).symm
  · rw [dif_neg h, dif_neg (fun hc => h ((hK _).2 (by rw [he]; exact hc)))]

end Transport

variable {L : Type*} [Group L] {H E : Subgroup L}

noncomputable def frobeniusConjAut (H E : Subgroup L) [H.Normal] : E →* MulAut H :=
  H.normalizerMonoidHom.comp (Subgroup.inclusion (by rw [H.normalizer_eq_top]; exact le_top))

@[simp] theorem coe_frobeniusConjAut_apply [H.Normal] (u : E) (x : H) :
    ((frobeniusConjAut H E u x : H) : L) = (u : L) * (x : L) * (u : L)⁻¹ := by
  simp [frobeniusConjAut]

theorem fixedPointFree_frobeniusConjAut [H.Normal] {u : E}
    (hu : H ⊓ Subgroup.centralizer {(u : L)} = ⊥) :
    MonoidHom.FixedPointFree (frobeniusConjAut H E u : H → H) := by
  intro x hx
  have hx' : (u : L) * (x : L) * (u : L)⁻¹ = (x : L) := by
    rw [← coe_frobeniusConjAut_apply (E := E) u x, hx]
  have hmem : (x : L) ∈ H ⊓ Subgroup.centralizer ({(u : L)} : Set L) :=
    Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc (x : L) * (u : L) = ((u : L) * (x : L) * (u : L)⁻¹) * (u : L) := by rw [hx']
        _ = (u : L) * (x : L) := by group)⟩
  rw [hu, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem isComplement'_of_mul_eq_univ_of_inf_eq_bot
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥) : H.IsComplement' E :=
  Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hinf) hmul

noncomputable def frobeniusMulEquiv [H.Normal] (hHE : H.IsComplement' E) :
    (H ⋊[frobeniusConjAut H E] E) ≃* L :=
  SemidirectProduct.mulEquivSubgroup hHE

theorem frobeniusMulEquiv_apply [H.Normal] (hHE : H.IsComplement' E)
    (x : H ⋊[frobeniusConjAut H E] E) :
    frobeniusMulEquiv hHE x = ((x.left : L) * (x.right : L)) :=
  SemidirectProduct.mulEquivSubgroup_apply hHE x

theorem mem_range_inl_iff_of_isComplement' [H.Normal] (hHE : H.IsComplement' E)
    (z : H ⋊[frobeniusConjAut H E] E) :
    z ∈ (inl : H →* H ⋊[frobeniusConjAut H E] E).range ↔ frobeniusMulEquiv hHE z ∈ H := by
  rw [frobeniusMulEquiv_apply, range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_eq_right]
  constructor
  · intro h
    have hz : (z.right : L) = 1 := by rw [h]; simp
    rw [hz, mul_one]
    exact z.left.2
  · intro h
    have hr : (z.right : L) ∈ H := by
      have h2 : (z.left : L)⁻¹ * ((z.left : L) * (z.right : L)) ∈ H :=
        H.mul_mem (H.inv_mem z.left.2) h
      simpa [← mul_assoc] using h2
    have hmem : (z.right : L) ∈ H ⊓ E := Subgroup.mem_inf.2 ⟨hr, z.right.2⟩
    rw [hHE.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem

theorem indClassFun_comp_frobeniusMulEquiv [Fintype L] [H.Normal] [Fintype H] [Fintype E]
    (hHE : H.IsComplement' E) (θ : H → ℂ) :
    indClassFun H θ ∘ (frobeniusMulEquiv hHE)
      = indClassFun (inl : H →* H ⋊[frobeniusConjAut H E] E).range
          (kernelClassFun (frobeniusConjAut H E) θ) := by
  refine indClassFun_comp_mulEquiv _ (mem_range_inl_iff_of_isComplement' hHE) ?_
  intro x y hxy
  obtain ⟨w, hw⟩ := x.2
  have hleft : (x : H ⋊[frobeniusConjAut H E] E).left = w := by rw [← hw]; simp
  have hright : (x : H ⋊[frobeniusConjAut H E] E).right = 1 := by rw [← hw]; simp
  rw [kernelClassFun_apply, hleft]
  congr 1
  refine Subtype.ext ?_
  rw [hxy, frobeniusMulEquiv_apply, hleft, hright]
  simp

theorem indClassFun_one_eq_card [Fintype L] (hHE : H.IsComplement' E) {θ : H → ℂ}
    (hθ1 : θ 1 = 1) : indClassFun H θ 1 = (Nat.card E : ℂ) := by
  rw [indClassFun_one, hθ1, mul_one]
  have hcard : Nat.card H * Nat.card E = Nat.card L := hHE.card_mul_card
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [← hcard]
  push_cast
  field_simp

theorem index_eq_card_of_isComplement' (hHE : H.IsComplement' E) : H.index = Nat.card E :=
  hHE.symm.index_eq_card

theorem exists_mem_Irr_indClassFun_mem_Irr [Fintype L] [H.Normal] [Group.IsSolvable H]
    (hH : H ≠ ⊥) (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    ∃ θ ∈ Irr H, θ ≠ 1 ∧ θ 1 = 1 ∧
      indClassFun H θ ∈ Irr L ∧ indClassFun H θ 1 = (Nat.card E : ℂ) := by
  have _ : Nontrivial H := H.nontrivial_iff_ne_bot.2 hH
  have _ : Fintype H := Fintype.ofFinite _
  have _ : Fintype E := Fintype.ofFinite _
  have hHE : H.IsComplement' E := isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf
  obtain ⟨θ, hθ, hθ1, hθne⟩ := exists_mem_Irr_apply_one_eq_one_and_ne_one H
  refine ⟨θ, hθ, hθne, hθ1, ?_, indClassFun_one_eq_card hHE hθ1⟩
  refine mem_Irr_of_comp_mulEquiv (frobeniusMulEquiv hHE) ?_
  rw [indClassFun_comp_frobeniusMulEquiv hHE θ]
  exact indClassFun_kernelClassFun_mem_Irr
    (fun v hv => fixedPointFree_frobeniusConjAut
      (hC (v : L) v.2 (fun h => hv (Subtype.ext h)))) hθ hθne

theorem exists_mem_Irr_indClassFun_mem_Irr_index [Fintype L] [H.Normal] [Group.IsSolvable H]
    (hH : H ≠ ⊥) (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    ∃ θ ∈ Irr H, θ ≠ 1 ∧ θ 1 = 1 ∧
      indClassFun H θ ∈ Irr L ∧ indClassFun H θ 1 = (H.index : ℂ) := by
  obtain ⟨θ, hθ, hθne, hθ1, hirr, hdeg⟩ :=
    exists_mem_Irr_indClassFun_mem_Irr (E := E) hH hmul hinf hC
  refine ⟨θ, hθ, hθne, hθ1, hirr, ?_⟩
  rw [hdeg, index_eq_card_of_isComplement'
    (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]

end CFSG.FeitThompson
