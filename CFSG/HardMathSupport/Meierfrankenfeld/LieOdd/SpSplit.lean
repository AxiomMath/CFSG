module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpEichler

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs Module

variable {K : Type} [Field K] {r : ℕ}

@[expose] def SympNondeg (U : Submodule K (Fin r ⊕ Fin r → K)) : Prop :=
  ∀ x ∈ U, (∀ y ∈ U, form x y = 0) → x = 0

@[expose] def eigSub (U : Submodule K (Fin r ⊕ Fin r → K))
    (s : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (ε : K) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  U ⊓ LinearMap.ker (s - ε • LinearMap.id)

theorem mem_eigSub {U : Submodule K (Fin r ⊕ Fin r → K)}
    {s : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)} {ε : K} {x : Fin r ⊕ Fin r → K} :
    x ∈ eigSub U s ε ↔ x ∈ U ∧ s x = ε • x := by
  simp [eigSub, LinearMap.mem_ker, sub_eq_zero]

theorem even_finrank_of_nondeg (U : Submodule K (Fin r ⊕ Fin r → K)) (hU : SympNondeg U) :
    Even (finrank K U) := by
  set B : LinearMap.BilinForm K (Fin r ⊕ Fin r → K) := Matrix.toBilin' (Matrix.J (Fin r) K)
  have hB : ∀ x y, B x y = -form x y := fun x y => toBilin'_J_apply x y
  have halt : (B.restrict U).IsAlt := fun z => by
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    exact isAlt_toBilin'_J (n := r) _
  have hnd : (B.restrict U).Nondegenerate := by
    have hl : ∀ x : U, (∀ y : U, (B.restrict U) x y = 0) → x = 0 := by
      intro x hx
      refine Subtype.ext (hU x x.2 fun y hy => ?_)
      have := hx ⟨y, hy⟩
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hB] at this
      exact neg_eq_zero.1 this
    refine ⟨hl, ?_⟩
    intro y hy
    refine hl y fun x => ?_
    have := hy x
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, hB, form_antisymm]
    rw [hB] at this
    simpa using this
  exact halt.even_finrank hnd

section Split

variable (h2 : (2 : K) ≠ 0) {U : Submodule K (Fin r ⊕ Fin r → K)}
  {s : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)}

include h2 in
theorem half_add_half : (2⁻¹ : K) + 2⁻¹ = 1 := by
  have : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination this

omit h2 in
theorem plus_part (hsU : ∀ u ∈ U, s u ∈ U) (hs2 : ∀ u ∈ U, s (s u) = u) {u : Fin r ⊕ Fin r → K}
    (hu : u ∈ U) : (2⁻¹ : K) • (u + s u) ∈ eigSub U s 1 := by
  rw [mem_eigSub]
  refine ⟨U.smul_mem _ (U.add_mem hu (hsU u hu)), ?_⟩
  rw [map_smul, map_add, hs2 u hu, one_smul, add_comm]

omit h2 in
theorem minus_part (hsU : ∀ u ∈ U, s u ∈ U) (hs2 : ∀ u ∈ U, s (s u) = u)
    {u : Fin r ⊕ Fin r → K} (hu : u ∈ U) : (2⁻¹ : K) • (u - s u) ∈ eigSub U s (-1) := by
  rw [mem_eigSub]
  refine ⟨U.smul_mem _ (U.sub_mem hu (hsU u hu)), ?_⟩
  rw [map_smul, map_sub, hs2 u hu]
  module

include h2 in
theorem plus_add_minus {u : Fin r ⊕ Fin r → K} :
    (2⁻¹ : K) • (u + s u) + (2⁻¹ : K) • (u - s u) = u := by
  calc (2⁻¹ : K) • (u + s u) + (2⁻¹ : K) • (u - s u) = ((2⁻¹ : K) + 2⁻¹) • u := by module
    _ = u := by rw [half_add_half h2, one_smul]

include h2 in
theorem eigSub_orth (hiso : ∀ u ∈ U, ∀ v ∈ U, form (s u) (s v) = form u v)
    {x y : Fin r ⊕ Fin r → K} (hx : x ∈ eigSub U s 1) (hy : y ∈ eigSub U s (-1)) :
    form x y = 0 := by
  rw [mem_eigSub] at hx hy
  have h := hiso x hx.1 y hy.1
  rw [hx.2, hy.2, form_smul_left, form_smul_right] at h
  have : (2 : K) * form x y = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left h2

include h2 in
theorem involution_split (hU : SympNondeg U) (hsU : ∀ u ∈ U, s u ∈ U)
    (hs2 : ∀ u ∈ U, s (s u) = u) (hiso : ∀ u ∈ U, ∀ v ∈ U, form (s u) (s v) = form u v) :
    SympNondeg (eigSub U s 1) ∧ SympNondeg (eigSub U s (-1)) ∧
      finrank K (eigSub U s 1) + finrank K (eigSub U s (-1)) = finrank K U := by
  have horth := fun {x y} (hx : x ∈ eigSub U s 1) (hy : y ∈ eigSub U s (-1)) =>
    eigSub_orth h2 hiso hx hy
  have hdec : ∀ u ∈ U, u = (2⁻¹ : K) • (u + s u) + (2⁻¹ : K) • (u - s u) :=
    fun u _ => (plus_add_minus h2).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hxo
    refine hU x (mem_eigSub.1 hx).1 fun u hu => ?_
    rw [hdec u hu, form_add_right, hxo _ (plus_part hsU hs2 hu), horth hx (minus_part hsU hs2 hu),
      add_zero]
  · intro x hx hxo
    refine hU x (mem_eigSub.1 hx).1 fun u hu => ?_
    rw [hdec u hu, form_add_right, hxo _ (minus_part hsU hs2 hu), add_zero, form_antisymm,
      horth (plus_part hsU hs2 hu) hx, neg_zero]
  · have hsup : eigSub U s 1 ⊔ eigSub U s (-1) = U :=
      le_antisymm (sup_le inf_le_left inf_le_left) (fun u hu => by
        rw [hdec u hu]
        exact Submodule.add_mem_sup (plus_part hsU hs2 hu) (minus_part hsU hs2 hu))
    have hinf : eigSub U s 1 ⊓ eigSub U s (-1) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [Submodule.mem_inf, mem_eigSub, mem_eigSub] at hx
      have e : (2 : K) • x = 0 := by
        have := hx.1.2.symm.trans hx.2.2
        calc (2 : K) • x = x - (-1 : K) • x := by module
          _ = 0 := by rw [one_smul] at this; rw [← this]; module
      exact (Submodule.mem_bot K).2 ((smul_eq_zero.1 e).resolve_left h2)
    have := Submodule.finrank_sup_add_finrank_inf_eq (eigSub U s 1) (eigSub U s (-1))
    rw [hsup, hinf, finrank_bot] at this
    omega

theorem two_le_finrank_of_nondeg (V' : Submodule K (Fin r ⊕ Fin r → K)) (hV : SympNondeg V')
    (hne : V' ≠ ⊥) : 2 ≤ finrank K V' := by
  have h1 : 0 < finrank K V' := Submodule.one_le_finrank_iff.2 hne
  obtain ⟨k, hk⟩ := even_finrank_of_nondeg V' hV
  omega

include h2 in
theorem involution_plane (hU : SympNondeg U) (hdim : finrank K U = 2) (hsU : ∀ u ∈ U, s u ∈ U)
    (hs2 : ∀ u ∈ U, s (s u) = u) (hiso : ∀ u ∈ U, ∀ v ∈ U, form (s u) (s v) = form u v) :
    (∀ u ∈ U, s u = u) ∨ (∀ u ∈ U, s u = -u) := by
  obtain ⟨hp, hm, hsum⟩ := involution_split h2 hU hsU hs2 hiso
  have h2i : (2⁻¹ : K) ≠ 0 := inv_ne_zero h2
  by_cases hP : eigSub U s 1 = ⊥
  · right
    intro u hu
    have h0 : (2⁻¹ : K) • (u + s u) = 0 := by
      have := plus_part hsU hs2 hu
      rw [hP] at this
      exact (Submodule.mem_bot K).1 this
    exact eq_neg_of_add_eq_zero_right ((smul_eq_zero.1 h0).resolve_left h2i)
  · left
    intro u hu
    have hge := two_le_finrank_of_nondeg _ hp hP
    have hz : finrank K (eigSub U s (-1)) = 0 := by omega
    have hM : eigSub U s (-1) = ⊥ := Submodule.finrank_eq_zero.1 hz
    have h0 : (2⁻¹ : K) • (u - s u) = 0 := by
      have := minus_part hsU hs2 hu
      rw [hM] at this
      exact (Submodule.mem_bot K).1 this
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left h2i)).symm

end Split

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
