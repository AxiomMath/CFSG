module

public import CFSG.LargeExtraspecial.AS35YFOm4
public import CFSG.LargeExtraspecial.AS35YFSym
public import CFSG.LargeExtraspecial.S12InspFamOMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap Matrix Equiv Equiv.Perm CFSG.ClassicalGroups.Orthogonal

namespace AS35YF

theorem exists_perm_five_of_orth_two {X : Type} [Group X] {D : Set X}
    (hgen : Subgroup.closure D = ⊤)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : CFSG.Open.fischerLinearModel D
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) :
    ∃ ψ : X ≃* Perm (Fin 5), ∀ x, x ∈ D ↔ (ψ x).IsSwap := by
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_fin_of_ncard_eq Q
    S12Insp5.quadMinusFour hnd S12Insp5.quadMinusFour_nondeg
    ((S12Insp5.ncard_eq_ten_of_minus hnd hmin).trans S12Insp5.ncard_quadMinusFour.symm)
  have hLq : ∀ v, Q v = qm4 (L v) := fun v => by
    rw [← hL, S12Insp5.quadMinusFour_apply]
    rfl
  have hLb : ∀ x y, polar Q x y = bm4 (L x) (L y) := fun x y => by
    rw [show bm4 (L x) (L y) = S12Insp5.b4 (L x) (L y) from rfl,
      ← S12Insp5.polar_quadMinusFour, polar, polar, ← map_add, hL, hL, hL]
  let Φ₁ : Perm (Fin 5) →* ((Fin (2 * 2) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 2) → ZMod 2)) :=
    (MulAut.conj L.symm).toMonoidHom.comp act5Hom
  let Φ : Perm (Fin 5) →* GL (Fin (2 * 2)) (ZMod 2) :=
    (toLinEquiv (Fin (2 * 2)) (ZMod 2)).symm.toMonoidHom.comp Φ₁
  have hΦ : ∀ σ x, ((Φ σ : GL (Fin (2 * 2)) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ x =
      L.symm (act5 σ (L x)) := fun σ x => by
    rw [← toLinEquiv_apply]
    change toLinEquiv _ _ ((toLinEquiv _ _).symm (Φ₁ σ)) x = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hΦH : ∀ σ, Φ σ ∈ CFSG.Open.fischerMatrixGroup
      fun A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) (ZMod 2) => ∀ x, Q (A *ᵥ x) = Q x :=
    fun σ => subset_closure (show ∀ x, Q ((Φ σ : Matrix _ _ (ZMod 2)) *ᵥ x) = Q x from
      fun x => by rw [hΦ, hLq, hLq x, LinearEquiv.apply_symm_apply, qm4_act5])
  let Ψ := Φ.codRestrict _ hΦH
  have hswap : ∀ i j : Fin 5, i ≠ j → ∀ x,
      ((Φ (swap i j) : GL (Fin (2 * 2)) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ x =
        x + polar Q x (L.symm (vv i j)) • L.symm (vv i j) := fun i j hij x => by
    rw [hΦ, act5_swap i j hij, map_add, map_smul, LinearEquiv.symm_apply_apply, hLb,
      LinearEquiv.apply_symm_apply]
  have hT : ∀ i j : Fin 5, i ≠ j → (Φ (swap i j) : GL (Fin (2 * 2)) (ZMod 2)) ∈
      CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1 := fun i j hij =>
    ⟨L.symm (vv i j), show Q (L.symm (vv i j)) = 1 by
      rw [hLq, LinearEquiv.apply_symm_apply]; exact qm4_vv i j hij, hswap i j hij⟩
  have hTsw : ∀ g : GL (Fin (2 * 2)) (ZMod 2),
      g ∈ CFSG.Open.fischerTransvections (polar Q) (fun v => Q v = 1) →
      ∃ i j : Fin 5, i ≠ j ∧ g = Φ (swap i j) := by
    rintro g ⟨v, hv, hgv⟩
    obtain ⟨i, j, hij, hvij⟩ := exists_eq_vv (L v) (by rw [← hLq]; exact hv)
    refine ⟨i, j, hij, (toLinEquiv (Fin (2 * 2)) (ZMod 2)).injective ?_⟩
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, toLinEquiv_apply, hgv, hswap i j hij, ← hvij,
      LinearEquiv.symm_apply_apply]
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    rw [Subgroup.mem_bot]
    have h0 : (Φ σ : GL (Fin (2 * 2)) (ZMod 2)) = 1 := congrArg Subtype.val hσ
    have h1 : ∀ y, act5 σ y = y := fun y => by
      have h2 := hΦ σ (L.symm y)
      rw [h0, Units.val_one, one_mulVec, LinearEquiv.apply_symm_apply] at h2
      exact (L.symm.injective h2).symm
    exact eq_one_of_act5 σ (h1 _) (h1 _) (h1 _) (h1 _)
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    have hcl : Subgroup.closure (φ.toMonoidHom '' D) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ φ.surjective]
    rw [← hcl, closure_le]
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨i, j, hij, hd'⟩ := hTsw _ ((hφ d).1 hd)
    exact MonoidHom.mem_range.mpr ⟨swap i j, Subtype.ext hd'.symm⟩
  let e := MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨φ.trans e.symm, fun x => ?_⟩
  rw [hφ x, MulEquiv.trans_apply]
  constructor
  · intro hx
    obtain ⟨i, j, hij, hxij⟩ := hTsw _ hx
    have hx' : φ x = e (swap i j) := Subtype.ext hxij
    rw [hx', MulEquiv.symm_apply_apply]
    exact ⟨i, j, hij, rfl⟩
  · rintro ⟨i, j, hij, hσ⟩
    have hx' : φ x = e (swap i j) := by rw [← hσ, MulEquiv.apply_symm_apply]
    rw [hx']
    exact hT i j hij

end AS35YF

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem asc_closure_Ehat : Subgroup.closure S.EhatAsc = ⊤ := by
  rw [← MonoidHom.map_closure, closure_closure_coe_preimage,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_orth_two (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : CFSG.Open.fischerLinearModel S.EhatAsc
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (polar Q) fun v => Q v = 1)) : False := by
  obtain ⟨ψ, hψ⟩ := AS35YF.exists_perm_five_of_orth_two asc_closure_Ehat hnd hmin hmod
  exact asc_false_of_perm_five hst hP hS htD htM ψ hψ

end Setting

end CFSG.LargeExtraspecial
