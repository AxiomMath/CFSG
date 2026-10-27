module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.L2.FourNormalizer
public import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Inn

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem exists_a4_innAut (hF : L2Field F) (e : K ≃* L2 F) :
    ∃ A V : Subgroup (MulAut K), A ≤ innAut K ∧ Nonempty (↥A ≃* alternatingGroup (Fin 4)) ∧
      Nat.card ↥V = 4 ∧ ∀ x, x ∈ V ↔ x ∈ A ∧ x * x = 1 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF.1
  obtain ⟨H, ⟨eH⟩⟩ := CFSG.Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup h2
  let φ : PSL2 F →* MulAut K := (innAut K).subtype.comp (innAutEquiv e).symm.toMonoidHom
  have hφ : Function.Injective φ := fun x y h =>
    (innAutEquiv e).symm.injective (Subtype.val_injective h)
  have hA : Nonempty (↥(H.map φ) ≃* alternatingGroup (Fin 4)) :=
    ⟨(Subgroup.equivMapOfInjective H φ hφ).symm.trans eH⟩
  obtain ⟨V, hV4, hV⟩ := CFSG.Glauberman.Dickson.MaxCases.exists_kleinFour hA.some
  exact ⟨H.map φ, V, by rintro _ ⟨x, -, rfl⟩; exact ((innAutEquiv e).symm x).2, hA, hV4, hV⟩

theorem exists_conj_fourSubgroups (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e)
    {U₁ U₂ : Subgroup (MulAut K)} (h₁ : U₁ ≤ innAut K) (h₂ : U₂ ≤ innAut K)
    (f₁ : IsFourSubgroup U₁) (f₂ : IsFourSubgroup U₂) :
    ∃ d : MulAut K, U₁.map (MulAut.conj d).toMonoidHom = U₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp₁ : IsPGroup 2 ↥U₁ := IsPGroup.of_card (n := 2) (by rw [f₁.2]; norm_num)
  have hp₂ : IsPGroup 2 ↥U₂ := IsPGroup.of_card (n := 2) (by rw [f₂.2]; norm_num)
  obtain ⟨g₁, -, hg₁⟩ := exists_conj_le_sylow_inf N.T (innAut K) h₁ hp₁
  obtain ⟨g₂, -, hg₂⟩ := exists_conj_le_sylow_inf N.T (innAut K) h₂ hp₂
  have hW₁P : U₁.map (MulAut.conj g₁⁻¹).toMonoidHom ≤ N.P := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g₁⁻¹).toMonoidHom u = g₁⁻¹ * u * g₁ := by simp
    rw [e1]
    exact hg₁ u hu
  have hW₂P : U₂.map (MulAut.conj g₂⁻¹).toMonoidHom ≤ N.P := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g₂⁻¹).toMonoidHom u = g₂⁻¹ * u * g₂ := by simp
    rw [e1]
    exact hg₂ u hu
  obtain ⟨p, -, hp⟩ := ivk_1_3f_a F hF K e N _ _ hW₁P hW₂P (isFourSubgroup_map _ f₁)
    (isFourSubgroup_map _ f₂)
  refine ⟨g₂ * p * g₁⁻¹, ?_⟩
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hmem : (MulAut.conj p) ((MulAut.conj g₁⁻¹) u) ∈ U₂.map (MulAut.conj g₂⁻¹).toMonoidHom := by
      rw [← hp]
      exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨u₂, hu₂, h⟩ := hmem
    have hy : (MulAut.conj (g₂ * p * g₁⁻¹)).toMonoidHom u = u₂ := by
      have h' := congrArg (fun z => g₂ * z * g₂⁻¹) h
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv] at h' ⊢
      calc g₂ * p * g₁⁻¹ * u * (g₁ * (p⁻¹ * g₂⁻¹)) = g₂ * (p * (g₁⁻¹ * u * g₁) * p⁻¹) * g₂⁻¹ := by
            group
        _ = g₂ * (g₂⁻¹ * u₂ * g₂) * g₂⁻¹ := by rw [h']
        _ = u₂ := by group
    rw [hy]
    exact hu₂
  · intro hy
    have hmem : (MulAut.conj g₂⁻¹) y ∈ (U₁.map (MulAut.conj g₁⁻¹).toMonoidHom).map
        (MulAut.conj p).toMonoidHom := by
      rw [hp]
      exact ⟨y, hy, rfl⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := hmem
    refine ⟨u, hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv] at h ⊢
    calc g₂ * p * g₁⁻¹ * u * (g₁ * (p⁻¹ * g₂⁻¹)) = g₂ * (p * (g₁⁻¹ * u * g₁) * p⁻¹) * g₂⁻¹ := by
          group
      _ = g₂ * (g₂⁻¹ * y * g₂) * g₂⁻¹ := by rw [h]
      _ = y := by group

end Inn

theorem ivk_1_3f_c : IVK_1_3f_c := by
  intro F _ _ hF K _ _ e U hUI hU4
  obtain ⟨N⟩ := exists_notation hF e
  obtain ⟨A, V, hAI, hA, hV4, hVmem⟩ := exists_a4_innAut hF e
  have hVA : V ≤ A := fun x hx => ((hVmem x).mp hx).1
  have hVsq : ∀ x ∈ V, x * x = 1 := fun x hx => ((hVmem x).mp hx).2
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hVsq x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hVsq y hy)
    have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hVsq _ (V.mul_mem hx hy))
    calc x * y = (x * y)⁻¹ := hxyi.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxi, hyi]
  have hVI : V ≤ innAut K := hVA.trans hAI
  have hV4' : IsFourSubgroup V := isFourSubgroup_of hVc hVsq hV4
  obtain ⟨d, hd⟩ := exists_conj_fourSubgroups hF e N hVI hUI hV4' hU4
  have hAV : ∀ a ∈ A, ∀ x, x ∈ V ↔ a * x * a⁻¹ ∈ V := by
    intro a ha x
    rw [hVmem, hVmem]
    have hsq : (a * x * a⁻¹) * (a * x * a⁻¹) = a * (x * x) * a⁻¹ := by group
    constructor
    · rintro ⟨hxA, hxx⟩
      exact ⟨A.mul_mem (A.mul_mem ha hxA) (A.inv_mem ha), by rw [hsq, hxx]; group⟩
    · rintro ⟨hxA, hxx⟩
      have h1 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact A.mul_mem (A.mul_mem (A.inv_mem ha) hxA) ha
      · rw [hsq] at hxx
        have : x * x = a⁻¹ * (a * (x * x) * a⁻¹) * a := by group
        rw [this, hxx]
        group
  obtain ⟨eA⟩ := hA
  refine klein_normalizer_a4_or_s4 (U := U) (A := A.map (MulAut.conj d).toMonoidHom) ?_ ?_ hU4.2
    (isFourSubgroup_props hU4).2 ?_ ?_ ⟨(Subgroup.equivMapOfInjective A (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective).symm.trans eA⟩
  · intro u hu
    exact ⟨Subgroup.le_normalizer hu, hUI hu⟩
  · intro n hn u hu
    exact (Subgroup.mem_normalizer_iff.mp hn.1 u).mp hu
  · intro g hg hcomm
    have hg' : g ∈ centralizer (U : Set (MulAut K)) ⊓ innDiagSub e :=
      ⟨Subgroup.mem_centralizer_iff.mpr (fun u hu => (hcomm u hu).symm),
        innAut_le_innDiagSub e hg.2⟩
    rw [centralizer_four_inf_innDiagSub e hF U hUI hU4] at hg'
    exact hg'
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨conj_mem_normalizer d hd hAV a ha, innAut_normal.conj_mem a (hAI ha) d⟩

end CFSG.GH74.GLS.IVK
