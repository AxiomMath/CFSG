module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.GroupTheory.FixedPointFreeQuotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open CFSG.RankThree.OrthogonalInvolutions Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem apply_eq_self_of_mem_commSpace_of_conj_eq_inv {ρ β : V ≃ₗ[ZMod 2] V}
    (hρ : ∀ v, q (ρ v) = q v) (hodd : Odd (orderOf ρ))
    (hinv : β * ρ * β⁻¹ = ρ⁻¹) {c : V} (hc : ρ c = c)
    (hβ : ∀ v, QuadraticMap.polar q v c = 0 → β v - v ∈ (ZMod 2) ∙ c) :
    ∀ w ∈ commSpace ρ, β w = w := by
  have hpolar : ∀ x y : V, QuadraticMap.polar q (ρ x) (ρ y) = QuadraticMap.polar q x y := by
    intro x y
    simp only [QuadraticMap.polar, ← map_add, hρ]
  have hWperp : ∀ w ∈ commSpace ρ, QuadraticMap.polar q w c = 0 := by
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    have hp : QuadraticMap.polar q (ρ v) c = QuadraticMap.polar q v c := by
      have h := hpolar v c
      rwa [hc] at h
    rw [QuadraticMap.polar_sub_left, hp, sub_self]
  have hβW : ∀ w ∈ commSpace ρ, β w ∈ commSpace ρ := by
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    have hβρ : β (ρ v) = ρ⁻¹ (β v) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e (β v)) hinv
      simpa [LinearEquiv.mul_apply] using h
    rw [map_sub, hβρ]
    have hmem : ρ⁻¹ (β v) - β v ∈ commSpace ρ⁻¹ := sub_mem_commSpace _ _
    rwa [AS35QCo.commSpace_inv] at hmem
  intro w hw
  have hspan : (ZMod 2) ∙ c ≤ fixSpace ρ :=
    (Submodule.span_singleton_le_iff_mem c (fixSpace ρ)).mpr (mem_fixSpace.mpr hc)
  have hmem : β w - w ∈ commSpace ρ ⊓ fixSpace ρ := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (hβW w hw) hw
    · exact hspan (hβ w (hWperp w hw))
  have hbot : commSpace ρ ⊓ fixSpace ρ = ⊥ := by
    rw [inf_comm]
    exact AS35QCo.fixSpace_inf_commSpace hodd (pow_orderOf_eq_one ρ)
  rw [hbot, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

theorem eq_one_of_conj_eq_inv_of_apply_eq {ρ β : V ≃ₗ[ZMod 2] V}
    (hρ : ∀ v, q (ρ v) = q v) (hodd : Odd (orderOf ρ))
    (hinv : β * ρ * β⁻¹ = ρ⁻¹) {c : V} (hc : ρ c = c)
    (hβ : ∀ v, QuadraticMap.polar q v c = 0 → β v - v ∈ (ZMod 2) ∙ c) : ρ = 1 := by
  have hβfix : ∀ w ∈ commSpace ρ, β w = w :=
    apply_eq_self_of_mem_commSpace_of_conj_eq_inv hρ hodd hinv hc hβ
  have hβinvW : ∀ w ∈ commSpace ρ, β⁻¹ w = w := by
    intro w hw
    refine β.injective ?_
    change β (β.symm w) = β w
    rw [LinearEquiv.apply_symm_apply, hβfix w hw]
  have hρW : ∀ w ∈ commSpace ρ, ρ w ∈ commSpace ρ := by
    intro w hw
    exact AS35QCo.apply_mem_commSpace (g := ρ) (k := ρ) rfl hw
  have hρsq : ∀ w ∈ commSpace ρ, ρ (ρ w) = w := by
    intro w hw
    have hinvW : ρ⁻¹ w = ρ w := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e w) hinv
      have h' : β (ρ (β⁻¹ w)) = ρ⁻¹ w := by
        simpa [LinearEquiv.mul_apply] using h
      rw [hβinvW w hw, hβfix (ρ w) (hρW w hw)] at h'
      exact h'.symm
    have h2 : w = ρ (ρ w) := by
      have h := congrArg (fun x : V => ρ x) hinvW
      simpa [LinearEquiv.apply_symm_apply] using h
    exact h2.symm
  have hρfix : ∀ w ∈ commSpace ρ, ρ w = w := by
    intro w hw
    have hsq : (ρ ^ 2) w = w := by
      simpa [pow_two, LinearEquiv.mul_apply] using hρsq w hw
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := ρ) (n := 2)
      (Odd.coprime_two_left hodd)
    have hpow : ((ρ ^ 2) ^ m) w = w := by
      rw [LinearEquiv.pow_apply]
      exact Function.iterate_fixed hsq m
    rw [← hm]
    exact hpow
  have hWle : commSpace ρ ≤ fixSpace ρ := fun w hw => mem_fixSpace.mpr (hρfix w hw)
  have hWbot : commSpace ρ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hmem : w ∈ commSpace ρ ⊓ fixSpace ρ := Submodule.mem_inf.mpr ⟨hw, hWle hw⟩
    have hbot : commSpace ρ ⊓ fixSpace ρ = ⊥ := by
      rw [inf_comm]
      exact AS35QCo.fixSpace_inf_commSpace hodd (pow_orderOf_eq_one ρ)
    rwa [hbot, Submodule.mem_bot] at hmem
  ext v
  have hv : ρ v - v ∈ commSpace ρ := sub_mem_commSpace ρ v
  rw [hWbot, Submodule.mem_bot, sub_eq_zero] at hv
  simpa using hv

theorem commSpace_le_fixSpace_of_commute [FiniteDimensional (ZMod 2) V]
    {ω y : V ≃ₗ[ZMod 2] V} (hodd : Odd (orderOf ω)) (hcomm : y * ω = ω * y)
    (htriv : ∀ u ∈ commSpace ω, y u = u) : commSpace y ≤ fixSpace ω := by
  have hbot : fixSpace ω ⊓ commSpace ω = ⊥ :=
    AS35QCo.fixSpace_inf_commSpace hodd (pow_orderOf_eq_one ω)
  have hsup : fixSpace ω ⊔ commSpace ω = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace ω) (commSpace ω)
    rw [hbot, finrank_bot, add_zero] at h
    rw [h]
    have hsum := finrank_commSpace_add_finrank_fixSpace ω
    omega
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  have hv : v ∈ fixSpace ω ⊔ commSpace ω := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  have hcalc : y (c + u) - (c + u) = y c - c := by
    rw [map_add, htriv u hu]
    abel
  rw [hcalc]
  exact Submodule.sub_mem (fixSpace ω) (AS35QCo.apply_mem_fixSpace hcomm hc) hc

theorem le_commSpace_of_inf_fixSpace_eq_bot [FiniteDimensional (ZMod 2) V]
    {ω : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, ω w ∈ W)
    (hfree : W ⊓ fixSpace ω = ⊥) : W ≤ commSpace ω := by
  let f : W →ₗ[ZMod 2] W :=
    { toFun := fun w => ⟨ω w, hW w w.2⟩
      map_add' := fun a b => Subtype.ext (by simp [map_add])
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hker : LinearMap.ker (f - 1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hfx : f x = x := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
      simpa using hx
    have hx' : ω (x : V) = (x : V) := by
      have := congrArg Subtype.val hfx
      simpa [f] using this
    have hmem : (x : V) ∈ W ⊓ fixSpace ω :=
      Submodule.mem_inf.mpr ⟨x.2, mem_fixSpace.mpr hx'⟩
    rw [hfree, Submodule.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  intro w hw
  obtain ⟨u, -, hu⟩ := CFSG.GroupTheory.exists_mem_sub_one_eq_of_mem (T := f) hker
    (U := ⊤) (fun _ _ => Submodule.mem_top) (w := ⟨w, hw⟩) Submodule.mem_top
  refine mem_commSpace.mpr ⟨u, ?_⟩
  have := congrArg Subtype.val hu
  simpa [f] using this

end CFSG.LargeExtraspecial
