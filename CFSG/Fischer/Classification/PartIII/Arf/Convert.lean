module

public import CFSG.Fischer.Classification.PartIII.Arf.Witt
public import CFSG.Fischer.Classification.PartIII.Arf.Gamma
public import CFSG.Fischer.Classification.PartIII.Symp.MinusSix

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open QuadraticMap Symplectic LocalSymp Matrix

namespace Arf

theorem tv_tv_tv_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hsymm : ∀ x y, B x y = B y x) (halt : ∀ x, B x x = 0)
    (u v x : V) : tv B u (tv B v (tv B u x)) = tv B (tv B u v) x := by
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    halt, mul_zero, add_zero, smul_add, smul_smul]
  rw [hsymm u v]
  rcases zmod_two_cases (B x u) with h1 | h1 <;> rcases zmod_two_cases (B x v) with h2 | h2 <;>
    rcases zmod_two_cases (B v u) with h3 | h3 <;>
    simp only [h1, h2, h3, zero_add, add_zero, zero_smul, one_smul, mul_zero, mul_one,
      zmod_two_one_add_one] <;>
    zmod_two_abel

variable {H : Type} [Group H] {F : Set H} {k : ℕ} {Q : QuadraticForm (ZMod 2) (Fin k → ZMod 2)}
  {φ : H ≃* (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)}

theorem exists_modelAct_eq
    (hφ : ∀ g, g ∈ F ↔ ((φ g : GL (Fin k) (ZMod 2)) ∈
      fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) {e : H} (he : e ∈ F) :
    ∃ v, Q v = 1 ∧ modelAct φ e = tv (polarBilin Q) v := by
  obtain ⟨v, hv, h⟩ := (hφ e).1 he
  exact ⟨v, hv, funext fun x => by rw [tv_apply, polarBilin_apply_apply]; exact h x⟩

theorem exists_mem_modelAct_eq
    (hφ : ∀ g, g ∈ F ↔ ((φ g : GL (Fin k) (ZMod 2)) ∈
      fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) {v : Fin k → ZMod 2}
    (hv : Q v = 1) : ∃ e ∈ F, modelAct φ e = tv (polarBilin Q) v := by
  have hT := orthTransvectionGL_mem_fischerTransvections hv
  refine ⟨φ.symm ⟨_, fischerTransvections_polar_subset hT⟩, ?_, ?_⟩
  · rw [hφ, MulEquiv.apply_symm_apply]
    exact hT
  · rw [modelAct_symm]
    funext x
    rw [tv_apply, polarBilin_apply_apply]
    exact orthTransvectionGL_mulVec hv x

theorem eq_of_tv_eq_of_map_eq_one (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    {v w : Fin k → ZMod 2} (hv : Q v = 1) (h : tv (polarBilin Q) v = tv (polarBilin Q) w) :
    v = w := by
  refine eq_of_tv_eq _ (fun x hx => hnd x fun y => ?_) (fun h0 => ?_) h
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hx y
  · rw [h0, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv

end Arf

open Arf

theorem exists_mulEquiv_formMinusFive_of_minusSix {H : Type} [Group H] {F : Set H}
    (hP : Pair H F) (hZ : Subgroup.center H = ⊥) (h : MinusSixLocal H F) :
    ∃ φ : H ≃* R3 formMinusFive, φ '' F = D3 formMinusFive := by
  obtain ⟨Q, hnd, hQ, φ, hφ⟩ := h
  set B := polarBilin Q
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]
  have halt : ∀ x, B x x = 0 := fun x => by
    rw [polarBilin_apply_apply, polar_self_zmod2]
  have hN : {v | Q v = 1}.ncard = 36 := by
    have h2 := two_mul_ncard_quadratic Q hnd (m := 3) (by simp)
    norm_num at h2 hQ
    omega
  obtain ⟨L, hL⟩ := exists_linearEquiv_of_ncard_eq Q quadMinusSix hnd polar_quadMinusSix_nondeg
    rfl (hN.trans ncard_quadMinusSix.symm)
  have hLpol : ∀ x y, polar quadMinusSix (L x) (L y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, hL, hL, hL]
  choose vec hvecQ hvec using fun e : F => exists_modelAct_eq hφ e.2
  have hvec_eq : ∀ (e : F) {w}, modelAct φ e = tv B w → vec e = w := fun e w hw =>
    eq_of_tv_eq_of_map_eq_one hnd (hvecQ e) (by rw [← hvec e, hw])
  have hQ₀ : ∀ e : F, quadMinusSix (L (vec e)) = 1 := fun e => by rw [hL]; exact hvecQ e
  obtain ⟨ψ, -, hψ⟩ := exists_mulEquiv_R3_of_vec hP hZ isF3Form_formMinusFive (by norm_num)
    (fun e => gamma (L (vec e))) (fun e => gamma_norm _)
    (fun e e' h => Subtype.ext (modelAct_injective φ (by
      rw [hvec e, hvec e', L.injective (gamma_injective (hQ₀ e) (hQ₀ e') h)])))
    (fun x hx => by
      obtain ⟨v, hv, h⟩ := exists_gamma_eq hx
      obtain ⟨e, he, hev⟩ := exists_mem_modelAct_eq hφ (v := L.symm v) (by
        rw [← hL, LinearEquiv.apply_symm_apply, hv])
      refine ⟨⟨e, he⟩, ?_⟩
      rwa [hvec_eq ⟨e, he⟩ hev, LinearEquiv.apply_symm_apply])
    (fun d e => by
      have hv : vec (tauE hP d e) = tv B (vec d) (vec e) := hvec_eq _ (funext fun x => by
        rw [tauE_coe, modelAct_mul, modelAct_mul, hvec d, hvec e, Function.comp_apply,
          Function.comp_apply, tv_tv_tv_eq B hsymm halt])
      rw [hv, tv_apply, map_add, map_smul, polarBilin_apply_apply, ← hLpol]
      exact gamma_transvection (hQ₀ d) (hQ₀ e))
  exact ⟨ψ, hψ⟩

end CFSG.Fischer.Classification
