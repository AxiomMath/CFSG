module

public import CFSG.LargeExtraspecial.AS35YFOm4
public import CFSG.LargeExtraspecial.BridgeForms
public import CFSG.LargeExtraspecial.S12InspFamOMinus
public import CFSG.RankThree.PartOne.S11d.OrthCyclic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4MinusC

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification

set_option maxRecDepth 100000 in
theorem exists_threeCycle_fix : ∀ x : Fin (2 * 2) → ZMod 2, x ≠ 0 →
    ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ AS35YF.act5 σ x = x := by
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_isometry_qm4 (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    ∃ L : V ≃ₗ[ZMod 2] (Fin (2 * 2) → ZMod 2), ∀ v, AS35YF.qm4 (L v) = Q v := by
  let L₀ : V ≃ₗ[ZMod 2] (Fin (2 * 2) → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) V h4).equivFun
  let Q' : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2) :=
    Q.comp (L₀.symm : (Fin (2 * 2) → ZMod 2) →ₗ[ZMod 2] V)
  have hQ' : ∀ v, Q' (L₀ v) = Q v := fun v => by simp [Q']
  have hnd : ∀ x, (∀ y, polar Q' x y = 0) → x = 0 :=
    Bridge.nondegenerate_of_map L₀ hQ'
      ((Bridge.polarBilin_nondegenerate_iff Q).mp hQ)
  have hmin' : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q' w = 0 := by
    rintro ⟨W, hW2, hW0⟩
    obtain ⟨u, ⟨w, hw, rfl⟩, hu⟩ := hmin (W.map (L₀.symm : _ →ₗ[ZMod 2] V))
      (by rw [LinearEquiv.finrank_map_eq, hW2])
    refine hu ?_
    rw [LinearEquiv.coe_coe, ← hQ' (L₀.symm w), LinearEquiv.apply_symm_apply]
    exact hW0 w hw
  obtain ⟨L₁, hL₁⟩ := exists_linearEquiv_fin_of_ncard_eq Q' S12Insp5.quadMinusFour hnd
    S12Insp5.quadMinusFour_nondeg
    ((S12Insp5.ncard_eq_ten_of_minus hnd hmin').trans S12Insp5.ncard_quadMinusFour.symm)
  refine ⟨L₀.trans L₁, fun v => ?_⟩
  rw [LinearEquiv.trans_apply]
  calc AS35YF.qm4 (L₁ (L₀ v)) = S12Insp5.quadMinusFour (L₁ (L₀ v)) :=
        (S12Insp5.quadMinusFour_apply _).symm
    _ = Q' (L₀ v) := hL₁ _
    _ = Q v := hQ' v

theorem exists_omega_three_fix (hQ : Q.polarBilin.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0)
    {b : V} (hb : b ≠ 0) :
    ∃ ω ∈ omegaGroup Q hQ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω b = b := by
  obtain ⟨L, hL⟩ := exists_isometry_qm4 hQ h4 hmin
  obtain ⟨σ, hσ3, hσ1, hσb⟩ := exists_threeCycle_fix (L b) ((LinearEquiv.map_ne_zero_iff L).mpr hb)
  let ω : V ≃ₗ[ZMod 2] V := (L.trans (AS35YF.act5L σ)).trans L.symm
  have hω : ∀ v, ω v = L.symm (AS35YF.act5 σ (L v)) := fun v => rfl
  have hωO : ω ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [← hL, hω, LinearEquiv.apply_symm_apply, AS35YF.qm4_act5, hL]
  have hω3 : ω ^ 3 = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have h3 : AS35YF.act5 σ (AS35YF.act5 σ (AS35YF.act5 σ (L v))) = L v := by
      rw [← AS35YF.act5_mul, ← AS35YF.act5_mul, ← pow_three', hσ3, AS35YF.act5_one]
    rw [pow_three]
    change ω (ω (ω v)) = v
    rw [hω, hω, hω, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h3,
      LinearEquiv.symm_apply_apply]
  have hω1 : ω ≠ 1 := by
    intro h1
    have hfix : ∀ y, AS35YF.act5 σ y = y := fun y => by
      have h2 := DFunLike.congr_fun h1 (L.symm y)
      rw [hω, LinearEquiv.apply_symm_apply] at h2
      exact L.symm.injective h2
    exact hσ1 (AS35YF.eq_one_of_act5 σ (hfix _) (hfix _) (hfix _) (hfix _))
  have hωΩ : ω ∈ omegaGroup Q hQ :=
    CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hQ (by decide) hωO hω3
  refine ⟨ω, hωΩ, hω3, hω1, ?_⟩
  rw [hω, hσb, LinearEquiv.symm_apply_apply]

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_one_of_forall_sub_singular (hQ : Q.polarBilin.Nondegenerate)
    (hmin : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → ∃ u ∈ U, Q u ≠ 0)
    {e : V ≃ₗ[ZMod 2] V} (he : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h0 : ∀ x, Q (e x - x) = 0) : e = 1 := by
  have hnd := (Bridge.polarBilin_nondegenerate_iff Q).mp hQ
  have z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h2 : (2 : ZMod 2) = 0 := rfl
  have key : ∀ v, polar Q v (e v - v) = 0 := fun v => by
    have h1 := QuadraticMap.map_add Q (e v - v) v
    rw [sub_add_cancel, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup he v, h0 v] at h1
    rw [polar_comm]
    linear_combination -h1
  by_contra hne
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, e v₀ ≠ v₀ := by
    by_contra! h
    exact hne (LinearEquiv.ext h)
  obtain ⟨c, hc⟩ : ∃ c, c = e v₀ - v₀ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.mpr hv₀
  obtain ⟨w, hw⟩ : ∃ w, polar Q c w ≠ 0 := by
    by_contra! h
    exact hc0 (hnd c h)
  obtain ⟨d, hd⟩ : ∃ d, d = e w - w := ⟨_, rfl⟩
  have hwc : polar Q w c = 1 := by
    rw [polar_comm]
    exact (z2 _).resolve_left hw
  have hkc : polar Q v₀ c = 0 := by
    rw [hc]
    exact key v₀
  have hkd : polar Q w d = 0 := by
    rw [hd]
    exact key w
  have hcd : c + d = e (v₀ + w) - (v₀ + w) := by
    rw [hc, hd, map_add]
    abel
  have hQc : Q c = 0 := by
    rw [hc]
    exact h0 v₀
  have hQd : Q d = 0 := by
    rw [hd]
    exact h0 w
  have hQcd : Q (c + d) = 0 := by
    rw [hcd]
    exact h0 _
  have hvd : polar Q v₀ d = 1 := by
    have h1 := key (v₀ + w)
    rw [← hcd, polar_add_left, polar_add_right, polar_add_right] at h1
    linear_combination h1 - hkc - hkd - hwc - h2
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hvd
    exact zero_ne_one hvd
  have hcd_ne : c ≠ d := by
    rintro rfl
    rw [hkd] at hwc
    exact zero_ne_one hwc
  have hli : LinearIndependent (ZMod 2) ![c, d] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    rcases z2 s with rfl | rfl <;> rcases z2 t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at h
      exact absurd h hd0
    · rw [zero_smul, one_smul, add_zero] at h
      exact absurd h hc0
    · rw [one_smul, one_smul, ← ZModModule.sub_eq_add, sub_eq_zero] at h
      exact absurd h hcd_ne
  obtain ⟨u, hu, hQu⟩ := hmin (Submodule.span (ZMod 2) (Set.range ![c, d]))
    (by rw [finrank_span_eq_card hli, Fintype.card_fin])
  rw [Submodule.mem_span_range_iff_exists_fun] at hu
  obtain ⟨f, rfl⟩ := hu
  refine hQu ?_
  rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases z2 (f 0) with h0' | h0' <;> rcases z2 (f 1) with h1' | h1' <;>
    simp [h0', h1', hQc, hQd, hQcd]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_sub_sub_eq_zero {e : V ≃ₗ[ZMod 2] V}
    (he : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (he2 : e * e = 1) (v v' : V) :
    QuadraticMap.polar Q (e v - v) (e v' - v') = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hee : e (e v') = v' := DFunLike.congr_fun he2 v'
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup he v v'
  have h3 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup he v (e v')
  rw [hee] at h3
  simp only [polar_sub_left, polar_sub_right]
  linear_combination h1 + h3 + (polar Q v v' - polar Q (e v) v') * h2

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_le_one_of_anisotropic_of_isotropic {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, Q w = 0 → w = 0)
    (hpol : ∀ w ∈ W, ∀ w' ∈ W, QuadraticMap.polar Q w w' = 0) :
    finrank (ZMod 2) W ≤ 1 := by
  have hcc : ∀ c : ZMod 2, c * c = c := by decide
  let f : W →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun w => Q (w : V)
      map_add' := fun w w' => by
        have h := QuadraticMap.map_add Q (w : V) (w' : V)
        rw [hpol w w.2 w' w'.2, add_zero] at h
        exact h
      map_smul' := fun c w => by
        change Q ((c • w : W) : V) = c • Q (w : V)
        rw [Submodule.coe_smul, QuadraticMap.map_smul, hcc, smul_eq_mul] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    exact Subtype.ext (hW w w.2 hw)
  calc finrank (ZMod 2) W ≤ finrank (ZMod 2) (ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := finrank_self (ZMod 2)

end CFSG.GF2Type.Smith1979.W4MinusC
