module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8K1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8Stab_repr_inl_of_neg {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u : V}
    (hu : ((fr.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = -u)
    (i : Fin 2) : fr.b.repr u (Sum.inl i) = 0 := by
  have h := congrArg (fun x => fr.b.repr x (Sum.inl i)) hu
  have hnot : (Sum.inl i : FFE8Idx) ∉ ffE8Hat Finset.univ := by simp [ffE8Hat]
  simp only [fr.repr_signChange, hnot, if_false, map_neg, Finsupp.coe_neg, Pi.neg_apply] at h
  revert h
  generalize fr.b.repr u (Sum.inl i) = c
  revert c
  decide

theorem ffE8Stab_repr_inr_of_fix {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u : V}
    (hu : ((fr.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = u)
    (k : Fin 4) : fr.b.repr u (Sum.inr k) = 0 := by
  have h := congrArg (fun x => fr.b.repr x (Sum.inr k)) hu
  have hmem : (Sum.inr k : FFE8Idx) ∈ ffE8Hat Finset.univ := by simp [ffE8Hat]
  simp only [fr.repr_signChange, hmem, if_true] at h
  revert h
  generalize fr.b.repr u (Sum.inr k) = c
  revert c
  decide

theorem ffE8Stab_refl_neg {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u : V} [Invertible (Q u)] (hu : Q u = -ε)
    (ht : ((fr.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = -u) :
    TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
      normalizer (ffE8Group fr : Set (OGroup Q)) :=
  ffE8K1_refl_mem_normalizer hε fr hu (ffE8Stab_repr_inl_of_neg fr ht 0)
    (ffE8Stab_repr_inl_of_neg fr ht 1)

theorem ffE8Stab_refl_fix {ε : ZMod 3} (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {u : V}
    [Invertible (Q u)]
    (ht : ((fr.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V) u = u) :
    TauCeti.QuadraticMap.reflectionOrthogonal Q u ∈
      normalizer (ffE8Group fr : Set (OGroup Q)) :=
  ffE8K1_refl_mem_normalizer_perp fr (ffE8Stab_repr_inr_of_fix fr ht)

theorem ffE8Stab_reflection_apply {γ : V ≃ₗ[ZMod 3] V} {μ : (ZMod 3)ˣ}
    (hγ : IsSimilitude Q γ μ) (w : V) [Invertible (Q w)] [Invertible (Q (γ w))] (y : V) :
    TauCeti.QuadraticMap.reflection Q (γ w) (γ y) =
      γ (TauCeti.QuadraticMap.reflection Q w y) := by
  have hpol : QuadraticMap.polar Q (γ w) (γ y) = μ * QuadraticMap.polar Q w y := by
    simp only [QuadraticMap.polar]
    rw [← map_add γ, hγ, hγ, hγ]
    ring
  have hμ : (μ : ZMod 3) ≠ 0 := μ.ne_zero
  have hw0 : Q w ≠ 0 := Invertible.ne_zero (Q w)
  have hs : (⅟(Q (γ w)) : ZMod 3) * (μ * QuadraticMap.polar Q w y) =
      ⅟(Q w) * QuadraticMap.polar Q w y := by
    simp only [invOf_eq_inv]
    rw [hγ w]
    field_simp
  rw [TauCeti.QuadraticMap.reflection_apply, TauCeti.QuadraticMap.reflection_apply, map_sub,
    map_smul, hpol, hs]

theorem ffE8Stab_simAct_reflection {γ : simGroup Q} {μ : (ZMod 3)ˣ}
    (hγ : IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) μ) (w : V) [Invertible (Q w)]
    [Invertible (Q ((γ : V ≃ₗ[ZMod 3] V) w))] :
    simAct Q γ (TauCeti.QuadraticMap.reflectionOrthogonal Q w) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q ((γ : V ≃ₗ[ZMod 3] V) w) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [coe_simAct, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.coe_reflectionOrthogonal, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ← ffE8Stab_reflection_apply hγ w]
  simp [LinearEquiv.coe_inv]

theorem ffE8Stab_conj_mem_normalizer {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (fr' : PFrame Q FFE8Idx (ffE8Norm ε)) (fr : PFrame Q (Option (Fin 5)) ffC)
    (ht : fr'.signChange (ffE8Hat Finset.univ) = ffZ0p fr) {γ : simGroup Q} {μ : (ZMod 3)ˣ}
    (hγ : IsSimilitude Q (γ : V ≃ₗ[ZMod 3] V) μ) (hμ : (μ : ZMod 3) = -ε)
    (hz : simAct Q γ (ffZ0p fr) = ffZ0p fr) :
    ∀ g ∈ ffB0p fr, simAct Q γ g ∈ normalizer (ffE8Group fr' : Set (OGroup Q)) := by
  have hcomm : ∀ x : V, ((ffZ0p fr : OGroup Q) : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) x) =
      (γ : V ≃ₗ[ZMod 3] V) (((ffZ0p fr : OGroup Q) : V ≃ₗ[ZMod 3] V) x) := by
    intro x
    have h := congrArg (fun g : OGroup Q =>
      ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) x)) hz
    simp only [coe_simAct, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] at h
    exact h.symm
  have hne : -ε ≠ 0 := by rcases hε with rfl | rfl <;> decide
  have hzv : ∀ x : V,
      ((fr'.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V) x =
        ((ffZ0p fr : OGroup Q) : V ≃ₗ[ZMod 3] V) x := fun x => by rw [ht]
  have hone : ∀ i : Fin 5, Q (fr.b (some i)) = 1 := fun i => fr.norm (some i)
  have hQu : ∀ i : Fin 5, Q ((γ : V ≃ₗ[ZMod 3] V) (fr.b (some i))) = -ε := fun i => by
    rw [hγ, hμ, hone i, mul_one]
  have hlast : Fin.last 4 ∉ ({0, 1, 2, 3} : Finset (Fin 5)) := by decide
  have hlow : ∀ i : Fin 4, (Fin.castSucc i : Fin 5) ∈ ({0, 1, 2, 3} : Finset (Fin 5)) := by
    decide
  have hsingle : ∀ i : Fin 5, fr.signChange {some i} ∈
      (normalizer (ffE8Group fr' : Set (OGroup Q))).comap (simAct Q γ).toMonoidHom := by
    refine Fin.lastCases ?_ (fun i' => ?_)
    · haveI : Invertible (Q (fr.b (some (Fin.last 4)))) :=
        invertibleOfNonzero (by rw [hone]; decide)
      haveI : Invertible (Q ((γ : V ≃ₗ[ZMod 3] V) (fr.b (some (Fin.last 4))))) :=
        invertibleOfNonzero (by rw [hQu]; exact hne)
      have hw : ((ffZ0p fr : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b (some (Fin.last 4))) =
          fr.b (some (Fin.last 4)) := by
        rw [ffZ0p, fr.signChange_basis, if_neg]
        rw [mem_ffOpt_some]
        exact hlast
      show simAct Q γ (fr.signChange {some (Fin.last 4)}) ∈
        normalizer (ffE8Group fr' : Set (OGroup Q))
      rw [ffOutFF6POmega_signChange_single_eq_reflection fr (some (Fin.last 4)),
        ffE8Stab_simAct_reflection hγ]
      exact ffE8Stab_refl_fix fr' (by rw [hzv, hcomm, hw])
    · haveI : Invertible (Q (fr.b (some (Fin.castSucc i')))) :=
        invertibleOfNonzero (by rw [hone]; decide)
      haveI : Invertible (Q ((γ : V ≃ₗ[ZMod 3] V) (fr.b (some (Fin.castSucc i'))))) :=
        invertibleOfNonzero (by rw [hQu]; exact hne)
      have hw : ((ffZ0p fr : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b (some (Fin.castSucc i'))) =
          -fr.b (some (Fin.castSucc i')) := by
        rw [ffZ0p, fr.signChange_basis, if_pos]
        rw [mem_ffOpt_some]
        exact hlow i'
      show simAct Q γ (fr.signChange {some (Fin.castSucc i')}) ∈
        normalizer (ffE8Group fr' : Set (OGroup Q))
      rw [ffOutFF6POmega_signChange_single_eq_reflection fr (some (Fin.castSucc i')),
        ffE8Stab_simAct_reflection hγ]
      exact ffE8Stab_refl_neg hε fr' (hQu _) (by rw [hzv, hcomm, hw, map_neg])
  intro g hg
  obtain ⟨J, hJn, -, rfl⟩ := hg
  exact ffE8K1_signChange_mem fr hsingle J hJn

theorem ffE8Stab_ts_mem_normalizer {ε : ZMod 3} (fr' : PFrame Q FFE8Idx (ffE8Norm ε))
    (fr : PFrame Q (Option (Fin 5)) ffC)
    (ht : fr'.signChange (ffE8Hat Finset.univ) = ffZ0p fr) :
    ffTs fr ∈ normalizer
      (((ffE8Group fr').map (ffSim Q) : Subgroup (ProjSim Q)) : Set (ProjSim Q)) := by
  haveI : Invertible (Q (fr.b none)) := invertibleOfNonzero (by rw [fr.norm]; decide)
  have hfix : ((fr'.signChange (ffE8Hat Finset.univ) : OGroup Q) : V ≃ₗ[ZMod 3] V)
      (fr.b none) = fr.b none := by
    rw [ht, ffZ0p, fr.signChange_basis, if_neg (none_notMem_ffOpt _)]
  have hmem := ffE8Stab_refl_fix fr' hfix
  have hts : ffTs fr = ffSim Q (fr.signChange {none}) := rfl
  rw [hts, ffOutFF6POmega_signChange_single_eq_reflection fr none]
  exact Subgroup.le_normalizer_map (ffSim Q) (Subgroup.mem_map_of_mem _ hmem)

end CFSG.OddStandard.SmallF3.Omega
