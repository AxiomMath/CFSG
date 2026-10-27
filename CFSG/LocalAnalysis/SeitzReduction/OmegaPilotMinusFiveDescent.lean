module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClassDescent

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap
open CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT incl incl_injective
  subfieldDerivedImage vecIncl exists_ne_zero_of_nondeg)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed
  isExtension_coordinateQuadMinus autExtensionComm_incl_minus)
open CFSG.Quasithin (perfectCore)

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_mulEquiv_congr_eq_fieldAutT_minus_of_four_le {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hn : 4 ≤ n) {b c : K} (hb : σ b = b) (hc : σ c = c)
    (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hβ : β * β = 1)
    {D : Subgroup (fixedSubgroup β)} (hD : CFSG.IsComponent D) {g : ℕ}
    (hDm : LieModel D .POmegaMinus n 2 g) :
    ∃ Θ : matrixProjectiveDerived (coordinateQuadPlus n K) ≃*
        matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus n K (by omega) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact TwistedE6Pilot.exists_mulEquiv_congr_eq_fieldAutT hσ hb hc hirr hβ hD hDm
  · exact exists_mulEquiv_congr_eq_fieldAutT_minus hσ h5 hb hc hirr hβ hD hDm

end Descent

section Normalize

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem exists_mulEquiv_comp_eq_incl_minus_of_four_le {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {k : Subfield F} (hσk : ∀ x, x ∈ k ↔ σ x = x) (hm : 4 ≤ m) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {Kc : Type} [Group Kc] (ψ₀ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus m F))
    {τ : MulAut Kc} (hτ : τ * τ = 1)
    {D' : Subgroup (fixedSubgroup τ)} (hD' : CFSG.IsComponent D') {g : ℕ}
    (hD'm : LieModel D' .POmegaMinus m 2 g)
    {A : Type} [Group A] (ε : A →* Kc) (hε : Function.Injective ε)
    (hεr : ε.range = D'.map (fixedSubgroup τ).subtype)
    (j : A ≃* matrixProjectiveDerived (coordinateQuadMinus m k (by omega) b c)) :
    ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadMinus m F (by omega) (b : F) (c : F)),
      (∀ a, ψ (ε a) = incl k (isExtension_coordinateQuadMinus k (by omega) b c) (j a)) ∧
      MulAut.congr ψ τ = fieldAutT (coordinateQuadMinus m F (by omega) (b : F) (c : F)) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) ((hσk b).1 b.2) ((hσk c).1 c.2)) := by
  have hm1 : 1 ≤ m := by omega
  have hext := isExtension_coordinateQuadMinus k hm1 b c
  have hb : σ (b : F) = b := (hσk b).1 b.2
  have hc : σ (c : F) = c := (hσk c).1 c.2
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + (b : F) * s + (c : F) ≠ 0 := by
    intro s hs h0
    apply hirr ⟨s, (hσk s).2 hs⟩
    apply Subtype.ext
    simpa using h0
  have hQσ := coordinateQuadMinus_fieldMap_of_fixed (n := m) hm1 hb hc
  set σs := fieldAutT (coordinateQuadMinus m F hm1 (b : F) (c : F)) σ hQσ with hσs
  set β : MulAut (matrixProjectiveDerived (coordinateQuadPlus m F)) := MulAut.congr ψ₀ τ
    with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hfix : fixedSubgroup β = (fixedSubgroup τ).map ψ₀.toMonoidHom :=
    ExcSelector.fixedSubgroup_congr ψ₀ τ
  let Φ : fixedSubgroup τ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ).equivMapOfInjective ψ₀.toMonoidHom ψ₀.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  have hD'' : CFSG.IsComponent (D'.map Φ.toMonoidHom) := CatLeaf.isComponent_map_mulEquiv Φ hD'
  have hD''m : LieModel (D'.map Φ.toMonoidHom) .POmegaMinus m 2 g :=
    LieType.CurtisTits.lieModel_of_mulEquiv (D'.equivMapOfInjective Φ.toMonoidHom Φ.injective)
      hD'm
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_congr_eq_fieldAutT_minus_of_four_le hσ hm hb hc hirrF hβ hD''
    hD''m
  set ψ₁ : Kc ≃* matrixProjectiveDerived (coordinateQuadMinus m F hm1 (b : F) (c : F)) :=
    ψ₀.trans Θ with hψ₁
  have hψ₁τ : MulAut.congr ψ₁ τ = σs := by
    have h1 : MulAut.congr ψ₁ τ = MulAut.congr Θ β := MulEquiv.ext fun _ => rfl
    rw [h1, hΘ]
  have hσψ : ∀ x, ψ₁ (τ x) = σs (ψ₁ x) := fun x => by
    rw [← hψ₁τ]
    change ψ₁ (τ x) = ψ₁ (τ (ψ₁.symm (ψ₁ x)))
    rw [MulEquiv.symm_apply_apply]
  have hfixε : ∀ a, ψ₁ (ε a) ∈ fixedSubgroup σs := by
    intro a
    obtain ⟨d, -, hda⟩ : ε a ∈ D'.map (fixedSubgroup τ).subtype := hεr ▸ ⟨a, rfl⟩
    have hτd : τ (ε a) = ε a := by
      rw [← hda]
      exact d.2
    change σs (ψ₁ (ε a)) = ψ₁ (ε a)
    rw [← hσψ, hτd]
  set ε' : matrixProjectiveDerived (coordinateQuadMinus m k hm1 b c) →*
      matrixProjectiveDerived (coordinateQuadMinus m F hm1 (b : F) (c : F)) :=
    (ψ₁.toMonoidHom.comp ε).comp j.symm.toMonoidHom with hε'
  have hε'inj : Function.Injective ε' := ψ₁.injective.comp (hε.comp j.symm.injective)
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
  obtain ⟨hQk, -⟩ := regular_coordinateQuadMinus m k b c (by omega) hirr
  have hQne : ∃ v, coordinateQuadMinus m F hm1 (b : F) (c : F) v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne_zero_of_nondeg (by omega : 0 < 2 * m) hQk
    refine ⟨vecIncl k v, ?_⟩
    rw [hext v]
    exact fun h => hv (Subtype.ext h)
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT hQσ hσk hext hQne hJ
  have hperf : ⁅ε'.range, ε'.range⁆ = ε'.range :=
    E7Pilot.commutator_range_of_commutator_top _ (commutator_top_coordinateMinus (by omega) hirr)
  have hle : ε'.range ≤ subfieldDerivedImage k hext := by
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ hperf
    rintro _ ⟨x, rfl⟩
    exact hfixε (j.symm x)
  have hιinj : Function.Injective (incl k hext) := incl_injective k hext (by omega)
  have hrange : ε'.range = (incl k hext).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hε'inj).toEquiv]
  let δ : MulAut (matrixProjectiveDerived (coordinateQuadMinus m k hm1 b c)) :=
    ((MonoidHom.ofInjective hε'inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hιinj).symm
  have hδ : ∀ x, incl k hext (δ x) = ε' x := by
    intro x
    have h1 := (MonoidHom.ofInjective hιinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε'inj x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδ'c⟩ := autExtensionComm_incl_minus (n := m) (by omega) hσk b c hirr hQσ δ⁻¹
  refine ⟨ψ₁.trans δ', fun a => ?_, ?_⟩
  · have h3 : ψ₁ (ε a) = ε' (j a) := by
      rw [hε']
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [MulEquiv.trans_apply, h3, ← hδ, hδ', MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · have h4 : MulAut.congr (ψ₁.trans δ') τ = δ' * MulAut.congr ψ₁ τ * δ'⁻¹ :=
      MulEquiv.ext fun _ => rfl
    rw [h4, hψ₁τ, hδ'c, mul_assoc, mul_inv_cancel, mul_one]

end Normalize

end CFSG.SeitzReduction.OmegaPilot
