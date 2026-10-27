module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsCover

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT incl_injective
  subfieldDerivedImage vecIncl exists_ne_zero_of_nondeg fieldAutT_fixes_J)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.Quasithin (perfectCore)

section PSLCongr

variable {K L : Type*} [Field K] [Field L]

@[expose] def slRingCongr (ρ : K ≃+* L) (n : ℕ) :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) L where
  toFun := SpecialLinearGroup.map ρ.toRingHom
  invFun := SpecialLinearGroup.map ρ.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

@[expose] def pslRingCongr (ρ : K ≃+* L) (n : ℕ) :
    LinearFlag.projectiveSL n K ≃* LinearFlag.projectiveSL n L :=
  QuotientGroup.congr (LinearFlag.scalars n K) (LinearFlag.scalars n L) (slRingCongr ρ n) (by
    rw [LinearFlag.scalars_eq_center, LinearFlag.scalars_eq_center]
    exact CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (slRingCongr ρ n))

theorem pslRingCongr_proj (ρ : K ≃+* L) (n : ℕ) (g : SpecialLinearGroup (Fin n) K) :
    pslRingCongr ρ n (LinearFlag.proj n K g) =
      LinearFlag.proj n L (SpecialLinearGroup.map ρ.toRingHom g) :=
  rfl

theorem pslRingCongr_fieldAut (ρ : K ≃+* L) (n : ℕ) (φ : K ≃+* K)
    (x : LinearFlag.projectiveSL n K) :
    pslRingCongr ρ n (LinearFlag.fieldAut n K φ x) =
      LinearFlag.fieldAut n L (ρ.symm.trans (φ.trans ρ)) (pslRingCongr ρ n x) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K x
  rw [LinearFlag.fieldAut_proj, pslRingCongr_proj, pslRingCongr_proj, LinearFlag.fieldAut_proj]
  congr 1
  ext i j
  simp

theorem pslRingCongr_dualAut (ρ : K ≃+* L) (n : ℕ) (x : LinearFlag.projectiveSL n K) :
    pslRingCongr ρ n (LinearFlag.dualAut n K x) = LinearFlag.dualAut n L (pslRingCongr ρ n x) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K x
  rw [LinearFlag.dualAut_proj, pslRingCongr_proj, pslRingCongr_proj, LinearFlag.dualAut_proj]
  congr 1
  rw [← map_inv]
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]

end PSLCongr

section Facts

theorem exists_roots_of_minus {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {k : Subfield F} (hσk : ∀ x, x ∈ k ↔ σ x = x) {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ∃ α : F, α + σ α = (b : F) ∧ α * σ α = (c : F) ∧ σ (σ α) = α := by
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have : CharP k 2 := RingHom.charP k.subtype Subtype.val_injective 2
  obtain ⟨f, -, hkf⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range k.subtype := fun x => by
    rw [← hσk]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix k.subtype hkf hσ hfix
  have hFk : Nat.card F = Nat.card k ^ 2 := by rw [hF, hkf, ← pow_mul, mul_comm]
  obtain ⟨α, hα0⟩ := exists_root_of_card_eq_sq k.subtype hFk hirr
  have hα : α ^ 2 + (b : F) * α + (c : F) = 0 := hα0
  have hb : σ (b : F) = b := (hσk b).1 b.2
  have hc : σ (c : F) = c := (hσk c).1 c.2
  have hα' : σ α ^ 2 + (b : F) * σ α + (c : F) = 0 := by
    have := congrArg σ hα
    rw [map_add, map_add, map_mul, map_pow, map_zero] at this
    change σ α ^ 2 + σ (b : F) * σ α + σ (c : F) = 0 at this
    rwa [hb, hc] at this
  have hne : σ α ≠ α := by
    intro h
    apply hirr ⟨α, (hσk α).2 h⟩
    apply Subtype.ext
    simpa using hα
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsum : α + σ α = (b : F) := by
    have h3 : (α - σ α) * (α + σ α + (b : F)) = 0 := by linear_combination hα - hα'
    have h4 : α + σ α + (b : F) = 0 :=
      (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm hne))
    linear_combination h4 - (b : F) * h2
  refine ⟨α, hsum, ?_, ?_⟩
  · have h5 : σ α = (b : F) - α := by linear_combination hsum
    rw [h5]
    linear_combination -hα + ((b : F) * α) * h2
  · have := congrArg (fun γ : F ≃+* F => γ α) hσσ
    exact this

theorem commutator_top_coordinateMinus_three {k : Type} [Field k] [Finite k] [CharP k 2]
    {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ⁅(⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadMinus 3 k (by norm_num) b c))),
      (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadMinus 3 k (by norm_num) b c)))⁆ =
        ⊤ := by
  obtain ⟨hR, hW⟩ := regular_wittIndex_coordinateQuadMinus (K := k) (m := 3) (by norm_num) hirr
  have hts : ∀ U : Submodule k (Fin (2 * 3) → k), Module.finrank k U = 3 →
      ∃ u ∈ U, coordinateQuadMinus 3 k (by norm_num) b c u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    have := hW U hcon
    omega
  obtain ⟨hq, -⟩ := isQuasisimple_orthDerived_of_six hR (by rw [Module.finrank_fin_fun]) hts
  have h1 := E7Pilot.commutator_range_of_commutator_top
    (projHom (coordinateQuadMinus 3 k (by norm_num) b c)) hq.1.commutator_eq_top
  rwa [MonoidHom.range_eq_top.2 (projHom_surjective _)] at h1

theorem commutator_range_toPSL_four {f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 f F) :
    ⁅(UnitaryPilot.toPSL h 4).range, (UnitaryPilot.toPSL h 4).range⁆ =
      (UnitaryPilot.toPSL h 4).range := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card F = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h'
    exact absurd (congrArg Prod.fst h') (by norm_num)
  obtain ⟨hq, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 4) hF
    (by norm_num) hnq
  have h1 := E7Pilot.commutator_range_of_commutator_top
    ((UnitaryPilot.toPSL h 4).comp (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 4))
    hq.1.commutator_eq_top
  rwa [MonoidHom.range_comp, MonoidHom.range_eq_top.2
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj_surjective h 4), ← MonoidHom.range_eq_map] at h1

end Facts

section Normalize

theorem minusNormalizationThreeInput_holds : MinusNormalizationThreeInput := by
  intro F _ _ _ σ hσ k hσk b c hirr Kc _ τ K' _ _ hK' eK φ hφ hτ A _ ε hε hεfix j
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have : CharP k 2 := RingHom.charP k.subtype Subtype.val_injective 2
  obtain ⟨f, hf1, hkf⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range k.subtype := fun x => by
    rw [← hσk]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix k.subtype hkf hσ hfix
  have hU : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf1, hF⟩
  obtain ⟨-, hσpow⟩ := LinearFlag.even_and_eq_pow_of_involution (by omega : 1 ≤ 2 * f) hF hσ1 hσσ
  have hσq : ∀ x, σ x = x ^ 2 ^ f := fun x => by
    rw [hσpow]
    congr 2
    omega
  have hbar : UnitaryPilot.barRingEquiv hU = σ := RingEquiv.ext fun x => by
    rw [UnitaryPilot.barRingEquiv_apply, hU.bar_apply, hσq]
  have hθ : UnitaryPilot.graphFieldAut hU 4 =
      LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F := by
    rw [UnitaryPilot.graphFieldAut, hbar]
  have : Fintype K' := Fintype.ofFinite K'
  have : Fintype F := Fintype.ofFinite F
  let ρ : K' ≃+* F := FiniteField.ringEquivOfCardEq (K := K') (K' := F) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'])
  have hρφ : ρ.symm.trans (φ.trans ρ) = σ := RingEquiv.ext fun x => by
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hφ, map_pow, RingEquiv.apply_symm_apply,
      hσq, hkf]
  set eF : Kc ≃* LinearFlag.projectiveSL 4 F := eK.trans (pslRingCongr ρ 4) with heF
  have hτF : ∀ x, eF (τ (eF.symm x)) =
      (LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F) x := by
    intro x
    obtain ⟨y, rfl⟩ := (pslRingCongr ρ 4).surjective x
    have h1 : eF (τ (eF.symm (pslRingCongr ρ 4 y))) =
        pslRingCongr ρ 4 (MulAut.congr eK τ y) := by
      rw [heF, MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply]
      rfl
    rw [h1, hτ, MulAut.mul_apply, MulAut.mul_apply, pslRingCongr_fieldAut, pslRingCongr_dualAut,
      hρφ]
  obtain ⟨α, hs, hp, hσσα⟩ := exists_roots_of_minus hσ hσk hirr
  have hb0 : (b : F) ≠ 0 := by
    have : b ≠ 0 := coeff_ne_zero_of_irreducible hirr
    exact fun h => this (Subtype.ext h)
  have hbβ : (b : F) * (b : F)⁻¹ = 1 := mul_inv_cancel₀ hb0
  have hσb : σ (b : F) = b := (hσk b).1 b.2
  have hσc : σ (c : F) = c := (hσk c).1 c.2
  have hσβ : σ (b : F)⁻¹ = (b : F)⁻¹ := by rw [map_inv₀, hσb]
  have hQσ := coordinateQuadMinus_fieldMap_of_fixed (n := 2 + 1) (by omega) hσb hσc
  set σs := fieldAutT (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F)) σ hQσ with hσs
  set Θ : LinearFlag.projectiveSL 4 F ≃*
      matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F)) :=
    minusKleinEquiv hs hp hbβ with hΘdef
  have hΘ : ∀ x, Θ ((LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F) x) = σs (Θ x) :=
    minusKleinEquiv_graphField hs hp hbβ σ rfl hσσα hσb hσc hσβ hQσ
  have hΘθ : ∀ x, Θ (UnitaryPilot.graphFieldAut hU 4 x) = σs (Θ x) := fun x => by
    rw [hθ]
    exact hΘ x
  set ψ₁ : Kc ≃* matrixProjectiveDerived
      (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F)) := eF.trans Θ with hψ₁
  have hψ₁τ : MulAut.congr ψ₁ τ = σs := by
    ext x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    change Θ (eF (τ (eF.symm (Θ.symm (Θ y))))) = σs (Θ y)
    rw [MulEquiv.symm_apply_apply, hτF, hΘ]
  have hσψ : ∀ x, ψ₁ (τ x) = σs (ψ₁ x) := fun x => by
    rw [← hψ₁τ]
    change ψ₁ (τ x) = ψ₁ (τ (ψ₁.symm (ψ₁ x)))
    rw [MulEquiv.symm_apply_apply]
  have hfixε : ∀ a, ψ₁ (ε a) ∈ fixedSubgroup σs := by
    intro a
    have hτa : τ (ε a) = ε a := hεfix ⟨a, rfl⟩
    change σs (ψ₁ (ε a)) = ψ₁ (ε a)
    rw [← hσψ, hτa]
  have hext := isExtension_coordinateQuadMinus k (n := 2 + 1) (by omega) b c
  have hJtop := commutator_top_coordinateMinus_three hirr
  have hJ : ⁅subfieldDerivedImage k hext, subfieldDerivedImage k hext⁆ =
      subfieldDerivedImage k hext :=
    E7Pilot.commutator_range_of_commutator_top _ hJtop
  have hQne : ∃ v, coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F) v ≠ 0 :=
    exists_ne_zero_of_isometry (minusKleinIso hs hp hbβ)
  have hcore := E7Pilot.perfectCore_fixedSubgroup_fieldAutT hQσ hσk hext hQne hJ
  set ε' : matrixProjectiveDerived (coordinateQuadMinus (2 + 1) k (by omega) b c) →*
      matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F)) :=
    (ψ₁.toMonoidHom.comp ε).comp j.symm.toMonoidHom with hε'
  have hε'inj : Function.Injective ε' := ψ₁.injective.comp (hε.comp j.symm.injective)
  have hperf : ⁅ε'.range, ε'.range⁆ = ε'.range := E7Pilot.commutator_range_of_commutator_top _ hJtop
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
  let δ : MulAut (matrixProjectiveDerived (coordinateQuadMinus (2 + 1) k (by omega) b c)) :=
    ((MonoidHom.ofInjective hε'inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hιinj).symm
  have hδ : ∀ x, incl k hext (δ x) = ε' x := by
    intro x
    have h1 := (MonoidHom.ofInjective hιinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε'inj x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  set ι := UnitaryPilot.toPSL hU 4 with hι
  set θ := UnitaryPilot.graphFieldAut hU 4 with hθdef
  have hθfix : ∀ x, θ (Θ.symm x) = Θ.symm (σs x) := fun x => by
    apply Θ.injective
    rw [hΘθ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hJfix : ∀ x, σs (incl k hext x) = incl k hext x := fun x =>
    fieldAutT_fixes_J k _ σ hQσ hext hσk ⟨x, rfl⟩
  have hsub1 : ((incl k hext).range.map Θ.symm.toMonoidHom) ≤ ι.range := by
    apply UnitaryPilot.le_range_toPSL_of_le_fixedSubgroup hU
    · rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map Θ.symm.toMonoidHom) hJ
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change θ (Θ.symm (incl k hext x)) = Θ.symm (incl k hext x)
      rw [hθfix, hJfix]
  have hsub2 : ι.range.map Θ.toMonoidHom ≤ (incl k hext).range := by
    have h1 : ⁅ι.range.map Θ.toMonoidHom, ι.range.map Θ.toMonoidHom⁆ =
        ι.range.map Θ.toMonoidHom := by
      rw [← Subgroup.map_commutator, commutator_range_toPSL_four hU]
    change _ ≤ subfieldDerivedImage k hext
    rw [← hcore]
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ h1
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    change σs (Θ (ι y)) = Θ (ι y)
    rw [← hΘθ, UnitaryPilot.graphFieldAut_toPSL]
  have hrange' : (Θ.symm.toMonoidHom.comp (incl k hext)).range = ι.range := by
    apply le_antisymm
    · rw [MonoidHom.range_comp]
      exact hsub1
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hsub2 ⟨ι y, ⟨y, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      change Θ.symm (incl k hext x) = ι y
      rw [hx]
      exact Θ.symm_apply_apply (ι y)
  have hinj' : Function.Injective (Θ.symm.toMonoidHom.comp (incl k hext)) :=
    Θ.symm.injective.comp hιinj
  let lam : matrixProjectiveDerived (coordinateQuadMinus (2 + 1) k (by omega) b c) ≃*
      CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 4 :=
    ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange')).trans
      (MonoidHom.ofInjective (UnitaryPilot.toPSL_injective hU)).symm
  have hlam : ∀ x, ι (lam x) = Θ.symm (incl k hext x) := by
    intro x
    have h1 := (MonoidHom.ofInjective (UnitaryPilot.toPSL_injective hU)).apply_symm_apply
      (MulEquiv.subgroupCongr hrange' (MonoidHom.ofInjective hinj' x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ'', hδ''1, hδ''2⟩ := UnitaryPilot.exists_mulAut_toPSL_comm hU (m := 4) (by norm_num)
    (by omega) (MulAut.congr lam δ⁻¹)
  obtain ⟨δ', hδ'def⟩ : ∃ δ' : MulAut (matrixProjectiveDerived
      (coordinateQuadMinus (2 + 1) F (by omega) (b : F) (c : F))), δ' = MulAut.congr Θ δ'' :=
    ⟨_, rfl⟩
  have hδ' : ∀ x, δ' (incl k hext x) = incl k hext (δ⁻¹ x) := by
    intro x
    rw [hδ'def]
    change Θ (δ'' (Θ.symm (incl k hext x))) = incl k hext (δ⁻¹ x)
    rw [← hlam, hδ''1]
    have h3 : MulAut.congr lam δ⁻¹ (lam x) = lam (δ⁻¹ x) := by
      change lam (δ⁻¹ (lam.symm (lam x))) = lam (δ⁻¹ x)
      rw [MulEquiv.symm_apply_apply]
    rw [h3, hlam, MulEquiv.apply_symm_apply]
  have hσsθ : MulAut.congr Θ θ = σs := by
    ext x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    change Θ (θ (Θ.symm (Θ y))) = σs (Θ y)
    rw [MulEquiv.symm_apply_apply, hΘθ]
  have hδ'c : Commute δ' σs := by
    rw [← hσsθ, hδ'def]
    exact hδ''2.map (MulAut.congr Θ).toMonoidHom
  refine ⟨ψ₁.trans δ', fun a => ?_, ?_⟩
  · have h3 : ψ₁ (ε a) = ε' (j a) := by
      rw [hε']
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [MulEquiv.trans_apply, h3, ← hδ, hδ']
    exact congrArg (incl k hext) (MulAut.inv_apply_self _ δ (j a))
  · have h4 : MulAut.congr (ψ₁.trans δ') τ = δ' * MulAut.congr ψ₁ τ * δ'⁻¹ :=
      MulEquiv.ext fun _ => rfl
    rw [h4, hψ₁τ, hδ'c.eq, mul_assoc, mul_inv_cancel, mul_one]

end Normalize

end CFSG.SeitzReduction.OmegaPilot
