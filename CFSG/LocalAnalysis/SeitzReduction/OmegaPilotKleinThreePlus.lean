module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeMinus
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinatePlusIsometry plusIndexEquiv)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom_val fieldAutT vecIncl
  glIncl mulVec_vecIncl IsExtension)

section PlusKlein

variable (F : Type) [Field F] [CharP F 2]

@[expose] noncomputable def plusKleinIso :
    (coordinateQuadPlus 3 F).IsometryEquiv (quadPlus 3 F) :=
  (coordinatePlusIsometry 3 F).symm

variable {F}

variable (F) [Finite F]

@[expose] noncomputable def plusKleinEquiv :
    LinearFlag.projectiveSL 4 F ≃* matrixProjectiveDerived (coordinateQuadPlus 3 F) :=
  kleinEquivOf (plusKleinIso F)

variable {F}

theorem plusKleinEquiv_fieldAut (σ : F ≃+* F)
    (hQσ : ∀ v, coordinateQuadPlus 3 F (coordinateFieldMap (2 * 3) σ v) =
      σ (coordinateQuadPlus 3 F v))
    (x : LinearFlag.projectiveSL 4 F) :
    plusKleinEquiv F (LinearFlag.fieldAut 4 F σ x) =
      fieldAutT (coordinateQuadPlus 3 F) σ hQσ (plusKleinEquiv F x) :=
  kleinEquivOf_fieldAut _ σ (fun _ => rfl) hQσ x

theorem plusKleinEquiv_projMap (k : Subfield F) [CharP k 2] (x : LinearFlag.projectiveSL 4 k) :
    plusKleinEquiv F (LinearPilot.projMap 4 k.subtype x) =
      incl k (E7Pilot.isExtension_coordinateQuadPlus 3 k) (plusKleinEquiv k x) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 4 k x
  rw [LinearPilot.projMap_proj]
  change matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨kleinRep (plusKleinIso F) _,
      kleinRep_mem _ _⟩) =
    incl k _ (matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨kleinRep (plusKleinIso k) g,
      kleinRep_mem _ _⟩))
  rw [incl_mk]
  congr 1
  apply (derivedEquiv _).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_derivedEquiv, inclHom_val]
  symm
  refine (Pi.basisFun F (Fin (2 * 3))).ext' fun i => ?_
  rw [Pi.basisFun_apply]
  have hsingle := CFSG.RankThree.PartOne.KCOrthogonalSubfield.vecIncl_single k
    (d := 2 * 3) i
  rw [← hsingle]
  change (glIncl k ((derivedEquiv _).symm ⟨kleinRep (plusKleinIso k) g, _⟩).val).val *ᵥ
      vecIncl k (Pi.single i 1) = _
  rw [mulVec_vecIncl]
  have hA : ((derivedEquiv _).symm ⟨kleinRep (plusKleinIso k) g, kleinRep_mem _ _⟩ :
      matrixDerived (coordinateQuadPlus 3 k)).val.val *ᵥ (Pi.single i 1 : Fin (2 * 3) → k) =
        kleinRep (plusKleinIso k) g (Pi.single i 1) := by
    have := coe_derivedEquiv (coordinateQuadPlus 3 k)
      ((derivedEquiv _).symm ⟨kleinRep (plusKleinIso k) g, kleinRep_mem _ _⟩)
    rw [MulEquiv.apply_symm_apply] at this
    have h2 := congrArg (fun φ : (Fin (2 * 3) → k) ≃ₗ[k] (Fin (2 * 3) → k) =>
      φ (Pi.single i 1)) this
    exact h2.symm
  rw [hA]
  show vecIncl k (kleinRep (plusKleinIso k) g (Pi.single i 1)) =
    kleinRep (plusKleinIso F) (SpecialLinearGroup.map k.subtype g) (vecIncl k (Pi.single i 1))
  apply EquivLike.injective (plusKleinIso F)
  rw [kleinRep_apply]
  have h3 := cong_map k.subtype (g : Matrix (Fin 4) (Fin 4) k)
    (plusKleinIso k (Pi.single i 1))
  rw [← kleinRep_apply] at h3
  exact h3.symm

end PlusKlein

section Normalize

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_mulEquiv_comp_eq_incl_three {σ : F ≃+* F} (hσ : orderOf σ = 2) {k : Subfield F}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {Kc : Type} [Group Kc]
    (ψ₀ : Kc ≃* LinearFlag.projectiveSL 4 F) {τ : MulAut Kc} (hτ : τ * τ = 1)
    {A : Type} [Group A] (ε : A →* Kc) (hε : Function.Injective ε)
    (hεθ : ε.range ≤ fixedSubgroup τ)
    (hcomp : CFSG.IsComponent (ε.range.subgroupOf (fixedSubgroup τ)))
    (j : A ≃* matrixProjectiveDerived (coordinateQuadPlus (2 + 1) k)) :
    ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus (2 + 1) F),
      (∀ a, ψ (ε a) = incl k (E7Pilot.isExtension_coordinateQuadPlus (2 + 1) k) (j a)) ∧
      MulAut.congr ψ τ = fieldAutT (coordinateQuadPlus (2 + 1) F) σ
        (E7Pilot.coordinateQuadPlus_fieldMap (2 + 1) σ) := by
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
  set εL : LinearFlag.projectiveSL 4 k →* Kc :=
    (ε.comp j.symm.toMonoidHom).comp (plusKleinEquiv k).toMonoidHom with hεLdef
  have hεL : Function.Injective εL := hε.comp (j.symm.injective.comp (plusKleinEquiv k).injective)
  have hrangeL : εL.range = ε.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(plusKleinEquiv k).symm (j a), ?_⟩
      simp [hεLdef]
  obtain ⟨ψL, hψL1, hψL2⟩ := LinearPilot.exists_mulEquiv_projMap_eq_of_isComponent (n := 4)
    (by norm_num) hf1 hkf k.subtype hσ1 hσσ hfix ψ₀ hτ εL hεL (hrangeL ▸ hεθ)
    (hrangeL ▸ hcomp)
  refine ⟨ψL.trans (plusKleinEquiv F), fun a => ?_, ?_⟩
  · have h1 : ε a = εL ((plusKleinEquiv k).symm (j a)) := by simp [hεLdef]
    rw [MulEquiv.trans_apply, h1, hψL1, plusKleinEquiv_projMap, MulEquiv.apply_symm_apply]
  · ext x
    obtain ⟨y, rfl⟩ := (ψL.trans (plusKleinEquiv F)).surjective x
    change plusKleinEquiv F (ψL (τ ((ψL.trans (plusKleinEquiv F)).symm
      ((ψL.trans (plusKleinEquiv F)) y)))) = _
    rw [MulEquiv.symm_apply_apply, hψL2, plusKleinEquiv_fieldAut σ
      (E7Pilot.coordinateQuadPlus_fieldMap 3 σ)]
    rfl

theorem plusNormalizationThree_of_isComponent :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F), orderOf σ = 2 →
    ∀ (k : Subfield F), (∀ x, x ∈ k ↔ σ x = x) → ∀ f : ℕ, Nat.card k = 2 ^ f →
    ∀ (Kc : Type) [Group Kc] (τ : MulAut Kc), τ * τ = 1 → LieModel Kc .PSL 4 2 (2 * f) →
      (∀ P : Subgroup (fixedSubgroup τ), IsPComponent 2 P → LieModel P .PSL 4 2 f) →
      τ ∉ (MulAut.conj : Kc →* MulAut Kc).range →
    ∀ (A : Type) [Group A] (ε : A →* Kc), Function.Injective ε → ε.range ≤ fixedSubgroup τ →
      CFSG.IsComponent (ε.range.subgroupOf (fixedSubgroup τ)) →
    ∀ j : A ≃* matrixProjectiveDerived (coordinateQuadPlus (2 + 1) k),
      ∃ ψ : Kc ≃* matrixProjectiveDerived (coordinateQuadPlus (2 + 1) F),
        (∀ a, ψ (ε a) = incl k (E7Pilot.isExtension_coordinateQuadPlus (2 + 1) k) (j a)) ∧
        MulAut.congr ψ τ = fieldAutT (coordinateQuadPlus (2 + 1) F) σ
          (E7Pilot.coordinateQuadPlus_fieldMap (2 + 1) σ) := by
  intro F _ _ _ σ hσ k hσk f hkf Kc _ τ hτ hmodel _ _ A _ ε hε hεθ hcomp j
  have hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range k.subtype := fun x => by
    rw [← hσk]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix k.subtype hkf hσ hfix
  obtain ⟨K₁, _, _, hK₁, ⟨e₁⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel
    hmodel
  have : Fintype K₁ := Fintype.ofFinite K₁
  have : Fintype F := Fintype.ofFinite F
  let ρ : K₁ ≃+* F := FiniteField.ringEquivOfCardEq (K := K₁) (K' := F) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₁, hF])
  exact exists_mulEquiv_comp_eq_incl_three hσ hσk (e₁.trans (pslRingCongr ρ 4)) hτ ε hε hεθ
    hcomp j

end Normalize

end CFSG.SeitzReduction.OmegaPilot
