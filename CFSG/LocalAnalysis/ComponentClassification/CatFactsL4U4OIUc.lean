module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUa
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev fixW (A : Matrix (Fin 4) (Fin 4) K) : Submodule h.fixedField (Fin 4 → K) :=
  conjFixed h (((1 : Kˣ) : K) • antiunitaryMap h A)

theorem mem_fixW {A : Matrix (Fin 4) (Fin 4) K} {v : Fin 4 → K} :
    v ∈ fixW h A ↔ A *ᵥ (fun i => h.bar (v i)) = v := by
  change ((1 : Kˣ) : K) • antiunitaryMap h A v = v ↔ _
  rw [Units.val_one, one_smul, antiunitaryMap_apply]

theorem false_of_psl2_fixed (hp2 : p ≠ 2) {X : Type} [Group X]
    (hXm : Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 2 p (2 * f))
    (eP : X ⧸ Subgroup.center X ≃* GorensteinWalter.PSL2 h.fixedField) : False := by
  have : Finite K := h.finite
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hqodd : GorensteinWalter.IsOddPrimePower (Nat.card h.fixedField) :=
    ⟨p, f, h.prime, h.prime.odd_of_ne_two hp2, h.one_le, hK⟩
  have h1 : Nat.card (X ⧸ Subgroup.center X) = Nat.card h.fixedField *
      (Nat.card h.fixedField ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eP.toEquiv]
    exact GorensteinWalter.psl2_card_formula h.fixedField hqodd
  have h2 := AZ.two_mul_card_of_isSec8JType h.prime hp2
    (Or.inl hXm : GSThmB.IsSec8JType _ p f)
  have hq3 : 3 ≤ p ^ f := by
    have : 3 ≤ p := by have := h.prime.two_le; omega
    exact this.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  rw [hK] at h1
  set q := p ^ f with hq
  have h4 : q * (q ^ 2 - 1) % 2 = 0 := by
    have : Even (q * (q ^ 2 - 1)) := by
      rcases Nat.even_or_odd q with he | ho
      · exact he.mul_right _
      · exact (Nat.Odd.sub_odd (ho.pow) odd_one).mul_left _
    exact Nat.even_iff.mp this
  have h6 : q * (q ^ 2 - 1) < q ^ 2 * (q ^ 4 - 1) := by
    have a1 : q < q ^ 2 := by nlinarith
    have a2 : 1 ≤ q ^ 2 - 1 := by
      have : 9 ≤ q ^ 2 := by nlinarith
      omega
    have a3 : q ^ 2 - 1 ≤ q ^ 4 - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1
    calc q * (q ^ 2 - 1) < q ^ 2 * (q ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right a1 a2
      _ ≤ q ^ 2 * (q ^ 4 - 1) := Nat.mul_le_mul_left _ a3
  omega

section Generic

variable {k₀ W G : Type} [Field k₀] [AddCommGroup W] [Module k₀ W] [Group G]

theorem es_apply {Q : QuadraticForm k₀ W} {δ : k₀ˣ} (ψW : W ≃ₗ[k₀] hermitianSubmodule (δ : k₀))
    (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* HermitianIsometries (δ : k₀))
    (he : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : hermitianSubmodule (δ : k₀)),
      (e g).val X = ψW (g.val (ψW.symm X)))
    (d' : HermitianIsometries (δ : k₀)) (w : W) :
    (e.symm d').val w = ψW.symm (d'.val (ψW w)) := by
  apply ψW.injective
  have h1 := he (e.symm d') (ψW w)
  rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
  rw [← h1, LinearEquiv.apply_symm_apply]

theorem mem_iff_of_model {Q : QuadraticForm k₀ W} {δ : k₀ˣ} (h2 : (2 : k₀) ≠ 0)
    (ψW : W ≃ₗ[k₀] hermitianSubmodule (δ : k₀))
    (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* HermitianIsometries (δ : k₀))
    (he : ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : hermitianSubmodule (δ : k₀)),
      (e g).val X = ψW (g.val (ψW.symm X)))
    (hc : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (specialImage (δ : k₀) h2).map e.symm.toMonoidHom)
    (Φ' : G ≃* TauCeti.QuadraticMap.orthogonalGroup Q) {Y : Subgroup G}
    (hYeq : Y.map Φ'.toMonoidHom = commutator (TauCeti.QuadraticMap.orthogonalGroup Q))
    (v : G) :
    v ∈ Y ↔ ∃ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k₀)),
      ∀ w, (Φ' v).val w = ψW.symm (rowOAction δ g (ψW w)) := by
  have hmem : v ∈ Y ↔ Φ' v ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← hYeq]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v', hv', hvv⟩
      rw [Φ'.injective hvv] at hv'
      exact hv'
  rw [hmem, hc]
  constructor
  · rintro ⟨d', ⟨g, rfl⟩, hd'⟩
    refine ⟨g, fun w => ?_⟩
    rw [← hd']
    exact es_apply ψW e he _ w
  · rintro ⟨g, hg⟩
    refine ⟨specialRho (δ : k₀) h2 g, ⟨g, rfl⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change (e.symm (specialRho (δ : k₀) h2 g)).val w = (Φ' v).val w
    rw [es_apply ψW e he, hg]
    rfl

end Generic

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
