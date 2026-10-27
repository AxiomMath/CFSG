module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaEven
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Blueprint

theorem map_oddCoreIn_mulEquiv {G : Type} [Group G] (φ : G ≃* G) (B : Subgroup G) (t : G) :
    (oddCoreIn B t).map φ.toMonoidHom = oddCoreIn (B.map φ.toMonoidHom) (φ t) := by
  set C := B ⊓ centralizer ({t} : Set G) with hC
  set D := B.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G) with hD
  have hCD : C.map φ.toMonoidHom = D := by
    rw [hC, hD, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective]
    congr 1
    ext y
    simp only [mem_map_equiv, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg φ h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using this
    · intro h
      apply φ.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  let e : C ≃* D := (C.equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hCD)
  have hcore := CFSG.pPrimeCore_map_iso 2 e
  rw [oddCoreIn, oddCoreIn, Subgroup.map_map, ← hC, ← hD, ← hcore, Subgroup.map_map]
  rfl

variable {K : Type} [Field K] [Finite K]

theorem d4_triality_reduction (hT1 : BurgoyneD4TrialityConjInput)
    (hT2 : BurgoyneD4TrialityOddCoreInput) (hK : ringChar K ≠ 2)
    {B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hB : (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range ≤ B)
    {t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (htB : t ∈ B)
    (ht : orderOf t = 2) :
    ∃ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      α * t * α⁻¹ ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) ∧
      ∀ y ∈ oddCoreIn B t, α * y * α⁻¹ ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
  obtain ⟨α, hα⟩ := hT1 K hK t ht
  set φ := MulAut.conj α with hφ
  have hφy : ∀ y, φ y = α * y * α⁻¹ := fun y => rfl
  have hB' : (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))).range ≤
      B.map φ.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj (α⁻¹ x), hB ⟨_, rfl⟩, ?_⟩
    change α * MulAut.conj (α⁻¹ x) * α⁻¹ = MulAut.conj x
    ext y
    simp [MulAut.conj_apply]
  have ht'B : φ t ∈ B.map φ.toMonoidHom := ⟨t, htB, rfl⟩
  have ht' : orderOf (φ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  have hcore := hT2 K hK _ hB' (φ t) ht'B ht' hα
  refine ⟨α, hα, fun y hy => hcore ?_⟩
  rw [← map_oddCoreIn_mulEquiv]
  exact ⟨y, hy, rfl⟩

theorem burgoynePropA_POmegaPlus4 (hT1 : BurgoyneD4TrialityConjInput)
    (hT2 : BurgoyneD4TrialityOddCoreInput) (X : Type) [Group X] [Finite X] (hX : IsM4 X)
    {p f : ℕ} (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaPlus 4 p f)
    (t : X) (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinatePlus hmod K hKc e
    set θ₀ := coordinatePlusWitnessEquiv K e with hθ₀
    have hψ₀ := socleAction_injective hsimple hnab θ₀
    obtain ⟨α, hαt, hαY⟩ := d4_triality_reduction hT1 hT2 hK (B := (socleAction θ₀).range)
      (by rintro _ ⟨y, rfl⟩; exact conj_mem_range_socleAction _ y) ⟨t, rfl⟩
      (by rw [orderOf_injective _ hψ₀ t]; exact ht)
    have hfam := coordinate_plus_family_eq_matrixImage hmod K hKc e
    have hsemi : ∀ β ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K),
        ∃ g : similarityPairs (coordinateQuadPlus 4 K), β = oκ _ g := by
      intro β hβ
      rw [hfam] at hβ
      obtain ⟨g, hg⟩ := hβ
      exact ⟨g, hg.symm⟩
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus 4 K)
      (regular_coordinateQuadPlus 4 K (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * 4)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadPlus 4 K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    set θ := (θ₀.trans α).trans (oTransport 1 1 hS₁) with hθ
    have key : ∀ x, socleAction θ x =
        MulAut.congr (oTransport 1 1 hS₁) (α * socleAction θ₀ x * α⁻¹) := fun x => by
      ext y
      rfl
    obtain ⟨g₁, hg₁⟩ := hsemi (α * socleAction θ₀ t * α⁻¹) hαt
    have hg : socleAction θ t = oκ _ (transPair 1 1 hS₁ g₁) :=
      calc socleAction θ t = MulAut.congr (oTransport 1 1 hS₁) (α * socleAction θ₀ t * α⁻¹) :=
            key t
        _ = MulAut.congr (oTransport 1 1 hS₁) (oκ _ g₁) := congrArg _ hg₁
        _ = oκ _ (transPair 1 1 hS₁ g₁) := oTransport_kappa 1 1 hS₁ g₁
    have hsurj : OSurjX θ t := by
      intro x hx
      have hmem : socleAction θ₀ x ∈ oddCoreIn (socleAction θ₀).range (socleAction θ₀ t) := by
        rw [← map_oddCentralizerCore_of_injective hψ₀]
        exact ⟨x, hx, rfl⟩
      obtain ⟨g, hgx⟩ := hsemi _ (hαY _ hmem)
      exact ⟨transPair 1 1 hS₁ g, (key x).trans ((congrArg _ hgx).trans
        (oTransport_kappa 1 1 hS₁ g))⟩
    by_cases hσ : (transPair 1 1 hS₁ g₁).val.right = 1
    · exact inner_even_propAConclusion hK hp hKc le_rfl hR hker hsimple hnab θ hsurj ht hσ hg
        hY hYO
    · exact field_propAConclusion hK (by omega) hp hf hKc hR hker hsimple hnab θ hsurj ht hσ hg
        hY hYO
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.O
