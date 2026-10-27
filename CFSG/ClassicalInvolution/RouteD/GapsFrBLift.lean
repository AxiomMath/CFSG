module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOddNormalized
public import CFSG.ClassicalInvolution.RouteD.GapsFrOdd
public import CFSG.ClassicalInvolution.RouteD.GapsFrBWeight
public import CFSG.ClassicalInvolution.RouteD.GapsFrBEigen
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBRecognition
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.Tri
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.ModelFacts.OrthAut
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (picB)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (isCompl_eigenspace_of_mul_self)
open scoped Matrix MatrixGroups

section Defs

variable {m : ℕ} {F : Type} [Field F] {X : Type} [Group X]

@[expose] def OddToralProp (θ : spinGroup (quadOdd m F) →* X) (σ : X ≃* X)
    (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2) : Prop :=
  ∀ γ : Fin m → ℤ, γ ∈ (oddDatum m F).roots →
    ((((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
      (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ ∧
    ((∀ y ∈ (((oddDatum m F).rootGroup γ ⊔ (oddDatum m F).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
      ∑ i, (γ i : ZMod 2) * v i = 0)

@[expose] def OddLift (α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F))
    (v : Fin m → ZMod 2) : Prop :=
  ∃ (g₀ : (Fin m ⊕ Fin m ⊕ Unit → F) ≃ₗ[F] (Fin m ⊕ Fin m ⊕ Unit → F)) (t : ℕ → ZMod 2),
    g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m F) ∧ g₀ * g₀ = 1 ∧
    (∀ y z, spinAction (quadOdd m F) (α y) (g₀ z) = g₀ (spinAction (quadOdd m F) y z)) ∧
    v = picB m t ∧
    Module.finrank F ↥(Module.End.eigenspace (g₀ : Module.End F (Fin m ⊕ Fin m ⊕ Unit → F)) 1) =
      1 + 2 * (Finset.univ.filter fun i : Fin m => t i.val = 0).card

end Defs

section Diagonal

variable {m : ℕ} {F : Type} [Field F]

local notation "𝕍" => (Fin m ⊕ Fin m ⊕ Unit → F)

theorem exists_lift_of_diagonal (h2 : (2 : F) ≠ 0)
    {α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F)} {g : SemiSim (quadOdd m F)}
    (hα : IsConj α g) (hφ : ∀ c, g.φ c = c) (κ : spinGroup (quadOdd m F)) (ζ : F) (hζ0 : ζ ≠ 0)
    (hζ2 : ζ * ζ = (g.μ : F)) (ε : Fin m ⊕ Fin m ⊕ Unit → F) (hε : ∀ c, ε c = 1 ∨ ε c = -1)
    (hE : ∀ c, g.conjSpin κ (Pi.single c 1) = (ζ * ε c) • (Pi.single c 1 : 𝕍))
    (S : Finset (Fin m ⊕ Fin m ⊕ Unit)) (hS : ∀ c, c ∈ S ↔ ε c = 1) :
    ∃ g₀ : 𝕍 ≃ₗ[F] 𝕍,
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m F) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadOdd m F) (α y) (g₀ z) = g₀ (spinAction (quadOdd m F) y z)) ∧
      Module.finrank F ↥(Module.End.eigenspace (g₀ : Module.End F 𝕍) 1) = S.card := by
  classical
  have hne : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hεε : ∀ c, ε c * ε c = 1 := fun c => by
    rcases hε c with h | h <;> simp [h]
  have hφ' : ∀ c, (g.conjSpin κ).φ c = c := hφ
  let gL : 𝕍 →ₗ[F] 𝕍 := (g.conjSpin κ).toLinear hφ'
  let Dm : 𝕍 →ₗ[F] 𝕍 := ζ⁻¹ • gL
  have hD : ∀ c, Dm (Pi.single c 1) = ε c • (Pi.single c 1 : 𝕍) := fun c => by
    simp only [Dm, gL, LinearMap.smul_apply, SemiSim.toLinear_apply, hE c, smul_smul]
    rw [← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
  have hDD' : Dm ∘ₗ Dm = LinearMap.id := by
    refine (Pi.basisFun F (Fin m ⊕ Fin m ⊕ Unit)).ext fun c => ?_
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, hD, map_smul, smul_smul, hεε,
      LinearMap.id_apply, one_smul]
  have hDD : ∀ x, Dm (Dm x) = x := fun x => by
    simpa using LinearMap.congr_fun hDD' x
  let DmE : 𝕍 ≃ₗ[F] 𝕍 := LinearEquiv.ofLinearMap Dm Dm hDD' hDD'
  let g₀ : 𝕍 ≃ₗ[F] 𝕍 :=
    (spinAction (quadOdd m F) κ⁻¹).trans (DmE.trans (spinAction (quadOdd m F) κ))
  have hg₀ : ∀ x, g₀ x = spinAction (quadOdd m F) κ (Dm (spinAction (quadOdd m F) κ⁻¹ x)) :=
    fun x => rfl
  have hgζ : ∀ x, g x = ζ • g₀ x := by
    intro x
    have e1 : g (spinAction (quadOdd m F) κ (spinAction (quadOdd m F) κ⁻¹ x)) =
        spinAction (quadOdd m F) κ ((g.conjSpin κ) (spinAction (quadOdd m F) κ⁻¹ x)) := by
      simp only [SemiSim.conjSpin_apply, spinAction_apply_inv]
    rw [spinAction_apply_inv] at e1
    have e2 : (g.conjSpin κ) (spinAction (quadOdd m F) κ⁻¹ x) =
        ζ • Dm (spinAction (quadOdd m F) κ⁻¹ x) := by
      simp only [Dm, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      rfl
    rw [e1, e2, map_smul, hg₀]
  have hiso : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m F) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    have h1 := g.map_Q x
    rw [hgζ x, QuadraticMap.map_smul, hφ, ← hζ2] at h1
    have hζζ : ζ * ζ ≠ 0 := mul_ne_zero hζ0 hζ0
    have h3 : (ζ * ζ) * (quadOdd m F) (g₀ x) = (ζ * ζ) * (quadOdd m F) x := by
      simpa [smul_eq_mul] using h1
    exact mul_left_cancel₀ hζζ h3
  have hsq : g₀ * g₀ = 1 := by
    refine LinearEquiv.ext fun x => ?_
    simp only [LinearEquiv.mul_apply, hg₀, spinAction_inv_apply, hDD, spinAction_apply_inv]
    rfl
  have hconj : ∀ y z, spinAction (quadOdd m F) (α y) (g₀ z) =
      g₀ (spinAction (quadOdd m F) y z) := by
    intro y z
    have h := hα y z
    rw [hgζ z, hgζ (spinAction (quadOdd m F) y z), map_smul] at h
    exact smul_right_injective _ hζ0 h
  refine ⟨g₀, hiso, hsq, hconj, ?_⟩
  have hcompl : IsCompl (Module.End.eigenspace Dm 1) (Module.End.eigenspace Dm (-1)) :=
    isCompl_eigenspace_of_mul_self h2 (T := Dm) (by
      rw [Module.End.mul_eq_comp]
      exact hDD')
  have hsum : Module.finrank F ↥(Module.End.eigenspace Dm 1) +
      Module.finrank F ↥(Module.End.eigenspace Dm (-1)) = Module.finrank F 𝕍 :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hV : Module.finrank F 𝕍 = Fintype.card (Fin m ⊕ Fin m ⊕ Unit) :=
    Module.finrank_fintype_fun_eq_card F
  set Sm := Finset.univ.filter fun c : Fin m ⊕ Fin m ⊕ Unit => ε c = -1 with hSm
  have hcard : S.card + Sm.card = Fintype.card (Fin m ⊕ Fin m ⊕ Unit) := by
    have hS' : S = Finset.univ.filter fun c : Fin m ⊕ Fin m ⊕ Unit => ε c = 1 := by
      ext c
      simp [hS c]
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m ⊕ Fin m ⊕ Unit)))
      (fun c => ε c = 1)
    have hs : (Finset.univ.filter fun c : Fin m ⊕ Fin m ⊕ Unit => ¬ ε c = 1) = Sm := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hSm]
      rcases hε c with h | h <;> simp [h, hne, hne.symm]
    rw [hs, Finset.card_univ] at h
    rw [hS']
    exact h
  have hlow : ∀ (T : Finset (Fin m ⊕ Fin m ⊕ Unit)) (e : F), (∀ c ∈ T, ε c = e) →
      T.card ≤ Module.finrank F ↥(Module.End.eigenspace Dm e) := by
    intro T e hT
    have hli : LinearIndependent F
        (fun c : T => (Pi.single (c : Fin m ⊕ Fin m ⊕ Unit) (1 : F) : 𝕍)) := by
      have h0 := (Pi.basisFun F (Fin m ⊕ Fin m ⊕ Unit)).linearIndependent.comp
        (fun c : T => (c : Fin m ⊕ Fin m ⊕ Unit)) Subtype.val_injective
      have e : (⇑(Pi.basisFun F (Fin m ⊕ Fin m ⊕ Unit)) ∘ fun c : T =>
          (c : Fin m ⊕ Fin m ⊕ Unit)) =
          fun c : T => (Pi.single (c : Fin m ⊕ Fin m ⊕ Unit) (1 : F) : 𝕍) :=
        funext fun c => by simp [Pi.basisFun_apply]
      rwa [e] at h0
    have hspan := finrank_span_eq_card hli
    have hle : Submodule.span F
        (Set.range fun c : T => (Pi.single (c : Fin m ⊕ Fin m ⊕ Unit) (1 : F) : 𝕍)) ≤
        Module.End.eigenspace Dm e := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hD, hT c c.2]
    have := Submodule.finrank_mono hle
    rw [hspan, Fintype.card_coe] at this
    exact this
  have hp := hlow S 1 (fun c hc => (hS c).mp hc)
  have hm' := hlow Sm (-1) (fun c hc => by simpa [hSm] using hc)
  have heq : Module.finrank F ↥(Module.End.eigenspace Dm 1) = S.card := by omega
  rw [← heq]
  have hmap : Module.End.eigenspace (g₀ : Module.End F 𝕍) 1 =
      (Module.End.eigenspace Dm 1).map (spinAction (quadOdd m F) κ : 𝕍 →ₗ[F] 𝕍) := by
    ext x
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_map, one_smul]
    constructor
    · intro hx
      refine ⟨spinAction (quadOdd m F) κ⁻¹ x, ?_, spinAction_apply_inv _ _⟩
      rw [Module.End.mem_eigenspace_iff, one_smul]
      have : spinAction (quadOdd m F) κ (Dm (spinAction (quadOdd m F) κ⁻¹ x)) = x := hx
      have h2' := congrArg (spinAction (quadOdd m F) κ⁻¹) this
      rwa [spinAction_inv_apply] at h2'
    · rintro ⟨y, hy, rfl⟩
      rw [Module.End.mem_eigenspace_iff, one_smul] at hy
      show spinAction (quadOdd m F) κ (Dm (spinAction (quadOdd m F) κ⁻¹
        (spinAction (quadOdd m F) κ y))) = spinAction (quadOdd m F) κ y
      rw [spinAction_inv_apply, hy]
  rw [hmap]
  exact LinearEquiv.finrank_map_eq (spinAction (quadOdd m F) κ) _

end Diagonal

section Tail

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem toralNormal_odd_of_diag_lift (hp2 : p ≠ 2) {m : ℕ} (h2 : (2 : F) ≠ 0)
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup (quadOdd m F)), ζ ^ p = 1 → ζ = 1)
    {X : Type} [Group X] (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F))) (σ : X ≃* X)
    {α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F)} {g : SemiSim (quadOdd m F)}
    (hα : IsConj α g) (hαθ : ∀ y, θ (α y) = σ (θ y)) (hα2 : ∀ y, α (α y) = y)
    (κ : spinGroup (quadOdd m F)) (lam : Fin m → Bool → F) (hφ : ∀ c, g.φ c = c)
    (hprod : ∀ i, lam i true * lam i false = g.μ)
    (hg₂ : ∀ i s, g.conjSpin κ ((oddFrame m F).vec i s) = lam i s • (oddFrame m F).vec i s)
    (hCpres : ∀ y : Fin m ⊕ Fin m ⊕ Unit → F,
      (∀ a r, polar (quadOdd m F) y ((oddFrame m F).vec a r) = 0) →
        ∀ a r, polar (quadOdd m F) (g.conjSpin κ y) ((oddFrame m F).vec a r) = 0)
    (hdiag : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      α (κ * (oddFrame m F).longRoot hij s t (.ofAdd c) * κ⁻¹) =
        κ * (oddFrame m F).longRoot hij s t
          (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹) :
    ∃ (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      OddToralProp θ σ k₀ v ∧ OddLift α v := by
  classical
  set Fr := oddFrame m F with hFr
  have hzorth : ∀ a r, polar (quadOdd m F) Fr.z (Fr.vec a r) = 0 := fun a r => by
    rw [polar_comm]
    exact Fr.polar_vec_z a r
  obtain ⟨ζ, hζ⟩ := odd_orth_eq_smul_z m (fun a r => hCpres Fr.z hzorth a r)
  have hζ2 : ζ * ζ = (g.μ : F) := by
    have h1 := (g.conjSpin κ).map_Q Fr.z
    rw [hζ, QuadraticMap.map_smul, Fr.map_z] at h1
    change (ζ * ζ) • (1 : F) = (g.μ : F) * g.φ 1 at h1
    simpa using h1
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hζ0 : ζ ≠ 0 := fun h0 => hμ0 (by rw [← hζ2, h0, zero_mul])
  have hlam2 : ∀ k s, lam k (!s) * lam k s = (g.μ : F) := by
    intro k s
    cases s
    · simpa using hprod k
    · simpa [mul_comm] using hprod k
  have hlam0 : ∀ k s, lam k s ≠ 0 := fun k s h0 => hμ0 (by rw [← hlam2 k s, h0, mul_zero])
  let a : Fin m → Fˣ := fun k => Units.mk0 (lam k true / ζ) (div_ne_zero (hlam0 k true) hζ0)
  have hlamζ : ∀ k s, lam k s = ζ * (a k : F) ^ boolSign s := by
    intro k s
    have h0 := hlam0 k true
    cases s
    · simp only [boolSign_false, a, Units.val_mk0, zpow_neg, zpow_one]
      have hp := hprod k
      rw [← hζ2] at hp
      field_simp
      linear_combination hp
    · simp only [boolSign_true, a, Units.val_mk0, zpow_one]
      field_simp
  set A := conjTwist α κ with hAdef
  have hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹ := fun y => by
    rw [hAdef, conjTwist_apply]
    group
  have hA2 : ∀ y, A (A y) = y := conjTwist_sq α hα2 κ
  have hAlong : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
      A (Fr.longRoot hij s t (.ofAdd c)) =
        Fr.longRoot hij s t (.ofAdd ((lam j t * ((g.μ : F)⁻¹ * lam i s)) * c)) := by
    intro i j hij s t c
    have h1 := hdiag i j hij s t c
    rw [hA] at h1
    rw [mul_left_cancel (mul_right_cancel h1)]
    congr 2
    ring
  have hα₂c : IsConj A (g.conjSpin κ) := hα.conjSpin κ
  have hAshort : ∀ (i : Fin m) (s : Bool) (c : F),
      A (Fr.shortRoot i s (.ofAdd c)) =
        Fr.shortRoot i s (.ofAdd ((lam i s * ((g.μ : F)⁻¹ * ζ)) * c)) := by
    intro i s c
    have h3 := IsConj.shortRoot_eq hp2 (odd_hker2 h2 m) Fr hα₂c lam (fun _ s => s) hg₂ ζ hζ i s c
    have hφc : (g.conjSpin κ).φ c = c := hφ c
    have hμc : (((g.conjSpin κ).μ : Fˣ) : F) = (g.μ : F) := rfl
    rw [h3, hφc, hμc]
    congr 2
    ring
  have hχL2 : ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool),
      (lam j t * ((g.μ : F)⁻¹ * lam i s)) * (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 :=
    fun i j hij s t => sq_eq_one_of_scalar A hA2 (Fr.longRoot hij s t)
      (Fr.longRoot_injective hij s t) _ (hAlong i j hij s t)
  have hχS2 : ∀ (i : Fin m) (s : Bool),
      (lam i s * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 :=
    fun i s => sq_eq_one_of_scalar A hA2 (Fr.shortRoot i s) (Fr.shortRoot_injective i s) _
      (hAshort i s)
  have hψlong : ∀ (γ : Fin m → ℤ) (i j : Fin m) (s t : Bool),
      toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam j t * ((g.μ : F)⁻¹ * lam i s) := by
    intro γ i j s t h
    rw [charPsiB_long a s t h, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, hlamζ i s, hlamζ j t, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    have haj : (a j : F) ≠ 0 := (a j).ne_zero
    field_simp
  have hψshort : ∀ (γ : Fin m → ℤ) (i : Fin m) (s : Bool),
      toStdB m γ = Pi.single i (boolSign s) →
        ((charPsiB a (Multiplicative.ofAdd γ) : Fˣ) : F) = lam i s * ((g.μ : F)⁻¹ * ζ) := by
    intro γ i s h
    rw [charPsiB_short a s h, Units.val_zpow_eq_zpow_val, hlamζ i s, ← hζ2]
    have hai : (a i : F) ≠ 0 := (a i).ne_zero
    field_simp
  have hψ1 : ∀ a₀ : Fin m, charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = 1 ∨
      charPsiB a (Multiplicative.ofAdd (Pi.single a₀ 1)) = -1 := by
    intro a₀
    by_cases hlt : a₀.val + 1 < m
    · have hkj : a₀ ≠ ⟨a₀.val + 1, hlt⟩ := Fin.ne_of_val_ne (by simp)
      have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) +
          Pi.single (⟨a₀.val + 1, hlt⟩ : Fin m) (boolSign false) := by
        rw [toStdB_single_of_lt m hlt, boolSign_true, boolSign_false, Pi.single_neg,
          sub_eq_add_neg]
      have h1 := hψlong _ _ _ true false hrep
      have h2' := hχL2 _ _ hkj true false
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
    · have hrep : toStdB m (Pi.single a₀ 1) = Pi.single a₀ (boolSign true) := by
        rw [toStdB_single_of_not_lt m hlt, boolSign_true]
      have h1 := hψshort _ _ true hrep
      have h2' := hχS2 a₀ true
      rw [← h1] at h2'
      rcases mul_self_eq_one_iff.mp h2' with h3 | h3
      · exact Or.inl (Units.ext (by rw [h3, Units.val_one]))
      · exact Or.inr (Units.ext (by rw [h3, Units.val_neg, Units.val_one]))
  obtain ⟨v, hv⟩ := exists_vec_of_hom h2 (charPsiB a) hψ1
  have hroot : OddToralProp θ σ κ v := by
    intro γ hγ
    rcases odd_root_cases hγ with ⟨i, j, hij, s, t, hstd⟩ | ⟨i, s, hstd⟩
    · have hX1 : (oddDatum m F).rootGroup γ = (Fr.longRoot hij s t).range :=
        oddRootGroup_eq_long hij s t hstd
      have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) + Pi.single j (boolSign (!t)) := by
        have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
        rw [e, hstd, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]
      have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.longRoot hij (!s) (!t)).range :=
        oddRootGroup_eq_long hij (!s) (!t) hstd'
      rw [hX1, hX2]
      have hχ : lam j t * ((g.μ : F)⁻¹ * lam i s) = 1 →
          lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s)) = 1 := by
        intro h1
        have hprod' : (lam j (!t) * ((g.μ : F)⁻¹ * lam i (!s))) *
            (lam j t * ((g.μ : F)⁻¹ * lam i s)) = 1 := by
          calc _ = (lam j (!t) * lam j t) * (lam i (!s) * lam i s) *
                ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by ring
            _ = (g.μ : F) * (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) := by rw [hlam2, hlam2]
            _ = 1 := by field_simp
        rw [h1, mul_one] at hprod'
        exact hprod'
      have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
        (Fr.longRoot hij s t) (Fr.longRoot hij (!s) (!t)) (Fr.longRoot_injective hij s t)
        (fun c => longRoot_pow_char Fr.toHypFrame hij s t c) _ _ (hAlong i j hij s t)
        (hAlong i j hij (!s) (!t)) hχ
      refine ⟨hmain.1, ?_⟩
      rw [hmain.2, ← hv γ, Units.ext_iff, hψlong γ i j s t hstd, Units.val_one]
    · have hX1 : (oddDatum m F).rootGroup γ = (Fr.shortRoot i s).range :=
        oddRootGroup_eq_short i s hstd
      have hstd' : toStdB m (-γ) = Pi.single i (boolSign (!s)) := by
        have e : toStdB m (-γ) = -toStdB m γ := toStdB_neg m γ
        rw [e, hstd, boolSign_not, Pi.single_neg]
      have hX2 : (oddDatum m F).rootGroup (-γ) = (Fr.shortRoot i (!s)).range :=
        oddRootGroup_eq_short i (!s) hstd'
      rw [hX1, hX2]
      have hχ : lam i s * ((g.μ : F)⁻¹ * ζ) = 1 → lam i (!s) * ((g.μ : F)⁻¹ * ζ) = 1 := by
        intro h1
        have hprod' : (lam i (!s) * ((g.μ : F)⁻¹ * ζ)) * (lam i s * ((g.μ : F)⁻¹ * ζ)) = 1 := by
          calc _ = (lam i (!s) * lam i s) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (ζ * ζ) := by ring
            _ = (g.μ : F) * ((g.μ : F)⁻¹ * (g.μ : F)⁻¹) * (g.μ : F) := by rw [hlam2, hζ2]
            _ = 1 := by field_simp
        rw [h1, mul_one] at hprod'
        exact hprod'
      have hmain := normalizes_and_fixes_of_scalar hZ θ hker σ α A κ hαθ hA hA2
        (Fr.shortRoot i s) (Fr.shortRoot i (!s)) (Fr.shortRoot_injective i s)
        (fun c => shortRoot_pow_char Fr i s c) _ _ (hAshort i s) (hAshort i (!s)) hχ
      refine ⟨hmain.1, ?_⟩
      rw [hmain.2, ← hv γ, Units.ext_iff, hψshort γ i s hstd, Units.val_one]
  refine ⟨κ, v, hroot, ?_⟩
  have ha2 : ∀ k, (a k : F) * (a k : F) = 1 := by
    intro k
    have h1 := hχS2 k true
    rw [hlamζ k true, ← hζ2] at h1
    simp only [boolSign_true, zpow_one] at h1
    have e : ζ * (a k : F) * ((ζ * ζ)⁻¹ * ζ) = (a k : F) := by field_simp
    rw [e] at h1
    exact h1
  have hu : ∀ k, a k = 1 ∨ a k = -1 := by
    intro k
    rcases mul_self_eq_one_iff.mp (ha2 k) with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  let ε : Fin m ⊕ Fin m ⊕ Unit → F :=
    Sum.elim (fun i => (a i : F)) (Sum.elim (fun i => (a i : F)) (fun _ => (1 : F)))
  have hε : ∀ c, ε c = 1 ∨ ε c = -1 := by
    rintro (i | i | ⟨⟩)
    · rcases hu i with h | h
      · left; simp [ε, h]
      · right; simp [ε, h]
    · rcases hu i with h | h
      · left; simp [ε, h]
      · right; simp [ε, h]
    · left; simp [ε]
  have hainv : ∀ k, (a k : F)⁻¹ = (a k : F) := fun k => inv_eq_of_mul_eq_one_right (ha2 k)
  have hE : ∀ c, g.conjSpin κ (Pi.single c 1) =
      (ζ * ε c) • (Pi.single c 1 : Fin m ⊕ Fin m ⊕ Unit → F) := by
    rintro (i | i | ⟨⟩)
    · have h := hg₂ i true
      simp only [hFr, oddFrame_vec, oddVec_true] at h
      rw [h, hlamζ i true]
      simp [ε]
    · have h := hg₂ i false
      simp only [hFr, oddFrame_vec, oddVec_false] at h
      rw [h, hlamζ i false]
      simp [ε, boolSign_false, zpow_neg, hainv]
    · have h := hζ
      simp only [hFr, oddFrame_z, oddZ] at h
      simp only [h, ε]
      simp
  classical
  obtain ⟨g₀, hiso, hsq, hconj, hdim⟩ := exists_lift_of_diagonal h2 hα hφ κ ζ hζ0 hζ2 ε hε hE
    (Finset.univ.filter fun c => ε c = 1) (fun c => by simp)
  let t : ℕ → ZMod 2 := fun k => if h : k < m then (if a ⟨k, h⟩ = 1 then 0 else 1) else 0
  have ht : ∀ i : Fin m, t i.val = if a i = 1 then 0 else 1 := fun i => by
    simp [t, i.isLt]
  have hne1 : (1 : Fˣ) ≠ -1 := fun h => h2 (by
    have := congrArg Units.val h
    simp only [Units.val_one, Units.val_neg] at this
    linear_combination this)
  have key1 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  refine ⟨g₀, t, hiso, hsq, hconj, ?_, ?_⟩
  · funext j
    have hj := hv (Pi.single j 1)
    have hsum : ∑ i, (((Pi.single j (1 : ℤ) : Fin m → ℤ) i : ℤ) : ZMod 2) * v i = v j := by
      simp [Pi.single_apply]
    rw [hsum] at hj
    simp only [picB]
    by_cases hlt : j.val + 1 < m
    · have hrep : toStdB m (Pi.single j 1) = Pi.single j (boolSign true) +
          Pi.single (⟨j.val + 1, hlt⟩ : Fin m) (boolSign false) := by
        rw [toStdB_single_of_lt m hlt, boolSign_true, boolSign_false, Pi.single_neg,
          sub_eq_add_neg]
      have hc := charPsiB_long a true false hrep
      rw [boolSign_true, boolSign_false, zpow_one, zpow_neg_one] at hc
      have hjv : v j = 0 ↔ a j = a ⟨j.val + 1, hlt⟩ := by
        rw [← hj, hc, mul_inv_eq_one]
      simp only [hlt, ↓reduceIte]
      rw [ht j, show t (j.val + 1) = t (⟨j.val + 1, hlt⟩ : Fin m).val from rfl,
        ht ⟨j.val + 1, hlt⟩]
      rcases hu j with h1 | h1 <;> rcases hu ⟨j.val + 1, hlt⟩ with h2' | h2'
      · have : v j = 0 := hjv.mpr (h1.trans h2'.symm)
        simp [h1, h2', this]
      · have : v j ≠ 0 := fun h => by
          have := hjv.mp h
          rw [h1, h2'] at this
          exact hne1 this
        simp [h1, h2', hne1.symm, key1 _ this]
      · have : v j ≠ 0 := fun h => by
          have := hjv.mp h
          rw [h1, h2'] at this
          exact hne1 this.symm
        simp [h1, h2', hne1.symm, key1 _ this]
      · have : v j = 0 := hjv.mpr (h1.trans h2'.symm)
        simp [h1, h2', this, hne1.symm]
        decide
    · have hrep : toStdB m (Pi.single j 1) = Pi.single j (boolSign true) := by
        rw [toStdB_single_of_not_lt m hlt, boolSign_true]
      have hc := charPsiB_short a true hrep
      rw [boolSign_true, zpow_one] at hc
      have hjv : v j = 0 ↔ a j = 1 := by
        rw [← hj, hc]
      simp only [hlt, ↓reduceIte]
      rw [ht j]
      rcases hu j with h1 | h1
      · have : v j = 0 := hjv.mpr h1
        simp [h1, this]
      · have : v j ≠ 0 := fun h => by
          have := hjv.mp h
          rw [h1] at this
          exact hne1 this.symm
        simp [h1, hne1.symm, key1 _ this]
  · rw [hdim]
    have e1 : (Finset.univ.filter fun c : Fin m ⊕ Fin m ⊕ Unit => ε c = 1).card =
        1 + 2 * (Finset.univ.filter fun i : Fin m => (a i : F) = 1).card := by
      rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [ε, Sum.elim_inl, Sum.elim_inr, ← Finset.card_filter]
      simp
      ring
    have e2 : (Finset.univ.filter fun i : Fin m => t i.val = 0) =
        Finset.univ.filter fun i : Fin m => (a i : F) = 1 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ht i, Units.val_eq_one]
      by_cases h : a i = 1 <;> simp [h]
    rw [e1, e2]


end Tail

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem toralNormal_odd_of_normalized_lift (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {m : ℕ} (hm : 5 ≤ m) {X : Type} [Group X] (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) (s₀ t₀ s₁ t₁ : Bool) (k : spinGroup (quadOdd m F))
    (H1 : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (oddFrame m F).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (oddFrame m F).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) (c : F),
        σ (θ (k * (oddFrame m F).longRoot hab s t (.ofAdd c) * k⁻¹)) =
          θ (k * (oddFrame m F).longRoot hab s t (.ofAdd c) * k⁻¹))
    (H3 : ∀ c : F, ∃ c' : F,
      σ (θ (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹)) =
        θ (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c') * k⁻¹)) :
    ∃ (α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F))
      (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      (∀ x, θ (α x) = σ (θ x)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hZ, -⟩ := odd_center_facts (F := F) hp2 hm3
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_odd hp2 hm3 hf hF θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd m F)) := isPerfect_spinGroup_quadOdd h2 hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadOdd m F) →* _).comp
      (α : spinGroup (quadOdd m F) →* _)) (MonoidHom.id (spinGroup (quadOdd m F))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  set Fr := oddFrame m F with hFr
  have hfix : ∀ {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F),
      σ (θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹)) =
        θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹) →
      conjTwist α k (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd c) :=
    fun hij s t c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k
      (longRoot_pow_char Fr.toHypFrame hij s t c) (longRoot_pow_char Fr.toHypFrame hij s t c) h
  have hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c) := fun c => hfix h01 s₀ t₀ c (H1 c)
  have hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) := fun c => hfix h01.symm (!t₀) (!s₀) c (H1' c)
  obtain ⟨c', hc'⟩ := H3 1
  have hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c') :=
    conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ 1)
      (longRoot_pow_char Fr.toHypFrame hjc s₁ t₁ c') hc'
  have hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ →
      b ≠ c₀ → ∀ (s t : Bool) (c : F), conjTwist α k (Fr.longRoot hab s t (.ofAdd c)) =
        Fr.longRoot hab s t (.ofAdd c) :=
    fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c =>
      hfix hab s t c (H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t c)
  let C : Submodule F (Fin m ⊕ Fin m ⊕ Unit → F) := Submodule.span F {Fr.z}
  have hC : ∀ x : Fin m ⊕ Fin m ⊕ Unit → F,
      (∀ a r, polar (quadOdd m F) x (Fr.vec a r) = 0) → x ∈ C := fun x hx => by
    obtain ⟨c, hc⟩ := odd_orth_eq_smul_z m hx
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hCorth : ∀ x ∈ C, ∀ a r, polar (quadOdd m F) x (Fr.vec a r) = 0 := fun x hx a r => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [polar_smul_left, polar_comm, Fr.polar_vec_z a r, smul_zero]
  have hY : ∀ e ∈ C, ∃ y : spinGroup (quadOdd m F),
      spinAction (quadOdd m F) y = eichler (quadOdd m F) (Fr.vec c₀ s₁) e ∧
      ∀ (i j : Fin m) (hij : i ≠ j), i ≠ c₀ → j ≠ c₀ → ∀ (t t' : Bool) (c : F),
        Commute y (Fr.longRoot hij t t' (.ofAdd c)) := by
    intro e he
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp he
    exact ⟨Fr.shortRoot c₀ s₁ (.ofAdd c), Fr.spinAction_shortRoot_eq_eichler c₀ s₁ c,
      fun i j hij hi hj t t' c₁ =>
        (Fr.commute_longRoot_shortRoot_of_ne hij hi.symm hj.symm t t' s₁ c₁ c).symm⟩
  obtain ⟨k', hk1, hk1', hmul⟩ := exists_adjusted_frame Fr.toHypFrame h01 s₀ t₀ h2 hm C hC hCorth
    hα hα2 k hA1 hA1' hc0 hc1 hj0 hj1 hjc s₁ t₁ hO hN hY
  obtain ⟨κ, lam, hφ, hprod, hg₂, hCpres, hdiag, -⟩ := exists_diag_form_of_diag_compl
    Fr.toHypFrame h01 s₀ t₀ hm3 h2 hp2 (odd_hker2 h2 m) hα hα2 k' hk1 hk1' hmul
  obtain ⟨k₀, v, hr, hl⟩ := toralNormal_odd_of_diag_lift hp2 h2 hZ θ hker σ hα hαθ hα2 κ lam hφ
    hprod hg₂ hCpres hdiag
  exact ⟨α, k₀, v, hαθ, hr, hl⟩

theorem toralNormal_odd_of_normalized_subgroups_lift (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) {m : ℕ} (hm : 5 ≤ m) {X : Type} [Group X]
    (θ : spinGroup (quadOdd m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ c₀ j : Fin m} (h01 : i₀ ≠ i₁) (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀)
    (hj1 : j ≠ i₁) (hjc : c₀ ≠ j) {s₀ t₀ s₁ t₁ : Bool} {γ₀ γ₁ : Fin m → ℤ}
    (hγ₀ : toStdB m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (hγ₁ : toStdB m γ₁ = Pi.single c₀ (boolSign s₁) + Pi.single j (boolSign t₁))
    (k : spinGroup (quadOdd m F))
    (H1 : ∀ y ∈ (((oddDatum m F).rootGroup γ₀ ⊔ (oddDatum m F).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (H2 : ∀ (a b : Fin m), a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) {γ : Fin m → ℤ},
        toStdB m γ = Pi.single a (boolSign s) + Pi.single b (boolSign t) →
          ∀ y ∈ ((oddDatum m F).rootGroup γ).map (MulAut.conj k).toMonoidHom, σ (θ y) = θ y)
    (H3 : ∀ y ∈ ((oddDatum m F).rootGroup γ₁).map (MulAut.conj k).toMonoidHom,
      σ (θ y) ∈ (((oddDatum m F).rootGroup γ₁).map (MulAut.conj k).toMonoidHom).map θ) :
    ∃ (α : spinGroup (quadOdd m F) ≃* spinGroup (quadOdd m F))
      (k₀ : spinGroup (quadOdd m F)) (v : Fin m → ZMod 2),
      (∀ x, θ (α x) = σ (θ x)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  classical
  have hX1 : (oddDatum m F).rootGroup γ₀ = ((oddFrame m F).longRoot h01 s₀ t₀).range :=
    oddRootGroup_eq_long h01 s₀ t₀ hγ₀
  have hstd' : toStdB m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdB m (-γ₀) = -toStdB m γ₀ := toStdB_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (oddDatum m F).rootGroup (-γ₀) =
      ((oddFrame m F).longRoot h01.symm (!t₀) (!s₀)).range :=
    oddRootGroup_eq_long h01.symm (!t₀) (!s₀) hstd'
  have hX3 : (oddDatum m F).rootGroup γ₁ = ((oddFrame m F).longRoot hjc s₁ t₁).range :=
    oddRootGroup_eq_long hjc s₁ t₁ hγ₁
  refine toralNormal_odd_of_normalized_lift hp2 hf hF hm θ hker σ hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc
    s₀ t₀ s₁ t₁ k (fun c => ?_) (fun c => ?_)
    (fun a b hab ha0 ha1 hac hb0 hb1 hbc s t c => ?_) (fun c => ?_)
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩
  · have hγ : toStdB m (ofStdB m (Pi.single a (boolSign s) + Pi.single b (boolSign t))) =
        Pi.single a (boolSign s) + Pi.single b (boolSign t) := toStdB_ofStdB m _
    have hXγ : (oddDatum m F).rootGroup
        (ofStdB m (Pi.single a (boolSign s) + Pi.single b (boolSign t))) =
        ((oddFrame m F).longRoot hab s t).range := oddRootGroup_eq_long hab s t hγ
    refine H2 a b hab ha0 ha1 hac hb0 hb1 hbc s t hγ _ ⟨_, ?_, rfl⟩
    rw [hXγ]
    exact ⟨_, rfl⟩
  · have h1 := H3 (k * (oddFrame m F).longRoot hjc s₁ t₁ (.ofAdd c) * k⁻¹) ⟨_, ?_, rfl⟩
    · obtain ⟨y', ⟨y, hy, rfl⟩, hy'⟩ := h1
      rw [hX3] at hy
      obtain ⟨c', rfl⟩ := hy
      refine ⟨Multiplicative.toAdd c', ?_⟩
      rw [← hy', ofAdd_toAdd]
      rfl
    · rw [hX3]
      exact ⟨_, rfl⟩


end Main

section Chain

variable {p f : ℕ} [Fact p.Prime]

theorem toralNormal_odd_of_frame_chain_lift (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X] (θ : spinGroup (quadOdd (s + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd (s + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    (x : spinGroup (quadOdd (s + 4) (GaloisField p f))) (t : Bool)
    {R : ℕ → Subgroup (spinGroup (quadOdd (s + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd (s + 4) (GaloisField p f)))}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame s (s + 1) (by omega)
      (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame (s + 2) (s + 3)
      (by omega) (by omega) (by omega) true t).map (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (α : spinGroup (quadOdd (s + 4) (GaloisField p f)) ≃*
        spinGroup (quadOdd (s + 4) (GaloisField p f)))
      (k₀ : spinGroup (quadOdd (s + 4) (GaloisField p f)))
      (v : Fin (s + 4) → ZMod 2),
      (∀ x, θ (α x) = σ (θ x)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  classical
  have hm3 : 3 ≤ s + 4 := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadOdd (s + 4) (GaloisField p f))),
      ∃ η : GaloisField p f, ∀ v, spinAction (quadOdd (s + 4) (GaloisField p f)) z v = η • v := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars.mp (spinAction_center_mem_scalars_odd h2 hm3 hz)
    exact ⟨c, hc⟩
  obtain ⟨H1g, H2g, H3g⟩ := frame_chain_fixed_data hs
    (oddFrame (s + 4) (GaloisField p f)).toHypFrame
    θ hker σ hscal x t hR hRtw hRM hfix hfixtw hfixM hnorm0
  let i₀ : Fin (s + 4) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 4) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 4) := ⟨0, by omega⟩
  let jj : Fin (s + 4) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hc0 : c₀ ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, c₀] at this
  have hc1 : c₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, c₀] at this
  have hj0 : jj ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, jj] at this
  have hj1 : jj ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, jj] at this
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  have hγ₀ : toStdB (s + 4) (ofStdB (s + 4) (Pi.single i₀ (boolSign true) +
      Pi.single i₁ (boolSign t))) = Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t) :=
    toStdB_ofStdB _ _
  have hγ₁ : toStdB (s + 4) (ofStdB (s + 4) (Pi.single c₀ (boolSign false) +
      Pi.single jj (boolSign true))) = Pi.single c₀ (boolSign false) +
        Pi.single jj (boolSign true) := toStdB_ofStdB _ _
  refine toralNormal_odd_of_normalized_subgroups_lift hp2 hf hK (m := s + 4) (by omega) θ hker σ hσ2
    hσr h01 hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x ?_ ?_ ?_
  · rw [rootGroup_sup_eq_longSL2_range_odd h01 true t hγ₀]
    exact H1g
  · intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' γ hγ y hy
    have hXγ : (oddDatum (s + 4) (GaloisField p f)).rootGroup γ =
        ((oddFrame (s + 4) (GaloisField p f)).longRoot hab s' t').range :=
      oddRootGroup_eq_long hab s' t' hγ
    rw [hXγ] at hy
    obtain ⟨g, ⟨c, rfl⟩, rfl⟩ := hy
    exact H2g a b hab (fun h => ha0 (Fin.ext h)) (fun h => ha1 (Fin.ext h))
      (fun h => hac (Fin.ext h)) (fun h => hb0 (Fin.ext h)) (fun h => hb1 (Fin.ext h))
      (fun h => hbc (Fin.ext h)) s' t' (Multiplicative.toAdd c)
  · have hXγ₁ : (oddDatum (s + 4) (GaloisField p f)).rootGroup
        (ofStdB (s + 4) (Pi.single c₀ (boolSign false) + Pi.single jj (boolSign true))) =
        ((oddFrame (s + 4) (GaloisField p f)).longRoot hjc false true).range :=
      oddRootGroup_eq_long hjc false true hγ₁
    rw [hXγ₁]
    exact H3g

theorem toralNormal_odd_of_chain_long_lift (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ} {X : Type}
    [Group X]
    (θ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaOdd
      (oddDatum (u + 3 + 4) (GaloisField p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (α : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)) ≃*
        spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))
      (k₀ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))
      (v : Fin (u + 3 + 4) → ZMod 2),
      (∀ x, θ (α x) = σ (θ x)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_odd (m := u + 3 + 4) hp2 hm3 hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd (u + 3 + 4) (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd (u + 3 + 4) (GaloisField p f) h2)
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen hp2 hq hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := u + 3) (by omega)
    (oddFrame (u + 3 + 4) (GaloisField p f)).toHypFrame hdim cq hRf hRtwf hRMf hadj hlin hcomm hM
    hdist hne htwin
  exact toralNormal_odd_of_frame_chain_lift hp2 hq (s := u + 3) (by omega) θ hker σ hσ2 hσr x t hxR
    hxtw hxM hfix hfixtw hfixM hnorm0

end Chain

end CFSG.ClassicalInvolution.RouteD.Gaps
