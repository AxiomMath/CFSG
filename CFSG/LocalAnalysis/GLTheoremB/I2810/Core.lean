module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreLattice
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreRep
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreSection
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreOrth
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreAlt
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreClifford
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreAltSix
import CFSG.LocalAnalysis.GLTheoremB.I2810.Induced

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Core
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem trans_lattice (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a) :
    ∃ (u : X) (U₁ U₂ : Subgroup X), TLattice K (vOf W K S) a u U₁ U₂ :=
  trans_lattice_proof h hR haS ha2 htr

theorem trans_sectionM_of_lattice (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (ha2 : a ^ 2 = 1) {u : X} {U₁ U₂ : Subgroup X}
    (hl : TLattice K (vOf W K S) a u U₁ U₂) : TransSectionM K (vOf W K S) U₁ U₂ a :=
  trans_sectionM_of_lattice_proof h hR haS ha2 hl (K_eq_comm h hR haS hna)

theorem kirred_of_irredM {a : X} {K V U₁ U₂ : Subgroup X} (hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K)
    (hV : IsElemAbelian 2 V) (hts : TransSectionM K V U₁ U₂ a) :
    SingleFactor K V U₁ U₂ := kirred_of_irredM_proof hKa hV hts

theorem secRep_exists (K : Subgroup X) (a : X) (ha2 : a ^ 2 = 1) (hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K)
    (U₁ U₂ : Subgroup X) (hel : IsElemAbelian 2 U₁) (hle : U₂ ≤ U₁)
    (hK₁ : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁) (hK₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ ∈ U₂)
    (ha₁ : ∀ x ∈ U₁, a * x * a⁻¹ ∈ U₁) (ha₂ : ∀ x ∈ U₂, a * x * a⁻¹ ∈ U₂) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module (ZMod 2) P) (_ : Finite P)
      (ρ : ↥(K ⊔ Subgroup.zpowers a) →* LinearMap.GeneralLinearGroup (ZMod 2) P)
      (φ : ↥U₁ →* Multiplicative P), SecRepData (K ⊔ Subgroup.zpowers a) U₁ U₂ ρ φ :=
  secRep_exists_proof K a U₁ U₂ hel hle hK₁ hK₂ ha₁ ha₂

theorem rho_triv_of_W (h : Setup28 W K S) (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hU : U₁ ≤ vOf W K S) {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    {ρ : ↥(K ⊔ Subgroup.zpowers a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hd : SecRepData (K ⊔ Subgroup.zpowers a) U₁ U₂ ρ φ) :
    ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1 :=
  rho_triv_of_W_proof hR hU hd

theorem outer_rho (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) {U₁ U₂ : Subgroup X} (hts : TransSection K (vOf W K S) U₁ U₂ a)
    (hout : ¬ IndInner W K a) {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) (φ : ↥U₁ →* Multiplicative P)
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ) :
    ρ (aM K a) ∉ (K.subgroupOf (Mof K a)).map ρ :=
  outer_rho_proof h hR haS hts hout ρ φ hd

theorem shape_hyps (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (ha2 : a ^ 2 = 1) {U₁ U₂ : Subgroup X}
    (hts : TransSection K (vOf W K S) U₁ U₂ a)
    {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) (φ : ↥U₁ →* Multiplicative P)
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ)
    (hρ : ρ (aM K a) ∉ (K.subgroupOf (Mof K a)).map ρ) :
    ShapeHyp ρ.range ((K.subgroupOf (Mof K a)).map ρ) ∧ IsF2Transvection (ρ (aM K a)) ∧
      ρ (aM K a) ∈ Subgroup.normalizer
        (((K.subgroupOf (Mof K a)).map ρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
          Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) :=
  shape_hyps_proof h hR haS ha2 hts ρ φ hd hρ (K_eq_comm h hR haS hna)

theorem orth_coords {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (Q : QuadraticForm (ZMod 2) P) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hperf : ⁅⁅orthGL Q, orthGL Q⁆, ⁅orthGL Q, orthGL Q⁆⁆ = ⁅orthGL Q, orthGL Q⁆)
    (hnt : ⁅orthGL Q, orthGL Q⁆ ≠ ⊥) :
    ∃ n : ℕ, 1 ≤ n ∧
      ((∃ φ : P ≃ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2),
          ∀ v, StatedQuadPlus (n + 1) (ZMod 2) (φ v) = Q v) ∨
        (∃ φ : P ≃ₗ[ZMod 2] (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2),
          ∀ v, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (φ v) = Q v)) :=
  orth_coords_of_perfect Q hQ hperf hnt

theorem omega_model_of_coords {ι : Type} [Fintype ι] [DecidableEq ι] (Q₀ : (ι → ZMod 2) → ZMod 2)
    {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P} {φ : ↥U₁ →* Multiplicative P}
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1)
    (htr : IsF2Transvection (ρ (aM K a))) {Q : QuadraticForm (ZMod 2) P}
    (φc : P ≃ₗ[ZMod 2] (ι → ZMod 2)) (hφc : ∀ v, Q₀ (φc v) = Q v)
    (hH : ρ.range = orthGL Q)
    (hL : (K.subgroupOf (Mof K a)).map ρ = ⁅orthGL Q, orthGL Q⁆) :
    OmegaModelWith Q₀ W K a U₁ U₂ :=
  omega_model_of_coords_proof Q₀ hd htriv htr φc hφc hH hL

theorem sym_isAlt {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} (hsym : SymSpShape H)
    (hL : L = ⁅H, H⁆) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) : ∃ m : ℕ, 5 ≤ m ∧ IsAltModel L m :=
  sym_isAlt_of_perfect hsym hL hperf hL1

theorem isAlt_transv_swap_ne6 {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (hA : IsAltModel L m) {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    AltSwapConcl L m τ := isAlt_transv_swap_ne6_proof hm hm6 hA hτ hτn

theorem isAlt_transv_swap_six {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)}
    (hA : IsAltModel L 6) {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    AltSwapConcl L 6 τ := isAlt_transv_swap_six_proof hA hτ hτn

theorem altModel_of_isAlt {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P]
    [Module (ZMod 2) P] [Finite P]
    {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P} {φs : ↥U₁ →* Multiplicative P}
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φs)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1) {m : ℕ} (hm : 5 ≤ m)
    (σ : Equiv.Perm (Fin m)) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
    (θ : ↥((K.subgroupOf (Mof K a)).map ρ) ≃* ↥(alternatingGroup (Fin m))) (hσ : σ.IsSwap)
    (hφ : ∀ (g : ↥((K.subgroupOf (Mof K a)).map ρ)) (w : P)
      (x : CFSG.QuasithinUnique.evenWeight m), φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
            CFSG.RankThree.PartTwo.altHeart m))
    (hσθ : ∀ g g' : ↥((K.subgroupOf (Mof K a)).map ρ),
      (g' : LinearMap.GeneralLinearGroup (ZMod 2) P) = ρ (aM K a) * g * (ρ (aM K a))⁻¹ →
        (θ g' : Equiv.Perm (Fin m)) = σ * (θ g : Equiv.Perm (Fin m)) * σ⁻¹) :
    AltModel W K a U₁ U₂ :=
  altModel_of_isAlt_proof hd htriv hm σ φ θ hσ hφ hσθ

end Core

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
