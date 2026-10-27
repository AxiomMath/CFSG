module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksAux
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLOrth
import CFSG.RankThree.PartOne.LIT.McMitchell
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Arf
public import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement Matrix

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section Orth
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem omega_model_of_coords_proof {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q₀ : (ι → ZMod 2) → ZMod 2) {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P]
    [Module (ZMod 2) P] [Finite P]
    {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P} {φ : ↥U₁ →* Multiplicative P}
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1)
    (htr : CFSG.ComponentClassification.OutcomeLocal.IsF2Transvection (ρ (aM K a)))
    {Q : QuadraticForm (ZMod 2) P} (φc : P ≃ₗ[ZMod 2] (ι → ZMod 2)) (hφc : ∀ v, Q₀ (φc v) = Q v)
    (hH : ρ.range = orthGL Q)
    (hL : (K.subgroupOf (Mof K a)).map ρ = ⁅orthGL Q, orthGL Q⁆) :
    OmegaModelWith Q₀ W K a U₁ U₂ := by
  let Θ : LinearMap.GeneralLinearGroup (ZMod 2) P ≃* GL ι (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P).trans
      (CFSG.RankThree.PartOne.LIT.autGL φc)
  have hΘ : ∀ (g : LinearMap.GeneralLinearGroup (ZMod 2) P) (w : P),
      ((Θ g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φc w = φc ((g : P →ₗ[ZMod 2] P) w) := by
    intro g w
    show ((CFSG.RankThree.PartOne.LIT.autGL φc
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P g) : GL ι (ZMod 2)) :
        Matrix ι ι (ZMod 2)) *ᵥ φc w = _
    rw [CFSG.RankThree.PartOne.LIT.autGL_mulVec, LinearEquiv.symm_apply_apply]
    rfl
  have hmatrix : ∀ (A B : GL ι (ZMod 2)), (∀ v : ι → ZMod 2,
      (A : Matrix ι ι (ZMod 2)) *ᵥ v = (B : Matrix ι ι (ZMod 2)) *ᵥ v) → A = B := by
    intro A B hAB
    apply Units.ext
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hAB v)
  obtain ⟨hT1, hT2⟩ := stated_model_of_isometry φc hφc hL
  have hmem : ∀ g ∈ (K.subgroupOf (Mof K a)).map ρ, Θ g ∈ StatedOmega Q₀ := by
    intro g hg
    obtain ⟨A, hA, hAg⟩ := hT1 g hg
    have : Θ g = A := hmatrix _ _ fun v => by
      obtain ⟨w, rfl⟩ := φc.surjective v
      rw [hΘ, hAg]
    rw [this]; exact hA
  have hsurj : ∀ A ∈ StatedOmega Q₀, ∃ g ∈ (K.subgroupOf (Mof K a)).map ρ, Θ g = A := by
    intro A hA
    obtain ⟨g, hg, hAg⟩ := hT2 A hA
    refine ⟨g, hg, hmatrix _ _ fun v => ?_⟩
    obtain ⟨w, rfl⟩ := φc.surjective v
    rw [hΘ, hAg]
  have hmap : ((K.subgroupOf (Mof K a)).map ρ).map Θ.toMonoidHom = StatedOmega Q₀ := by
    ext A
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hmem g hg
    · intro hA
      obtain ⟨g, hg, hgA⟩ := hsurj A hA
      exact ⟨g, hg, hgA⟩
  let incl : ↥K →* ↥(Mof K a) := Subgroup.inclusion (le_sup_left : K ≤ Mof K a)
  have hθmem : ∀ k : ↥K, Θ (ρ (incl k)) ∈ StatedOmega Q₀ := fun k =>
    hmem _ ⟨incl k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  let θ : ↥K →* ↥(StatedOmega Q₀) :=
    ((Θ.toMonoidHom.comp ρ).comp incl).codRestrict _ hθmem
  have hθ : ∀ k : ↥K, ((θ k : ↥(StatedOmega Q₀)) : GL ι (ZMod 2)) = Θ (ρ (incl k)) := fun k => rfl
  let t : GL ι (ZMod 2) := Θ (ρ (aM K a))
  have hQinv : ∀ g ∈ ρ.range, ∀ w, Q ((g : P →ₗ[ZMod 2] P) w) = Q w := by
    intro g hg w
    rw [hH] at hg
    have := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff (Q := Q)
      (f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P g)).1 hg w
    simpa [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using this
  refine ⟨θ, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro A
    obtain ⟨g, ⟨m, hm, rfl⟩, hgA⟩ := hsurj A.1 A.2
    have hmK : (m : X) ∈ K := Subgroup.mem_subgroupOf.1 hm
    refine ⟨⟨m, hmK⟩, Subtype.ext ?_⟩
    rw [hθ]
    exact hgA
  · intro k hk
    apply Subtype.ext
    rw [hθ]
    change Θ (ρ ⟨k, Subgroup.mem_sup_left k.2⟩) = _
    rw [htriv k hk]
    simp
  ·
    obtain ⟨f, a₀, h0, hf, ha₀, hta⟩ :=
      (CFSG.ComponentClassification.OutcomeLocal.isF2Transvection_iff _).1 htr
    refine ⟨φc a₀, f ∘ₗ φc.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
    · intro h1
      apply ha₀
      simpa using h1
    · intro h1
      apply hf
      ext v
      have := LinearMap.congr_fun h1 (φc v)
      simpa using this
    · simpa using h0
    · intro x
      obtain ⟨w, rfl⟩ := φc.surjective x
      have h1 : ((t : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φc w =
          φc ((ρ (aM K a) : P →ₗ[ZMod 2] P) w) := hΘ _ w
      rw [h1, hta, CFSG.ComponentClassification.OutcomeLocal.tv_apply]
      simp
  ·
    intro x
    obtain ⟨w, rfl⟩ := φc.surjective x
    have h1 : ((t : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φc w =
        φc ((ρ (aM K a) : P →ₗ[ZMod 2] P) w) := hΘ _ w
    rw [h1, hφc, hφc]
    exact hQinv _ ⟨aM K a, rfl⟩ w
  ·
    have hn : ρ (aM K a) ∈ Subgroup.normalizer
        ((⁅orthGL Q, orthGL Q⁆ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
          Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) := by
      have := BlocksAux.le_normalizer_commutator (G := orthGL Q) (A := orthGL Q) (B := orthGL Q)
        Subgroup.le_normalizer Subgroup.le_normalizer
      exact this (hH ▸ ⟨aM K a, rfl⟩)
    rw [← hL] at hn
    have := Subgroup.le_normalizer_map Θ.toMonoidHom ⟨ρ (aM K a), hn, rfl⟩
    rw [hmap] at this
    exact this
  ·
    intro k k' hk'
    have e : incl k' = aM K a * incl k * (aM K a)⁻¹ := Subtype.ext (by simp [incl, aM, hk'])
    rw [hθ, hθ, e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  ·
    let ψ : Multiplicative P →* Multiplicative (ι → ZMod 2) :=
      AddMonoidHom.toMultiplicative φc.toAddEquiv.toAddMonoidHom
    refine ⟨ψ.comp φ, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd (φc.symm (Multiplicative.toAdd y)))
      refine ⟨x, ?_⟩
      show Multiplicative.ofAdd (φc (Multiplicative.toAdd (φ x))) = y
      rw [hx]
      simp
    · intro u
      rw [← hd.ker u]
      constructor
      · intro h1
        have := congrArg (fun z => φc.symm (Multiplicative.toAdd z)) h1
        simpa [ψ] using this
      · intro h1
        simp [ψ, h1]
    · intro ℓ u u' hu'
      have h1 := hd.equiv (incl ℓ) u u' hu'
      show Multiplicative.ofAdd (φc (Multiplicative.toAdd (φ u'))) =
        Multiplicative.ofAdd (((θ ℓ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
          φc (Multiplicative.toAdd (φ u)))
      rw [h1, toAdd_ofAdd, hθ, hΘ]

end Orth

section OrthCoords
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem orth_coords_of_perfect {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (Q : QuadraticForm (ZMod 2) P) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hperf : ⁅⁅orthGL Q, orthGL Q⁆, ⁅orthGL Q, orthGL Q⁆⁆ = ⁅orthGL Q, orthGL Q⁆)
    (hnt : ⁅orthGL Q, orthGL Q⁆ ≠ ⊥) :
    ∃ n : ℕ, 1 ≤ n ∧
      ((∃ φ : P ≃ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2),
          ∀ v, StatedQuadPlus (n + 1) (ZMod 2) (φ v) = Q v) ∨
        (∃ φ : P ≃ₗ[ZMod 2] (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → ZMod 2),
          ∀ v, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (φ v) = Q v)) := by
  haveI : FiniteDimensional (ZMod 2) P := Module.Finite.of_finite
  have h3 : 3 ≤ Module.finrank (ZMod 2) P := by
    by_contra hlt
    exact hnt (eq_bot_of_isPerfect_of_finrank_le_two (by omega) _ hperf)
  obtain ⟨ε, m, hstd, hm⟩ := exists_isStdSpace Q (hQ : PolarNondeg Q)
  cases ε
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := hm rfl; omega⟩
    obtain ⟨φ, hφ⟩ := (hstd : IsMinusSpace Q (k + 1))
    have hφ' : ∀ v, StatedQuadMinus (k + 1) (ZMod 2) 1 1 (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hφ v
    have hdim : Module.finrank (ZMod 2) P = k + k + 2 := by
      rw [LinearEquiv.finrank_eq φ, Module.finrank_fintype_fun_eq_card]; simp <;> omega
    exact ⟨k, by omega, Or.inr ⟨φ, hφ'⟩⟩
  · obtain ⟨φ, hφ⟩ := (hstd : IsPlusSpace Q m)
    have hdim : Module.finrank (ZMod 2) P = m + m := by
      rw [LinearEquiv.finrank_eq φ, Module.finrank_fintype_fun_eq_card]; simp <;> omega
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hφ' : ∀ v, StatedQuadPlus (n + 1) (ZMod 2) (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hφ v
    exact ⟨n, by omega, Or.inl ⟨φ, hφ'⟩⟩

end OrthCoords

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
