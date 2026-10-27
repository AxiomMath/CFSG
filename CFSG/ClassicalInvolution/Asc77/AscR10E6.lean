module

public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.LieType.AlgebraicGroups
open CFSG.ClassicalInvolution.Asc77.T3CII (eq_three_of_pow_eq_three ne_two_of_pow_eq_three
  neZero_of_pow_eq_three)
open scoped MatrixGroups commutatorElement



section Descent

variable {p e : ℕ} [Fact p.Prime]

theorem ringHom_eq_of_pow_eq_three (h3 : p ^ e = 3) {L : Type} [Field L]
    (g₁ g₂ : GaloisField p e →+* L) : g₁ = g₂ := by
  obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
  have : CharP (GaloisField 3 1) 3 := inferInstance
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hb := ZMod.castHom_bijective (R := GaloisField 3 1) (n := 3) hcard
  have h : g₁.comp (ZMod.castHom (dvd_refl 3) (GaloisField 3 1)) =
      g₂.comp (ZMod.castHom (dvd_refl 3) (GaloisField 3 1)) := RingHom.ext_zmod _ _
  ext x
  obtain ⟨a, rfl⟩ := hb.2 x
  exact congrArg (fun f : ZMod 3 →+* L => f a) h

theorem mem_rootRankOneGroup_of_baseChange (h3 : p ^ e = 3) {τ : Tag} {θ : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (ι : GaloisField p e →+* GaloisField p (2 * e))
    {z : ModGL τ (GaloisField p e)}
    (hz : baseChangeGL ι z ∈ rootRankOneGroup τ (GaloisField p (2 * e)) θ) :
    z ∈ rootRankOneGroup τ (GaloisField p e) θ := by
  have hne : NeZero e := neZero_of_pow_eq_three h3
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨B, hB⟩ := hz
  obtain ⟨j⟩ := nonempty_ringHom_galoisField_algClos (p := p) (e := e) (2 * e)
  have hcompat : j.comp ι = algebraMap (GaloisField p e) (AlgClosGF p e) :=
    ringHom_eq_of_pow_eq_three h3 _ _
  have h1 : baseChangeGL j (baseChangeGL ι z) =
      baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) z := by
    rw [baseChangeGL_baseChangeGL, hcompat]
  have h2 : baseChangeGL j (rootSL2 τ (GaloisField p (2 * e)) θ B) =
      rootSL2 τ (AlgClosGF p e) θ (Matrix.SpecialLinearGroup.map j B) :=
    baseChangeGL_rootSL2' j θ B
  have h3' : baseChangeGL j (rootSL2 τ (GaloisField p (2 * e)) θ B) =
      baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) z := by
    rw [hB, h1]
  have hfix : entrywiseFrobGL τ (AlgClosGF p e) p e
      (rootSL2 τ (AlgClosGF p e) θ (Matrix.SpecialLinearGroup.map j B)) =
        rootSL2 τ (AlgClosGF p e) θ (Matrix.SpecialLinearGroup.map j B) := by
    rw [← h2, h3']
    exact entrywiseFrobGL_baseChangeGL_algebraMap z
  obtain ⟨A₀, hA₀⟩ := exists_rootSL2_of_frobFixed hθ hp2 hfix
  refine ⟨A₀, ?_⟩
  apply baseChangeGL_injective (algebraMap (GaloisField p e) (AlgClosGF p e))
  rw [← hA₀, ← h2, h3']

end Descent


section Adjoint

variable {p e : ℕ} [Fact p.Prime]

theorem orthBranch_of_adjointEmbedding3 {t : StatedLieTag} {τ : Tag} (h3 : p ^ e = 3)
    (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hadm : StatedLieAdmissible t 0 p e)
    (ψ : (Generic.modelUniv t 0 p e Fact.out).K →* ModGL τ (GaloisField p e))
    (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p e))
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K)
    (hk2 : ∀ x ∈ ψ.ker, x * x = 1)
    (𝒯 : Subgroup (Generic.modelUniv t 0 p e Fact.out).K)
    (hT : ∀ c ∈ 𝒯, ∃ b : Fin τ.rank → (GaloisField p e)ˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ ψ c = rootDiagUnit τ b)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (hsingle : FundamentalSingleClass t (Generic.modelUniv t 0 p e Fact.out).D)
    {Rθ : Subgroup (Generic.modelUniv t 0 p e Fact.out).K}
    (hRθ𝓡 : Rθ ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hRθ : Rθ.map ψ = rootRankOneGroup τ (GaloisField p e) θ)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p (2 * e))ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p (2 * e)) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p (2 * e)) γ → IsLongRoot τ γ) :
    OrthBranch3 p t 0 e := by
  have hne : NeZero e := neZero_of_pow_eq_three h3
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  obtain ⟨ι⟩ : Nonempty (GaloisField p e →+* GaloisField p (2 * e)) := by
    obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
      (K := GaloisField p e) (L := GaloisField p (2 * e))
      (by
        rw [GaloisField.finrank p (NeZero.ne e), GaloisField.finrank p (NeZero.ne _)]
        exact dvd_mul_left e 2)
    exact ⟨f.toRingHom⟩
  have hinj : Function.Injective (baseChangeGL (τ := τ) ι) := baseChangeGL_injective ι
  let ψ' : (Generic.modelUniv t 0 p e Fact.out).K →* ModGL τ (GaloisField p (2 * e)) :=
    (baseChangeGL ι).comp ψ
  have hker' : ∀ x, ψ' x = 1 → ψ x = 1 := fun x hx =>
    hinj (by rw [map_one]; exact hx)
  have hqf : 5 ≤ p ^ (2 * e) := by
    rw [pow_mul', h3]
    norm_num
  refine orthBranch_of_hullEmbedding3 (f := 2 * e) h3 hqf hfund hG2 hD4
    (fun h => absurd h.2 (by norm_num)) hadm ψ'
    (fun x => baseChangeGL_mem_adjointGroup ι (hψ x))
    (fun x hx => hker (hker' x hx)) (fun x hx => hk2 x (hker' x hx)) 𝒯 ?_ hframe
    hsingle hRθ𝓡 hθ ?_ ?_ hlong
  · intro c hc
    obtain ⟨b, hb, hψc⟩ := hT c hc
    refine ⟨fun i => Units.map ι.toMonoidHom (b i), fun i => ?_, ?_⟩
    · rcases hb i with h | h <;> simp [h]
    · change baseChangeGL ι (ψ c) = _
      rw [hψc, baseChangeGL_rootDiagUnit]
  · have hm : Rθ.map ψ' = (Rθ.map ψ).map (baseChangeGL ι) := by
      rw [Subgroup.map_map]
    rw [hm, hRθ]
    rintro _ ⟨y, ⟨A, rfl⟩, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.map ι A, (baseChangeGL_rootSL2' ι θ A).symm⟩
  · rintro y ⟨hy1, ⟨x, rfl⟩⟩
    have hz := mem_rootRankOneGroup_of_baseChange h3 hθ.1 ι (z := ψ x) hy1
    rw [← hRθ] at hz
    obtain ⟨x', hx', hxx⟩ := hz
    exact ⟨x', hx', by simp [ψ', hxx]⟩

end Adjoint

end CFSG.ClassicalInvolution.ModelFacts
