module

public import CFSG.RankThree.PartOne.KGD.D4T36Family
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


section Graph

variable {L : Type} [Field L] {τ : Tag}

theorem conj_mem_rootSpan_of_monomial {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ γ ∈ S, IsRoot τ γ ∧
      weylQuotientHom τ L ⟨n, hn⟩ • γ ∈ S) {g : ModGL τ L} (hg : g ∈ rootSpan τ L S) :
    n * g * n⁻¹ ∈ rootSpan τ L S := by
  have hle : rootSpan τ L S ≤ (rootSpan τ L S).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (hS γ hγ).1
    change n * pinnedX τ L γ c * n⁻¹ ∈ rootSpan τ L S
    rw [hμ c]
    exact pinnedX_mem_rootSpan (hS γ hγ).2 _
  exact hle hg


theorem weyl_inv_smul_neg {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (h : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨n, hn⟩ • v = -v) (v : Fin τ.rank → ℤ) :
    weylQuotientHom τ L ⟨n⁻¹, inv_mem hn⟩ • v = -v := by
  have : (⟨n⁻¹, inv_mem hn⟩ : monomialSubgroup τ L) = (⟨n, hn⟩ : monomialSubgroup τ L)⁻¹ := rfl
  rw [this, map_inv, inv_smul_eq_iff, smul_neg, h, neg_neg]

variable {ρ : SL(3, L) →* ModGL τ L} {σ' : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

theorem exists_graph_action (hρ : IsA2Frame ρ σ') {ω : ModGL τ L} (hω : ω ∈ monomialSubgroup τ L)
    (hωW : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨ω, hω⟩ • v = -v) :
    ∃ (Ψ : SL(3, L) ≃* SL(3, L)) (c : ∀ i j : Fin 3, i ≠ j → Lˣ),
      (∀ X, ω * ρ X * ω⁻¹ = ρ (Ψ X)) ∧
      ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
        Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
          Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * t) := by
  classical
  have hS : ∀ {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L),
      (∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨n, hn⟩ • v = -v) →
      ∀ γ ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ' i j}, IsRoot τ γ ∧
        weylQuotientHom τ L ⟨n, hn⟩ • γ ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ' i j} := by
    rintro n hn hW γ ⟨i, j, hij, rfl⟩
    refine ⟨hρ.isRoot i j hij, ?_⟩
    rw [hW, ← hρ.neg]
    exact ⟨j, i, hij.symm, rfl⟩
  have hmem : ∀ {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L),
      (∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨n, hn⟩ • v = -v) → ∀ X, n * ρ X * n⁻¹ ∈ ρ.range := by
    intro n hn hW X
    rw [hρ.range]
    exact conj_mem_rootSpan_of_monomial hn (hS hn hW) (hρ.range ▸ ⟨X, rfl⟩)
  have hω' := weyl_inv_smul_neg hω hωW
  have h1 := hmem hω hωW
  have h2 := hmem (inv_mem hω) hω'
  let e : SL(3, L) ≃* ρ.range := MonoidHom.ofInjective hρ.injective
  have he : ∀ z : ρ.range, ρ (e.symm z) = (z : ModGL τ L) := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply z)
    simp [e] at this ⊢
  let f : SL(3, L) →* SL(3, L) :=
    e.symm.toMonoidHom.comp (((MulAut.conj ω).toMonoidHom.comp ρ).codRestrict ρ.range h1)
  let g : SL(3, L) →* SL(3, L) :=
    e.symm.toMonoidHom.comp (((MulAut.conj ω⁻¹).toMonoidHom.comp ρ).codRestrict ρ.range
      (fun X => by simpa using h2 X))
  have hf : ∀ X, ρ (f X) = ω * ρ X * ω⁻¹ := fun X => he _
  have hg : ∀ X, ρ (g X) = ω⁻¹ * ρ X * ω⁻¹⁻¹ := fun X => he _
  have hgf : g.comp f = MonoidHom.id _ := by
    refine MonoidHom.ext fun X => hρ.injective ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hg, hf]
    group
  have hfg : f.comp g = MonoidHom.id _ := by
    refine MonoidHom.ext fun X => hρ.injective ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hg, hf]
    group
  choose ε hε using hρ.transv
  choose μ hμ using fun i j (hij : i ≠ j) => monomial_conj_pinnedX hω (hρ.isRoot i j hij)
  refine ⟨f.toMulEquiv g hgf hfg, fun i j hij => (ε j i hij.symm)⁻¹ * μ i j hij * ε i j hij,
    fun X => (hf X).symm, fun i j hij t => ?_⟩
  apply hρ.injective
  have hfe : ρ ((f.toMulEquiv g hgf hfg) (Matrix.SpecialLinearGroup.transvection hij t)) =
      ω * ρ (Matrix.SpecialLinearGroup.transvection hij t) * ω⁻¹ := hf _
  rw [hfe, hε i j hij t, hμ i j hij, hωW, ← hρ.neg, hε j i hij.symm]
  congr 1
  push_cast
  field_simp

end Graph


section Opposition

variable {L : Type} [Field L]

theorem torus_mul_opposition {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    ∃ hω : t * trialityOpposition L ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
        weylQuotientHom TwistTag.D4.tag L ⟨t * trialityOpposition L, hω⟩ • v = -v := by
  have hM : t * trialityOpposition L ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (torusGroup_le_monomialSubgroup ht) trialityOpposition_mem_monomialSubgroup
  refine ⟨hM, fun v => ?_⟩
  have hm : MapsRootLines (t * trialityOpposition L) trialityOppositionWeyl := by
    simpa using (mapsRootLines_of_mem_torusGroup ht).mul mapsRootLines_trialityOpposition
  rw [weylQuotientHom_eq (g := ⟨t * trialityOpposition L, hM⟩) hm]
  exact trialityOppositionWeyl_smul v

theorem exists_graph_action_opposition {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ')
    {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L) :
    ∃ (Ψ : SL(3, L) ≃* SL(3, L)) (c : ∀ i j : Fin 3, i ≠ j → Lˣ),
      (∀ X, (t * trialityOpposition L) * ρ X * (t * trialityOpposition L)⁻¹ = ρ (Ψ X)) ∧
      ∀ (i j : Fin 3) (hij : i ≠ j) (s : L),
        Ψ (Matrix.SpecialLinearGroup.transvection hij s) =
          Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * s) := by
  obtain ⟨hω, hW⟩ := torus_mul_opposition ht
  exact exists_graph_action hρ hω hW

end Opposition

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
