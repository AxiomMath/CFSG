module

public import CFSG.RankThree.PartOne.KE.E7ThreeA5
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartOne.KA5L.Final

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement Pointwise

variable {L : Type} [Field L]

theorem a5_sigmaFactor_std [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hΩ : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) (h2 : 2 < ℓ ^ f)
    (n : ModGL Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L) (hnC : n ∈ adjointGroup Tag.E7 L)
    (hact : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        weylQuotientHom Tag.E7 L ⟨n, hn⟩ • α = u • ((-1 : ℤ) • α)) :
    SigmaFactor n (iterateFrobenius L ℓ f) (parabolicRoots Tag.E7 (a5Nodes Tag.E7))
      (fun _ : Unit => ⁅rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))),
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))⁆)
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
  classical
  set Γ' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) with hΓ'
  set P' : Subgroup (ModGL Tag.E7 L) := ⁅Γ', Γ'⁆ with hP'
  obtain ⟨hfin, hq, hcent, -⟩ := a5Layer_E7 L ℓ f hf hΩ (-1) (Or.inr rfl) (fun _ => h2) n hn hnC
    hact Γ' P' rfl rfl
  have hnormΓ : ∀ y ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L)),
      y ∈ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
        ∀ γ ∈ Γ', y * γ * y⁻¹ ∈ Γ' := fun y hy hyR γ hγ =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  exact ⟨fun _ => hfin, fun _ => hq,
    fun _ => (commutator_le_self_subgroup Γ').trans inf_le_left,
    fun _ => (commutator_le_self_subgroup Γ').trans inf_le_right,
    fun _ => ((commutator_le_self_subgroup Γ').trans inf_le_left).trans
      (rootSpan_le_adjointGroup L _),
    fun _ y hy hyR u hu => conj_mem_commutator_of_normalizes (hnormΓ y hy hyR) hu,
    fun y hy hc => hcent y hy fun u hu => hc () u hu⟩

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
