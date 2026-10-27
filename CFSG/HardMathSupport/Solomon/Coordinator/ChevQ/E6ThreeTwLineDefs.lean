module

public import CFSG.HardMathSupport.Lang.SeitzPlane.TwE6FrameData
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Tw6Transport

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Lang.SeitzPlane
open scoped MatrixGroups

set_option linter.unusedSectionVars false

@[expose] def twLineChar {Ω : Type} [Field Ω] (ω : Ωˣ) : Fin Tag.E6.rank → Ωˣ :=
  ![ω ^ 2, ω, 1, 1, ω, 1]

@[expose] def twLineWord : List (Fin Tag.E6.rank) := [0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 2, 1]

@[expose] def twLineWeyl : WeylGroup Tag.E6 :=
  (twLineWord.map (simple Tag.E6)).prod

section Psi


@[expose] def twLinePsi (K : Type) [Field K] (g₀ : ModGL Tag.E6 (AlgebraicClosure K)) :
    ModGL TwistTag.E6.tag K →* ModGL Tag.E6 (AlgebraicClosure K) :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp
    (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))

theorem twLinePsi_apply {K : Type} [Field K] (g₀ : ModGL Tag.E6 (AlgebraicClosure K))
    (x : ModGL TwistTag.E6.tag K) :
    twLinePsi K g₀ x =
      g₀⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) x * g₀ := by
  change g₀⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) x * g₀⁻¹⁻¹ = _
  rw [inv_inv]

theorem twLinePsi_injective (K : Type) [Field K] (g₀ : ModGL Tag.E6 (AlgebraicClosure K)) :
    Function.Injective (twLinePsi K g₀) :=
  (MulAut.conj g₀⁻¹).injective.comp (baseChangeGL_injective _)

end Psi

section Line


structure TwE6ThreeA2Picture (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g₀ : ModGL Tag.E6 (AlgebraicClosure K))
    (h₀ : ModGL TwistTag.E6.tag K) (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K))
    (T : Subgroup (ModGL TwistTag.E6.tag K)) (n : ModGL TwistTag.E6.tag K) : Prop where
  card_eq : Nat.card K = q ^ 2
  σ_apply : ∀ c, σ c = c ^ q
  Fr_apply : ∀ c, Fr c = c ^ q
  g₀_mem : g₀ ∈ adjointGroup Tag.E6 (AlgebraicClosure K)
  g₀_lang : twistE6 (AlgebraicClosure K) Fr g₀ = g₀ * tw6N (AlgebraicClosure K)
  psi_mem : ∀ x ∈ twistedE6RootGroup K σ,
    twLinePsi K g₀ x ∈ adjointGroup Tag.E6 (AlgebraicClosure K)
  psi_fixed : ∀ x ∈ twistedE6RootGroup K σ,
    tw6Theta (AlgebraicClosure K) Fr (twLinePsi K g₀ x) = twLinePsi K g₀ x
  perfect_le : ∀ P : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)), Finite P →
    P ≤ adjointGroup Tag.E6 (AlgebraicClosure K) →
    (∀ x ∈ P, tw6Theta (AlgebraicClosure K) Fr x = x) → ⁅P, P⁆ = P →
    P ≤ (twistedE6RootGroup K σ).map (twLinePsi K g₀)
  h₀_image : ∃ ω : (AlgebraicClosure K)ˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧
    twLinePsi K g₀ h₀ = rootDiagUnit Tag.E6 (twLineChar ω)
  mem_L : ∀ i x, x ∈ L i ↔ x ∈ twistedE6RootGroup K σ ∧
    twLinePsi K g₀ x ∈ rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS i)
  L_image : ∀ i, (L i).map (twLinePsi K g₀) =
    rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS i) ⊓
      (tw6Theta (AlgebraicClosure K) Fr).eqLocus (MonoidHom.id _)
  L_model : ∀ i, ∃ Φ : SL(3, AlgebraicClosure K) ≃* SL(3, AlgebraicClosure K),
    Nonempty (L i ≃* CFSG.RankThree.Classical2.fixSubgroup Φ) ∧
    ∃ H : SL(3, AlgebraicClosure K), ∀ X : SL(3, AlgebraicClosure K),
      X ∈ CFSG.RankThree.Classical2.fixSubgroup Φ ↔
        ∃ Y ∈ CFSG.RankThree.Classical2.unitarySet q 3, Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹
  mem_T : ∀ x, x ∈ T ↔ x ∈ twistedE6RootGroup K σ ∧
    twLinePsi K g₀ x ∈ torusGroup Tag.E6 (AlgebraicClosure K)
  n_image : ∃ t ∈ torusGroup Tag.E6 (AlgebraicClosure K),
    twLinePsi K g₀ n = canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twLineWeyl * t

structure TwE6ThreeA2Line (K : Type) [Field K] (σ : K ≃+* K) (h₀ : ModGL TwistTag.E6.tag K)
    (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)) (T : Subgroup (ModGL TwistTag.E6.tag K))
    (n : ModGL TwistTag.E6.tag K) : Prop where
  h₀_mem : h₀ ∈ twistedE6RootGroup K σ
  h₀_pow : h₀ ^ 3 = 1
  h₀_ne : h₀ ≠ 1
  finrank_fixed : Module.finrank K
    (LinearMap.ker ((h₀ : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24
  L_le : ∀ i, L i ≤ twistedE6RootGroup K σ
  L_finite : ∀ i, Finite (L i)
  L_quasisimple : ∀ i, CFSG.IsQuasisimple (L i)
  L_center : ∀ i, Nat.card (Subgroup.center (L i)) = 3
  L_center_eq : ∀ i, Subgroup.center (L i) = (Subgroup.zpowers h₀).subgroupOf (L i)
  h₀_mem_L : ∀ i, h₀ ∈ L i
  L_commute : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x
  T_le : T ≤ twistedE6RootGroup K σ
  T_comm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x
  h₀_mem_T : h₀ ∈ T
  T_le_normalizer : ∀ i, T ≤ Subgroup.normalizer (L i : Set (ModGL TwistTag.E6.tag K))
  n_mem : n ∈ twistedE6RootGroup K σ
  n_conj : ∀ i, (L i).map (MulAut.conj n).toMonoidHom = L (i + 1)
  centralizer_eq : twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} =
    (T ⊔ ⨆ i, L i) ⊔ Subgroup.zpowers n
  centralizer_mul : ∀ g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀},
    ∃ t ∈ T, ∃ l₀ ∈ L 0, ∃ l₁ ∈ L 1, ∃ l₂ ∈ L 2, ∃ k < 3, g = t * l₀ * l₁ * l₂ * n ^ k
  conj_shift : ∀ g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀}, ∃ k : Fin 3,
    ∀ i, (L i).map (MulAut.conj g).toMonoidHom = L (i + k)
  shift_zero : ∀ g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀},
    (∀ i, (L i).map (MulAut.conj g).toMonoidHom = L i) → g ∈ T ⊔ ⨆ i, L i
  le_normalizer : twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} ≤
    Subgroup.normalizer
      ((⨆ i, L i : Subgroup (ModGL TwistTag.E6.tag K)) : Set (ModGL TwistTag.E6.tag K))
  picture : ∃ (q : ℕ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g₀ : ModGL Tag.E6 (AlgebraicClosure K)), TwE6ThreeA2Picture K σ q Fr g₀ h₀ L T n

end Line

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
