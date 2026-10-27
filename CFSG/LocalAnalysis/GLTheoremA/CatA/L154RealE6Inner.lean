module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6Abs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6Diag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.RankThree.PartOne.KE6.E6LNormal
public import CFSG.RankThree.PartOne.KE6.E6LStdIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenCenterQuot LargeEvenChevH
  LargeEvenChevIDImage LargeEvenChevGL LargeEvenIsRoot LargeEvenCartanE LargeEvenLabel
  LargeEvenLieTag LargeEvenRawDatum LargeEvenRecipeChevalley)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.RecipeExcLang

theorem l154_chev_untransport {τ : Tag} {K : Type} [Field K]
    {Q : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : Q (LargeEvenCenterQuot (adjointGroup τ K))
      (markIDImage (IsRoot τ) K (adjointGroup τ K))) :
    Q (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have h1 : ∀ S : (Fin τ.rank → ℤ) → Prop, LargeEvenIsRoot τ.cartan = S →
      Q (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false))
        (markIDImage S K (MarkChev.chevH τ.cartan S K false)) →
      Q (LargeEvenCenterQuot (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false))
        (markIDImage (LargeEvenIsRoot τ.cartan) K
          (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false)) := by
    intro S hS
    subst hS
    exact id
  have h2 := h1 (IsRoot τ) (largeEvenIsRoot_eq_isRoot τ) (by
    rw [chevH_false_eq_adjointGroup]
    exact h)
  have h3 : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      Q (LargeEvenCenterQuot H) (markIDImage (LargeEvenIsRoot τ.cartan) K H) →
      Q (LargeEvenCenterQuot H) (LargeEvenChevIDImage τ.cartan K H) := by
    intro H hH hQ
    rw [largeEvenChevIDImage_eq]
    exact hQ
  exact h3 _ (largeEvenChevH_eq τ.cartan K false) (by
    rw [largeEvenChevH_eq]
    exact h2)

section Inner

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {K : Type} [Field K] [Finite K]

theorem l154_inner_hI {φ : MulAut (LargeEvenCenterQuot (adjointGroup Tag.E6 K))}
    (hφ : φ ∈ markIDImage (IsRoot Tag.E6) K (adjointGroup Tag.E6 K)) :
    ∃ (α : MulAut ↥(adjointGroup Tag.E6 K)) (Wq : ModGL τ K),
      (∀ c, QuotientGroup.mk (α c) = φ (QuotientGroup.mk c)) ∧
      Wq ∈ Subgroup.normalizer (subsystemGroup τ K (e6Set τ) : Set (ModGL τ K)) ∧
      ∀ q q' : ↥(subsystemGroup τ K (e6Set τ)),
        Wq * (q : ModGL τ K) * Wq⁻¹ = (q' : ModGL τ K) → e6Ad τ K q' = α (e6Ad τ K q) := by
  obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ
  refine ⟨autEquiv Tag.E6 K φ, ?_⟩
  obtain ⟨w, b, j, hj, rfl⟩ := w
  obtain ⟨q₀, hq₀⟩ := e6Ad_surjective (τ := τ) (k := K) ⟨j, hj⟩
  refine ⟨rootDiagUnit τ (e6DiagExt b) * (q₀ : ModGL τ K), fun c => autEquiv_apply φ c,
    Subgroup.mul_mem _ (rootDiagUnit_mem_normalizer_subsystemGroup _ _)
      (Subgroup.le_normalizer q₀.2), ?_⟩
  intro q q' hqq
  have hq' : q' = diagConj τ K (e6DiagExt b) (q₀ * q * q₀⁻¹) := by
    apply Subtype.ext
    rw [← hqq, coe_diagConj]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
  rw [hw, hq']
  apply Subtype.ext
  rw [e6Ad_diagConj, coe_inndiagConj, map_mul, map_mul, map_inv, hq₀]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]

theorem l154_realizedMarking_inner {M : Type} [Group M] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {j : ModGL τ K →* M} (hj : Function.Injective j)
    (hX : CFSG.IsQuasisimple ↥((subsystemGroup τ K (e6Set τ)).map j)) :
    L154RealizedMarking ((subsystemGroup τ K (e6Set τ)).map j) := by
  obtain ⟨hqC, θ, hθ⟩ := l154_realized_of_map hj hX (e6Ad τ K) e6Ad_surjective e6Ad_ne_one
    (I := markIDImage (IsRoot Tag.E6) K (adjointGroup Tag.E6 K))
    fun φ hφ => l154_inner_hI hφ
  refine ⟨hX.1.commutator_eq_top, ⟨.E6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  exact l154_chev_untransport (τ := Tag.E6)
    (Q := fun R _ I => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ' : ↥((subsystemGroup τ K (e6Set τ)).map j) ⧸
          Subgroup.center ↥((subsystemGroup τ K (e6Set τ)).map j) ≃* R,
        ∀ φ ∈ I, ∃ w ∈ Subgroup.normalizer (((subsystemGroup τ K (e6Set τ)).map j :
            Subgroup M) : Set M),
          LargeEvenInduces θ' (fun r r' : ↥((subsystemGroup τ K (e6Set τ)).map j) =>
            w * (r : M) * w⁻¹ = (r' : M)) φ)
    ⟨hqC.2.1, hqC.2.2, θ, hθ⟩

end Inner

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
