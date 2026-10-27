module

public import CFSG.RankThree.PartOne.KE6.Phi3A2Case
public import CFSG.RankThree.PartOne.KE6.Phi6A2
public import CFSG.RankThree.PartOne.KE6.Tw6Transport

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_unitary)
open scoped Matrix MatrixGroups Pointwise

section Main

set_option linter.unusedSectionVars false


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem tw6_A2_layer_equiv {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    ∃ (Φ : SL(3, Ω) ≃* SL(3, Ω)),
      Nonempty (↥(rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _)) ≃*
        ↥(fixSubgroup Φ)) ∧
      (∃ H : SL(3, Ω), ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔
        ∃ Y ∈ unitarySet (ℓ ^ f) 3, Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      Finite (fixSubgroup Φ) ∧
      (2 < ℓ ^ f → CFSG.IsQuasisimple (fixSubgroup Φ) ∧
        (∀ x : fixSubgroup Φ, x ∈ Subgroup.center (fixSubgroup Φ) ↔
          ∃ c : Ω, ((x : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) c) ∧
        Nat.card (Subgroup.center (fixSubgroup Φ)) = Nat.gcd 3 (ℓ ^ f + 1) ∧
        Odd (Nat.card (Subgroup.center (fixSubgroup Φ)))) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨π, hπ⟩ := exists_positive_of_conj hL hLT hT
  have hθ : ∀ i j : Fin 3, i ≠ j → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      tw6ThetaConj Ω Fr w (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π j) (π i)) (e * Fr c) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := exists_conj_tw6Theta_pinnedX (Fr := Fr) w
      (chainRoot13_mem_parabolicRoots hij).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ, ← chainRoot_swap]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (tw6ThetaConj Ω Fr w) (tw6ThetaConj_injective w) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, hfin, hq⟩ := sl3_root_permuting_frobenius_fixed_unitary hℓ hf hK
    π Φ b (fun i j hij t => by rw [hΦt, hFr])
  obtain ⟨e, -⟩ := exists_mulEquiv_fixSubgroup_gen (tw6Theta Ω Fr) (tw6ThetaConj Ω Fr w)
    (tw6ThetaConj_conj w) hQ hmaps Φ hΦ₀
  exact ⟨Φ, ⟨e⟩, ⟨H', hH'⟩, hfin, hq⟩

end Main

end CFSG.HardMathSupport.Lang.SeitzPlane
