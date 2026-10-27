module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Lattice (e6T3W)

open CFSG.RankThree.SL3RootPermuting (sl3_root_permuting_frobenius_fixed_unitary)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Frame


abbrev twFrameN (Ω : Type) [Field Ω] (i : Fin 3) : ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω (twE6FrameWeyl i)

@[expose] def twFrame (Ω : Type) [Field Ω] (i : Fin 3) : SL(3, Ω) →* ModGL Tag.E6 Ω :=
  (MulAut.conj (twFrameN Ω i)⁻¹).toMonoidHom.comp (e6rhoA2₁ Ω)

variable {Ω : Type} [Field Ω]

theorem twFrame_apply (i : Fin 3) (X : SL(3, Ω)) :
    twFrame Ω i X = (twFrameN Ω i)⁻¹ * e6rhoA2₁ Ω X * twFrameN Ω i := by
  simp [twFrame, MulAut.conj_apply]

theorem twFrame_injective (i : Fin 3) : Function.Injective (twFrame Ω i) :=
  (MulAut.conj (twFrameN Ω i)⁻¹).injective.comp e6rhoA2₁_injective

theorem twFrame_map (i : Fin 3) :
    (rootSpan Tag.E6 Ω (twE6FrameS i)).map (MulAut.conj (twFrameN Ω i)).toMonoidHom =
      subsystemGroup Tag.E6 Ω support13 := by
  rw [(canonical_weyl_root_transport Tag.E6 Ω).1 _ _ (fun α hα => twE6FrameS_root i hα),
    twE6FrameS_conj i, subsystemGroup_eq_rootSpan]

theorem twFrame_range (i : Fin 3) :
    (twFrame Ω i).range = rootSpan Tag.E6 Ω (twE6FrameS i) := by
  rw [twFrame, MonoidHom.range_comp, e6rhoA2₁_range, ← twFrame_map i]
  exact twLine_map_conj_inv_map _ _

theorem twFrame_mem_rootSpan (i : Fin 3) (X : SL(3, Ω)) :
    twFrame Ω i X ∈ rootSpan Tag.E6 Ω (twE6FrameS i) :=
  twFrame_range (Ω := Ω) i ▸ ⟨X, rfl⟩

theorem exists_twFrame_eq (i : Fin 3) {y : ModGL Tag.E6 Ω}
    (hy : y ∈ rootSpan Tag.E6 Ω (twE6FrameS i)) : ∃ X : SL(3, Ω), twFrame Ω i X = y := by
  rw [← twFrame_range i] at hy
  exact hy

theorem twFrame_torus (i : Fin 3) {m : ModGL Tag.E6 Ω} (hm : m ∈ torusGroup Tag.E6 Ω) :
    ∃ d : Fin 3 → Ωˣ, ∀ X : SL(3, Ω),
      m * twFrame Ω i X * m⁻¹ = twFrame Ω i (conjDiag3 d X) := by
  have hm' : twFrameN Ω i * m * (twFrameN Ω i)⁻¹ ∈ torusGroup Tag.E6 Ω :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer _) m).1 hm
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hm'
  refine ⟨fun j => rootChar b (chainRoot chain13 j 0), fun X => ?_⟩
  have h := (e6Std_frame Ω).torus b X
  change rootDiagUnit Tag.E6 b * e6rhoA2₁ Ω X * (rootDiagUnit Tag.E6 b)⁻¹ =
    e6rhoA2₁ Ω (conjDiag3 (fun j => rootChar b (chainRoot chain13 j 0)) X) at h
  rw [twFrame_apply, twFrame_apply, ← h, ← hb]
  group

theorem twFrame_theta {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    {Fr : Ω →+* Ω} {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (i : Fin 3) :
    ∃ (Φ : SL(3, Ω) ≃* SL(3, Ω)) (Hc : SL(3, Ω)),
      (∀ X, tw6Theta Ω Fr (twFrame Ω i X) = twFrame Ω i (Φ X)) ∧
      ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL Hc * Y *
          (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hℓ : ℓ.Prime := Fact.out
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hT : ∀ β ∈ parabolicRoots Tag.E6 support13,
      (twE6FrameWeyl i * e6T3W * (twE6FrameWeyl i)⁻¹) • β ∈ parabolicRoots Tag.E6 support13 := by
    intro β hβ
    rw [← twE6FrameS_conj i] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, twE6FrameS_stable i hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit (twE6FrameWeyl i)
  obtain ⟨π, hπ⟩ := exists_positive_of_conj hL hLT hT
  have hθ : ∀ a b : Fin 3, a ≠ b → ∃ e : Ω, e * e = 1 ∧ ∀ c : Ω,
      tw6ThetaConj Ω Fr (twE6FrameWeyl i) (pinnedX Tag.E6 Ω (chainRoot chain13 a b) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (π b) (π a)) (e * Fr c) := by
    intro a b hab
    obtain ⟨e, he, h⟩ := exists_conj_tw6Theta_pinnedX (Fr := Fr) (twE6FrameWeyl i)
      (CFSG.RankThree.Classical2.chainRoot13_mem_parabolicRoots hab).1
    refine ⟨e, he, fun c => ?_⟩
    rw [h, hπ, ← chainRoot_swap]
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_reversing_of_theta hFrs
    (tw6ThetaConj Ω Fr (twE6FrameWeyl i)) (tw6ThetaConj_injective (twE6FrameWeyl i)) π hθ
  obtain ⟨-, ⟨H', hH'⟩, -, -, -⟩ := sl3_root_permuting_frobenius_fixed_unitary hℓ hf hk
    π Φ b (fun a b' hab t => by rw [hΦt, hFr])
  refine ⟨Φ, H', fun X => ?_, hH'⟩
  have hΦX : e6rhoA2₁ Ω (Φ X) =
      tw6ThetaConj Ω Fr (twE6FrameWeyl i) (e6rhoA2₁ Ω X) := by
    have h1 := hΦ₀ ((a2Equiv₁ Ω).symm X)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : Φ X = a2Equiv₁ Ω ⟨tw6ThetaConj Ω Fr (twE6FrameWeyl i)
        (((a2Equiv₁ Ω).symm X : subsystemGroup Tag.E6 Ω support13) : ModGL Tag.E6 Ω),
        hmaps _ ((a2Equiv₁ Ω).symm X).2⟩ := by
      apply Subtype.ext
      rw [h1, a2Equiv₁_apply, coe_a2Rep₁]
    change (((a2Equiv₁ Ω).symm (Φ X) : subsystemGroup Tag.E6 Ω support13) :
      ModGL Tag.E6 Ω) = _
    rw [h2, MulEquiv.symm_apply_apply]
    rfl
  rw [twFrame_apply, twFrame_apply, tw6Theta_inv_conj, hΦX]

end Frame

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
