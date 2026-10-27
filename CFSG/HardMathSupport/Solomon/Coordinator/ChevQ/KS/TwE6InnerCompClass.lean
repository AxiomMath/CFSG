module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompFrames
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompStd
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqA2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoSLOBIn

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint TwE6UniqAbs CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups Matrix

namespace TwE6InnerAbs

set_option maxRecDepth 100000

section Class


theorem class_isLieQuot_of_inner {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq2 : S.D.q = 2) (hρ : ∀ γ, S.ρ γ = -γ)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (hin : rootChar a CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) TwE6TwoInnerCompIndex := by
  classical
  have h3 : ((3 : ℕ) : L) ≠ 0 := natCast_three_ne_zero_of_charTwo
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hcl⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hB := kc_innerTypes m0 m1 m2 m3 m4 m5 hsum (inner_mod_three hζ hchar hin)
    (exists_ne_zero_of_ne_one hζ hchar h1)
  unfold kcInnerB at hB
  have hx' := List.all_eq_true.1 hB x hx
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hx'
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hstab : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i := fun γ hγ => by
    rw [hρ]
    exact (isRootComponent_componentRoots i).neg_mem γ hγ
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hstab
  rcases hx' with (h6 | ⟨-, hD4⟩) | ⟨-, hA⟩
  ·
    exfalso
    have hn6 : (componentRoots (rootCharHom a) i).ncard = 6 := by rw [hncard]; exact h6
    have F := kac_facts h3 hap
    obtain ⟨-, himg, -⟩ := outer_componentOrbitLength_spec S hT i
    rw [hs1, Function.iterate_one] at himg
    exact orbit_ne_of_A2_quasisimple S hq2 hT i (F.frame i hn6) (F.glue i hn6) hQS himg
  ·
    have hΨ : componentRoots (rootCharHom a) i =
        (fun α => w⁻¹ • α) '' kacE6.rootsOf (↑sD4 : Set (Option (Fin Tag.E6.rank))) := by
      rw [hroots, hD4]
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      rw [hs1, Function.iterate_one, hΨ]
      exact twistInner_neg_D4 w⁻¹ hρ
    have hfam : componentRoots (rootCharHom a) i =
        rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range lD4) := by
      rw [hΨ, ← range_lD4]
      exact image_rootsOf_eq_rootsOfFam kacE6 w⁻¹ _
    have hmodel := KSExact.rationalComponent_dModel S (Or.inr (Or.inl rfl)) hT i hinner
      (n := 4) (by norm_num) (fun y => w⁻¹ • kacE6.extRoot y)
      (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹) lD4 hfam
      (fun c d hcd h1 h2 => by
        show iform (w⁻¹ • kacE6.extRoot (lD4 c)) (w⁻¹ • kacE6.extRoot (lD4 d)) = 0
        rw [iform_smul, kacE6_extRoot]
        exact d4_hgram c d hcd h1 h2)
      (fun {F} _ c d h => d4_frames w⁻¹ c d h) (r := 2) (e := 1) Nat.prime_two (by norm_num)
      (hq2.trans (pow_one 2).symm)
    rw [hs1, Nat.one_mul] at hmodel
    exact KSExact.isLieQuot_of_D_model hmodel _ fun q hp hf => by
      show IsTwoPow q 1 ∧ 4 = 4
      exact ⟨⟨hp, hf⟩, rfl⟩
  ·
    have hA' : cmpF (zlC m0 m1 m2 m3 m4 m5) x = sA5a ∨ cmpF (zlC m0 m1 m2 m3 m4 m5) x = sA5b ∨
        cmpF (zlC m0 m1 m2 m3 m4 m5) x = sA5c := by
      rcases hA with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨ψ, σ, hψ, -, hr⟩ := frame_of_A5 (L := L) hA' w⁻¹
    have hΨ : componentRoots (rootCharHom a) i = frameRoots σ := hroots.trans hr.symm
    have hπ : ∀ a' b : Fin (5 + 1), a' ≠ b →
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (σ a' b) =
            σ ((Equiv.refl (Fin (5 + 1))) b) ((Equiv.refl (Fin (5 + 1))) a') := by
      intro a' b _
      rw [hs1, Function.iterate_one, hρ]
      exact (hψ.neg a' b).symm
    have hmodel := KSExact.rationalComponent_suN_model S hT i (by norm_num : 3 ≤ 5 + 1) hψ hΨ
      (Equiv.refl _) hπ Nat.prime_two inferInstance (by norm_num : 0 < 1)
      (hq2.trans (pow_one 2).symm) (by rw [hs1]; decide)
    rw [hs1, Nat.one_mul] at hmodel
    exact KSExact.isLieQuot_of_twistedA_model hmodel _ fun q hp hf => by
      show IsTwoPow q 1 ∧ 5 = 5
      exact ⟨⟨hp, hf⟩, rfl⟩

end Class

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
