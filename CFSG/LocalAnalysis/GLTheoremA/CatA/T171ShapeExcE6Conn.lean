module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcE6ConnDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TKac
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn

theorem eq_one_of_ncard_kernelRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {a : Fin τ.rank → Lˣ}
    (h : (kernelRoots (rootCharHom a)).ncard = τ.rootCount) : a = 1 := by
  have hroot : kernelRoots (rootCharHom a) = {v | IsRoot τ v} := by
    refine Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1) ?_ (finite_setOf_isRoot τ)
    rw [ncard_setOf_isRoot, h]
  have ha : a = 1 := by
    funext j
    have hj : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) := by
      rw [hroot]
      exact isRoot_single τ j
    have h1 : rootChar a (Pi.single j 1) = 1 := hj.2
    have h2 := rootChar_nsmul_single a j 1
    rw [one_smul, pow_one] at h2
    rw [h2] at h1
    exact h1
  exact ha

theorem e6CentralizerConnOdd_holds
    (hsmall : E6CentralizerConnOddExcKernels) : E6CentralizerConnOdd := by
  intro L _ _ _ p₀ S huntw hq3 a hT hap y hyC hyF
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨ζ, w₀, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, -⟩ :=
    kac_class_data h3L hap
  have hcnt := ncard_kernelRoots_eq_cntB hζ w₀ hchar
  have hconn : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 30, 40} : Set ℕ) →
      y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := fun hk => by
    have hW := e6_stab_le_kernelReflectionGroup_of_conn a hap hk
    rw [toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 L a hW] at hyC
    exact hyC
  rcases KD264Lie.X2E6.T.cntB_cases m0 m1 m2 m3 m4 m5 hsum with h18 | h22 | h24 | h30 | h40 | h72
  ·
    exact hsmall L p₀ S huntw hq3 a hT hap (Or.inl (by rw [hcnt]; exact h18)) y hyC hyF
  · exact hconn (by rw [hcnt, h22]; simp)
  ·
    exact hsmall L p₀ S huntw hq3 a hT hap (Or.inr (by rw [hcnt]; exact h24)) y hyC hyF
  · exact hconn (by rw [hcnt, h30]; simp)
  · exact hconn (by rw [hcnt, h40]; simp)
  ·
    have h72n : (kernelRoots (rootCharHom a)).ncard = Tag.E6.rootCount := by
      rw [hcnt.trans h72]
      decide
    have ha1 : a = 1 := eq_one_of_ncard_kernelRoots h72n
    rw [ha1] at hyC ⊢
    have hroot : kernelRoots (rootCharHom (1 : Fin Tag.E6.rank → Lˣ)) =
        {α | IsRoot Tag.E6 α} := by
      ext α
      simp [kernelRoots, rootCharHom, rootChar]
    have hC : toralCentralizer Tag.E6 L (1 : Fin Tag.E6.rank → Lˣ) = adjointGroup Tag.E6 L := by
      rw [toralCentralizer, rootDiagUnit_one, Subgroup.centralizer_singleton_one, inf_top_eq]
    rw [hC, adjointGroup_eq_rootSpan] at hyC
    rw [hroot]
    exact Subgroup.mem_sup_right hyC

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
