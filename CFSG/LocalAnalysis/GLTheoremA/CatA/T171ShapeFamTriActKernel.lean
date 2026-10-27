module


import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped Pointwise commutatorElement MatrixGroups


theorem triKernelCompAction {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) {a : Fin Tag.D4.rank → Lˣ}
    (hT : rootDiagUnit Tag.D4 a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (h1 : rootDiagUnit Tag.D4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {y : ModGL Tag.D4 L}
    (hyZ : y ∈ torusGroup Tag.D4 L ⊔ rootSpan Tag.D4 L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  rcases typeA_frame_cases S hp hT hap h1 i hA with ⟨hr1, hn⟩ | h | h
  · obtain ⟨K, -, -, f, -, hKcard, hfeq, -, hK4, -, -, -⟩ :=
      exists_slCover_rationalComponent_rankOne S hT i hr1 hn hQS
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner :=
      twistKind_eq_inner_of_compRank_eq_one S i hr1
    have hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
      rw [← hfeq, ← hKcard]
      exact hK4
    exact centerQuotientHom_mem_innAutDerived_innerKind_of_four_leT S hT i hkind hQ hyZ hyF
      hyStab
  · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
    have hnorm : ∀ x y, x ≠ y → iform (σf x y) (σf x y) = 2 * 1 := by
      intro x y hxy
      have h := iform_self_simplyLaced (τ := Tag.D4) (Or.inl rfl) (hψ.isRoot x y hxy)
      simpa using h
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
      obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm (κ := 1) one_ne_zero hnorm π
      refine ⟨w, ?_, ?_⟩
      · rw [hΨ]
        exact hw
      · intro γ hγ
        rw [hΨ] at hγ
        obtain ⟨x, y, hxy, rfl⟩ := hγ
        rw [hπ x y hxy, hwσ x y]
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos hinner]
    have hbig : ∃ α ∈ componentRoots (rootCharHom a) i,
        ∃ δ ∈ componentRoots (rootCharHom a) i, δ ≠ α ∧ δ ≠ -α := by
      refine ⟨σf ⟨0, by omega⟩ ⟨1, by omega⟩, ?_,
        σf ⟨0, by omega⟩ ⟨2, by omega⟩, ?_, ?_, ?_⟩
      · rw [hΨ]
        exact ⟨_, _, by simp, rfl⟩
      · rw [hΨ]
        exact ⟨_, _, by simp, rfl⟩
      · intro h
        obtain ⟨-, hb⟩ := hψ.eq_of_eq (κ := 1) one_ne_zero hnorm (by simp) (by simp) h
        have hv := congrArg Fin.val hb
        norm_num at hv
      · intro h
        have h' : σf ⟨0, by omega⟩ ⟨2, by omega⟩ = σf ⟨1, by omega⟩ ⟨0, by omega⟩ := by
          rw [h, ← hψ.neg]
        obtain ⟨ha, -⟩ := hψ.eq_of_eq (κ := 1) one_ne_zero hnorm (by simp) (by simp) h'
        have hv := congrArg Fin.val ha
        norm_num at hv
    obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
    haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := ⟨hs0.ne'⟩
    have hinnerT := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
    obtain ⟨σQ, z, hσQ, hzZ, hnormz, hz⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinnerT
    have hperf : Group.IsPerfect ↥(CQ σQ i) := by
      haveI : Group.IsPerfect ↥(componentRootSpan (fixSubfield σQ) (rootCharHom a) i) :=
        isPerfect_componentRootSpan_simplyLaced (K := fixSubfield σQ) (Or.inl rfl) i hbig
      rw [CQ_eq_map (χ := rootCharHom a) (i := i) σQ]
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.equivMapOfInjective
          (componentRootSpan (fixSubfield σQ) (rootCharHom a) i)
          (baseChangeGL (fixSubfield σQ).subtype) (baseChangeGL_injective _)).toMonoidHom)
        (Subgroup.equivMapOfInjective
          (componentRootSpan (fixSubfield σQ) (rootCharHom a) i)
          (baseChangeGL (fixSubfield σQ).subtype) (baseChangeGL_injective _)).surjective
    exact centerQuotientHom_mem_innAutDerived_inner_of_untwist S hT i hs hmin σQ hσQ hzZ
      hnormz hz hperf hyZ hyF hyStab
  · obtain ⟨ν, ψ, σf, π, hν, hψ, hΨ, hπ⟩ := h
    obtain ⟨K, -, -, f, -, hKcard, hfeq, -, h32, -, -, -⟩ :=
      exists_suCover_rationalComponent_unitaryFrame S hT i hν hψ hΨ π hπ hQS
    have h32' : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ≠
        (3, 2) := by
      rw [← hfeq]
      exact h32
    exact centerQuotientHom_mem_innAutDerived_unitaryFrame S hT i hν hψ hΨ π hπ h32' hyZ hyF
      hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
