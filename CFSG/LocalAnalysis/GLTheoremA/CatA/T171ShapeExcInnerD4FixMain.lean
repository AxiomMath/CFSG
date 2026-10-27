module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriKac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


theorem isPerfect_CQ_of_simplyLaced {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : KernelComponent χ)
    (hc : 2 < (componentRoots χ i).ncard) (σ : L ≃+* L) :
    Group.IsPerfect ↥(CQ σ i) := by
  have hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α := by
    by_contra h
    have hfin : (componentRoots χ i).Finite :=
      (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
    obtain ⟨α, hα⟩ := (Set.ncard_pos hfin).mp (by omega)
    have hsub : componentRoots χ i ⊆ ({α, -α} : Set (Fin τ.rank → ℤ)) := by
      intro δ hδ
      by_cases hd : δ = α
      · rw [hd]; simp
      · have hd' : δ = -α := by
          by_contra hd''
          exact h ⟨α, hα, δ, hδ, hd, hd''⟩
        rw [hd']; simp
    have hle : (componentRoots χ i).ncard ≤ ({α, -α} : Set (Fin τ.rank → ℤ)).ncard :=
      Set.ncard_le_ncard hsub ((Set.finite_singleton (-α)).insert α)
    have h2 : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
      have := Set.ncard_insert_le α ({-α} : Set (Fin τ.rank → ℤ))
      rw [Set.ncard_singleton] at this
      simpa using this
    omega
  exact isPerfect_CQ_of_isPerfect_componentRootSpan i σ
    (isPerfect_componentRootSpan_simplyLaced (K := ↥(fixSubfield σ)) hτ i hbig)

theorem innerD4FixedPointsPerfect_of_simplyLaced {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p : ℕ} (S : LangSetup τ L p) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  have hinner := twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i hs0 hinner
  exact twoDExcFixedPointsPerfect_of_isPerfect_CQ S i hnorm hz
    (fun y hy hfix => mem_CQ_of_frobGL_fixed_rank_four i hr hc σ hy hfix)
    (isPerfect_CQ_of_simplyLaced hτ i (by rw [hc]; norm_num) σ)

theorem innerD4FixedPointsPerfect_holds : InnerD4FixedPointsPerfect := by
  intro τ L _ _ _ p₀ S a hT i hk hr hc
  cases τ with
  | G2 =>
    exfalso
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨N, hN, hNL, hTN⟩ := excTri_exists_order S hT
    exact (excTri_F4_absurd hN hNL hTN i hr hc).elim
  | D4 =>
    exact innerD4FixedPointsPerfect_of_simplyLaced S (Or.inl rfl) hT i hk hr hc
  | E6 =>
    exact innerD4FixedPointsPerfect_of_simplyLaced S (Or.inr (Or.inl rfl)) hT i hk hr hc
  | E7 =>
    exact innerD4FixedPointsPerfect_of_simplyLaced S (Or.inr (Or.inr (Or.inl rfl)))
      hT i hk hr hc
  | E8 =>
    exact innerD4FixedPointsPerfect_of_simplyLaced S (Or.inr (Or.inr (Or.inr rfl)))
      hT i hk hr hc

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
