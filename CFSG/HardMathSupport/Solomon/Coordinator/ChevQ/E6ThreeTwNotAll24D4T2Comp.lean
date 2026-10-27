module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section Comp

set_option linter.unusedSectionVars false


@[expose] def D4T2OuterThm : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀),
    (∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) →
    ∀ {l f : ℕ}, l.Prime → 0 < f → S.D.q = l ^ f → l ≠ 3 → ((3 : ℕ) : L) ≠ 0 →
      3 ∣ l ^ f + 1 →
    ∀ {a : Fin Tag.E6.rank → Lˣ}, rootDiagUnit .E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    ∀ (i : KernelComponent (rootCharHom a)),
      (kernelRoots (rootCharHom a)).ncard = 24 →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      (componentRoots (rootCharHom a) i).ncard = 24 →
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) →
      TwE6ComponentType (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem d4t2_class_eq_kernel {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := by
  obtain ⟨-, hn⟩ := d4t2_class_of_card h3 hap hall i
  exact Set.eq_of_subset_of_ncard_le (componentRoots_subset_kernelRoots _ i)
    (by rw [hn, hall]) (finite_kernelRoots_E6 _)

theorem d4t2_class_subsingleton {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) (i j : KernelComponent (rootCharHom a)) :
    i = j :=
  TwE6UniqAbs.eq_of_componentRoots_eq
    ((d4t2_class_eq_kernel h3 hap hall i).trans (d4t2_class_eq_kernel h3 hap hall j).symm)

theorem d4t2_rational_componentType (hOut : D4T2OuterThm)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    TwE6ComponentType (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap hall i
  have hker := d4t2_class_eq_kernel h3 hap hall i
  have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [hker] at hγ ⊢
    exact outer_rho_mem_kernelRoots S hT hγ
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
  · exact twE6ComponentType_rational_of_inner_d4 S hl hf hq hl3 h3 hT hap i hall hr hc hρ hin
  · exact hOut S hS hl hf hq hl3 h3 h3q hT hap i hall hr hc hρ hin

theorem twE6LineComponentsAt_of_d4 (hOut : D4T2OuterThm)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hd : TwE6LineDim K σ f 30) : TwE6LineComponentsAt K σ E f := by
  classical
  obtain ⟨h, hh, hh1, hh3, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  subst hh
  have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  have hsub : ∀ i j : KernelComponent (rootCharHom D.a), i = j := fun i j =>
    d4t2_class_subsingleton D.hL3 D.hap hall i j
  have hq3 : 3 ∣ ringChar K ^ D.e + 1 := D.hqe ▸ hE.three_dvd
  have hcomp : ∀ i : KernelComponent (rootCharHom D.a),
      TwE6ComponentType (rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) := fun i =>
    d4t2_rational_componentType hOut D.S D.hS D.hℓ D.he D.hSq hE.char_ne_three D.hL3 hq3 D.hT
      D.hap hall i
  intro J hJ
  obtain ⟨i, -, hi⟩ := D.exists_rationalComponent hJ
  refine ⟨fun g hg => ?_, twE6ComponentType_of_map_injective D.ι D.hinj (hi ▸ hcomp i)⟩
  have hfg : twistedE6InndiagConj K σ h * g = g * twistedE6InndiagConj K σ h :=
    congrArg Subtype.val (hE.elemAbelian.1.is_comm.comm ⟨_, hf⟩ ⟨g, hg⟩)
  obtain ⟨i', -, hi'⟩ := D.exists_rationalComponent (isComponentOf_map_of_commute _ g hfg hJ)
  exact D.eq_of_map_eq (by rw [hi', hi, hsub i' i])

end Comp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
