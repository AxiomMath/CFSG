module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterPassFormula
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighFixedAdj

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups


private theorem twoD_root_facts
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hsl : SimplyLacedTag τ)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {w : WeylGroup τ}
    (hwW : w ∈ componentWeylGroup (componentRoots (rootCharHom a) i))
    (hform : ∀ γ, f γ = S.ρ (w • γ))
    (hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
      f γ ∈ posRoots (componentRoots (rootCharHom a) i))
    (hne : ∃ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ) :
    (∀ γ ∈ (componentRoots (rootCharHom a) i), f (f γ) = γ) ∧ (∀ γ ∈ (componentRoots (rootCharHom a) i), f γ ≠ γ → iform γ (f γ) = 0) ∧
      (∀ γ ∈ (componentRoots (rootCharHom a) i), f γ = γ → ∃ γ' ∈ (componentRoots (rootCharHom a) i), f γ' = γ' ∧ iform γ γ' = -1) ∧
      ∀ γ ∈ (componentRoots (rootCharHom a) i), f γ ≠ γ → ∃ γ' ∈ (componentRoots (rootCharHom a) i), f γ' = γ' ∧ iform γ γ' = -1 := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨-, hcard⟩ := S.twoD_factsT hT i hk h5
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    S.image_componentRoots_eq_of_five_leT hT i h5
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  let δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    S.rhoHom.comp (DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) w)
  have hδf : ∀ γ, δ γ = f γ := fun γ => by rw [hform γ]; rfl
  have hiso : ∀ x y, iform (δ x) (δ y) = iform x y := fun x y => by
    rw [hδf x, hδf y, hform x, hform y, iform_rho S, iform_smul]
  have hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ := by
    intro γ hγ
    rw [hδf γ, hform γ]
    exact hρΨ _ (smul_mem_of_mem_componentWeylGroup hΨ hwW γ hγ)
  have hposδ : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ := fun γ hγ => by
    rw [hδf γ]
    exact hpos γ hγ
  have hmoved : ∃ γ ∈ Ψ, δ γ ≠ γ := by
    obtain ⟨γ, hγ, hfγ⟩ := hne
    exact ⟨γ, hγ, by rwa [hδf γ]⟩
  have hneΔ : ∃ β ∈ simpleRoots Ψ, δ β ≠ β :=
    exists_simpleRoot_ne_of_exists_ne hΨ hmoved
  have hsl' : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ =>
    outer_iform_self_of_simplyLaced hsl (hΨ.isRoot β hβ)
  have hG : IsGraphTwist Ψ δ :=
    isGraphTwist_of_twoD hΨ hsl' h5 hcard δ hiso hmaps hposδ hneΔ
  have hN := exists_fixed_adj_of_twoD hΨ hsl' h5 hcard δ hiso hmaps hposδ hneΔ
  obtain ⟨hinv, horth, hR2, hR3⟩ := hG.root_facts hiso hΨ hmaps hN
  simp only [hδf] at hinv horth hR2 hR3
  exact ⟨hinv, horth, hR2, hR3⟩

theorem commute_rootSpan_of_commute_component_twoD_two_of_tableCheck
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : RootOps.tableCheck τ = true) [CharP L 2] (hq : S.D.q = 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hmem : ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hsl : SimplyLacedTag τ := by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    S.componentOrbitLength_eq_one_of_five_leT hT i h5
  obtain ⟨hnin, -⟩ := S.twoD_factsT hT i hk h5
  obtain ⟨f, z₀, φ₁, hf, hpos, hpin, hz₀n, hφ₁, -, hne, w, hwW, hform⟩ :=
    outer_exists_lang_data_formula S hT i
  have hform' : ∀ γ, f γ = S.ρ (w • γ) := by
    intro γ
    rw [hform γ, hs1, Function.iterate_one]
  have hmoved : ∃ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ :=
    hne (by rwa [hs1, Function.iterate_one])
  obtain ⟨hinv, horth, hR2, hR3⟩ :=
    twoD_root_facts S hsl hT i hk h5 hwW hform' hpos hmoved
  refine commute_rootSpan_of_commute_component_outer_two_of_tableCheck S hτ hcheck i hs1 hf ?_ hz₀n hφ₁
    hinv horth hR2 hR3 hmem z hcomm
  simpa [hs1, hq] using hpin

theorem commute_rootSpan_of_commute_component_twoD_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP L 2] (hq : S.D.q = 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hmem : ∀ g ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i), g ∈ S.D.model →
      (∃ n : ℕ, g ^ 2 ^ n = 1) → g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g :=
  commute_rootSpan_of_commute_component_twoD_two_of_tableCheck S hτ (RootOps.tableCheck_eq τ)
    hq hT i hk h5 hmem z hcomm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
