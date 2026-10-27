module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc_negRho_untw {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {w : WeylGroup τ} (hρ : ∀ γ, IsRoot τ γ → ρ γ = w • γ) :
    ∃ u : WeylGroup τ, ∀ γ, IsRoot τ γ → ρ γ = -(u • γ) := by
  rcases hτ with rfl | rfl | rfl
  · exact ⟨w * f4Neg, fun γ hγ => by rw [hρ γ hγ, mul_smul, f4Neg_smul, smul_neg, neg_neg]⟩
  · exact ⟨w * e7Neg, fun γ hγ => by rw [hρ γ hγ, mul_smul, e7Neg_smul, smul_neg, neg_neg]⟩
  · exact ⟨w * e8Neg, fun γ hγ => by rw [hρ γ hγ, mul_smul, e8Neg_smul, smul_neg, neg_neg]⟩

theorem exc_negRho_twE6 {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {w : WeylGroup Tag.E6}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = w • permLattice e6Graph γ) :
    ∃ u : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → ρ γ = -(u • γ) := by
  refine ⟨w * HardMathSupport.Lang.E6Descent.twE6W0, fun γ hγ => ?_⟩
  rw [hρ γ hγ, mul_smul, HardMathSupport.Lang.E6Descent.twE6W0_smul, smul_neg, neg_neg]
  rfl

theorem exc_ennola_of_negRho {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hE6 : τ = .E6 → p ≠ 3)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (hqp : p ∣ S.D.q + 1)
    {u : WeylGroup τ} (hu : ∀ γ, IsRoot τ γ → S.ρ γ = -(u • γ))
    (i : KernelComponent (rootCharHom a)) :
    ∃ u' ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u' • γ) := by
  have hstab : u ∈ rootCharStabilizerSubgroup a := by
    refine f4Three_mem_rootCharStabilizer_of_roots fun γ hγ => ?_
    have h1 := S.frob.rootChar_eq a hT γ hγ
    rw [hu γ hγ, show -(u • γ) = (-1 : ℤ) • (u • γ) by rw [neg_one_smul], rootChar_zsmul,
      zpow_neg_one] at h1
    have hpow : rootChar a γ ^ p = 1 := CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hap γ
    obtain ⟨c, hc⟩ := hqp
    have h2 : rootChar a γ ^ S.D.q * rootChar a γ = 1 := by
      rw [← pow_succ, hc, pow_mul, hpow, one_pow]
    rw [eq_inv_of_mul_eq_one_left h2] at h1
    exact inv_injective h1
  have hker : u ∈ kernelReflectionGroup a :=
    T171Sh.rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2 hτ hE6 hap hstab
  obtain ⟨u', hu'C, hu'⟩ := f4Three_exists_restrict i hker
  exact ⟨u', hu'C, fun γ hγ => by rw [hu γ (isRoot_of_mem_componentRoots hγ), hu' γ hγ]⟩

theorem exc_ennola_untw {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : DefChar.LieFamily}
    (hk : k = .F4 ∨ k = .E7 ∨ k = .E8) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup (excTag k) L p₀) {a : Fin (excTag k).rank → Lˣ} {w : WeylGroup (excTag k)}
    (hρ : ∀ γ, IsRoot (excTag k) γ → S.ρ γ = w • γ) (hT : rootDiagUnit (excTag k) a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (hqp : p ∣ S.D.q + 1) (i : KernelComponent (rootCharHom a)) :
    ∃ u ∈ Subgroup.closure {s : WeylGroup (excTag k) | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ) := by
  have hτ : excTag k = .F4 ∨ excTag k = .E7 ∨ excTag k = .E8 := by
    rcases hk with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨u, hu⟩ := exc_negRho_untw hτ hρ
  refine exc_ennola_of_negRho hp hp2 ?_ (fun h => ?_) S hT hap hqp hu i
  · rcases hτ with h | h | h <;> rw [h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · rcases hτ with h' | h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)

theorem exc_ennola_twE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    {w : WeylGroup Tag.E6} (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (hqp : p ∣ S.D.q + 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ u ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ) := by
  obtain ⟨u, hu⟩ := exc_negRho_twE6 hρ
  exact exc_ennola_of_negRho hp hp2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun _ => hp3) S hT hap
    hqp hu i

theorem exc_neg_mem_component {τ : Tag} {K : Type} [Field K] {a : Fin τ.rank → Kˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) : -γ ∈ componentRoots (rootCharHom a) i := by
  have hr : rootReflection γ ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ δ ∈ componentRoots (rootCharHom a) i, s = rootReflection δ} :=
    Subgroup.subset_closure ⟨γ, hγ, rfl⟩
  have h := (f4Three_smul_mem_component_iff i hr γ).2 hγ
  rwa [rootReflection_smul_self (isRoot_of_mem_componentRoots hγ)] at h

theorem exc_rho_mem_component {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {u : WeylGroup τ} (huC : u ∈ Subgroup.closure {s : WeylGroup τ |
      ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ})
    (hu : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) : S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  rw [hu γ hγ]
  exact exc_neg_mem_component i ((f4Three_smul_mem_component_iff i huC γ).2 hγ)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
