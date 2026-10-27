module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.EnnolaOrbit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLangEnnola

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem ennola_orbitLength_odd_untw
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : DefChar.LieFamily}
    (hk : k = .F4 ∨ k = .E7 ∨ k = .E8) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup (excTag k) L p₀) {a : Fin (excTag k).rank → Lˣ} {w : WeylGroup (excTag k)}
    (hρ : ∀ γ, IsRoot (excTag k) γ → S.ρ γ = w • γ) (hT : rootDiagUnit (excTag k) a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (hqp : p ∣ S.D.q + 1) (i : KernelComponent (rootCharHom a)) :
    Odd (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  have hτ : excTag k = .F4 ∨ excTag k = .E7 ∨ excTag k = .E8 := by
    rcases hk with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨u, hu⟩ := exc_negRho_untw hτ hρ
  exact ennola_orbit_odd S.frob hp hp2 hqp hT hap hu i

theorem ennola_orbitLength_odd_twE6
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ m, a m ^ p = 1) (hqp : p ∣ S.D.q + 1)
    (i : KernelComponent (rootCharHom a)) :
    Odd (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  obtain ⟨u, hu⟩ := exc_negRho_twE6 hρ
  exact ennola_orbit_odd S.frob hp hp2 hqp hT hap hu i

end CFSG.LocalAnalysis.GLTheoremA.I167

end
