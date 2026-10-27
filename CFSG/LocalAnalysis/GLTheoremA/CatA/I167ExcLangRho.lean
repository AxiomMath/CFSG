module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem excLang_twE6_rho {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) :
    ∃ w : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := by
    intro g
    rw [hΦ]
    rfl
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hq0 : 0 < S.D.q := S.hqpow.1.pos
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  refine ⟨w, fun γ hγ => ?_⟩
  have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
      Fr := by
    ext1 g
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
      (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
    rw [hΦ', hn]
  have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
  have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
      rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
    rw [← S.frob.map_rootSubgroup γ hγ, hst]
    exact h2
  have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
    IsRoot.smul (hγ.permLattice e6Graph_cartan) w
  exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3


end CFSG.LocalAnalysis.GLTheoremA.I167

end
