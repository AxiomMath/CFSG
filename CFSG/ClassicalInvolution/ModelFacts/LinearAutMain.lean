module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.ClassicalInvolution.RouteD.GapsD4A
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open CFSG.ClassicalInvolution.RouteD.Gaps

theorem linearAutClassification {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) : LinearAutClassification (GaloisField p f) n := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  intro X _ θ hθ hker σ
  obtain ⟨α, hα⟩ := exists_mulEquiv_lift (p := p) (by omega : 1 ≤ n) θ hθ hker σ
  obtain ⟨g, φ, ε, h⟩ := exists_aut_form hp2 hq hn α
  exact ⟨α.toMonoidHom, g, φ, ε, hα, h⟩

end CFSG.ClassicalInvolution.ModelFacts.LinearAut
