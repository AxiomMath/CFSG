module

public import CFSG.Certificates.Kernel.GGToral.PkTwistWalk

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.StepTwoToralCert


theorem pkSplit_facts {τ : Tag} {p : ℕ} (hp : p.Prime) {D : List ℕ}
    (hc : pkCheck (pkTheta τ) D = true) (hh : pkHead τ.rootCertificate.roots D = true)
    (ht : pkTag τ p 0 D = true) :
    ∀ μ : Fin τ.rank → ℤ, (kacOf τ).IsNormal p μ → modP p μ ≠ 0 →
      ∀ O : Set (Fin τ.rank → ℤ),
        IsCompOrbit τ.symmetrizedCartan 1 (latPhi {α | IsRoot τ α} p (modP p μ)) O →
        CaseFacts p 1 ⊤ (modP p μ) O :=
  pkSplit_caseFacts hp hc hh ht

theorem pkTwist_facts {p : ℕ} (hp : p.Prime) {D : List ℕ} (hc : pkCheck [] D = true)
    (hh : pkHead Tag.E6.rootCertificate.roots D = true) (ht : pkTag .E6 p 1 D = true) :
    ∀ b ∈ fixedSub p e6Gamma, b ≠ 0 →
      ∀ O : Set (Fin Tag.E6.rank → ℤ),
        IsCompOrbit Tag.E6.symmetrizedCartan e6Gamma (latPhi {α | IsRoot .E6 α} p b) O →
        CaseFacts p e6Gamma (fixedSub p e6Gamma) b O :=
  pkTwist_caseFacts hp hc hh ht

theorem pkSplit_sound {τ : Tag} {p : ℕ} (hp : p.Prime) {D : List ℕ}
    (hc : pkCheck (pkTheta τ) D = true) (hh : pkHead τ.rootCertificate.roots D = true)
    (ht : pkTag τ p 0 D = true) : SplitCertSpec τ p ⊤ := by
  intro μ hμ _ hμ0 O hO hcard D hD
  exact caseFacts_certConcl hp (pkSplit_facts hp hc hh ht μ hμ hμ0 O hO) hD hcard

theorem pkTwist_sound {p : ℕ} (hp : p.Prime) {D : List ℕ} (hc : pkCheck [] D = true)
    (hh : pkHead Tag.E6.rootCertificate.roots D = true) (ht : pkTag .E6 p 1 D = true) :
    TwistCertSpec p e6Gamma := by
  intro b hb hb0 O hO hcard D hD
  exact caseFacts_certConcl hp (pkTwist_facts hp hc hh ht b hb hb0 O hO) hD hcard

end CFSG.KC.GGToral
