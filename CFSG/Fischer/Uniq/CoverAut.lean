module

public import CFSG.Fischer.Uniq.TwoCover
public import CFSG.Fischer.Uniq.MuSets

public section

namespace CFSG.Fischer

namespace TwoCover

variable {V : Type*} {G : SimpleGraph V} {H : V → V → V → Prop}

theorem map_other (P Q : TwoCover G H) {φ : P.C → Q.C} (hφπ : ∀ c, Q.π (φ c) = P.π c)
    (hinj : Function.Injective φ) (c : P.C) : φ (P.other c) = Q.other (φ c) := by
  rcases Q.eq_or_eq_other (c := φ c) (x := φ (P.other c)) (by rw [hφπ, hφπ, P.π_other]) with
    h | h
  · exact absurd (hinj h) (P.other_ne c)
  · exact h

theorem eq_of_eq_at (P Q : TwoCover G H) (hG : G.Connected) {φ ψ : P.C → Q.C}
    (hφπ : ∀ c, Q.π (φ c) = P.π c) (hψπ : ∀ c, Q.π (ψ c) = P.π c)
    (hφ : ∀ c c', P.adj.Adj c c' → Q.adj.Adj (φ c) (φ c'))
    (hψ : ∀ c c', P.adj.Adj c c' → Q.adj.Adj (ψ c) (ψ c'))
    (hφinj : Function.Injective φ) (hψinj : Function.Injective ψ) {c₀ : P.C}
    (h₀ : φ c₀ = ψ c₀) : φ = ψ := by
  have hstep : ∀ c c', P.adj.Adj c c' → φ c = ψ c → φ c' = ψ c' := by
    intro c c' hcc' hc
    obtain ⟨x, -, huniq⟩ := Q.lift (φ c) (P.π c') (by rw [hφπ]; exact P.proj hcc')
    have h1 := huniq (φ c') ⟨hφ c c' hcc', hφπ c'⟩
    have h2 := huniq (ψ c') ⟨hc ▸ hψ c c' hcc', hψπ c'⟩
    rw [h1, h2]
  have hoth : ∀ c, φ c = ψ c → φ (P.other c) = ψ (P.other c) := by
    intro c hc
    rw [map_other P Q hφπ hφinj, map_other P Q hψπ hψinj, hc]
  have hfib : ∀ v, ∀ c, P.π c = v → φ c = ψ c := by
    intro v
    refine reachable_induction (G := G) (p := fun v => ∀ c, P.π c = v → φ c = ψ c)
      (fun u w huw hu c hc => ?_) (hG (P.π c₀) v) ?_
    · obtain ⟨c₁, ⟨hcc₁, hπ⟩, -⟩ := P.lift c u (by rw [hc]; exact huw.symm)
      exact hstep c₁ c hcc₁.symm (hu c₁ hπ)
    · intro c hc
      rcases P.eq_or_eq_other hc with rfl | rfl
      · exact h₀
      · exact hoth c₀ h₀
  funext c
  exact hfib _ c rfl

end TwoCover

end CFSG.Fischer
