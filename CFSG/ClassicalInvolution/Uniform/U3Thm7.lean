module

public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Model

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly CFSG.Blueprint
open scoped MatrixGroups

section G2D4

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem noTwins_of_g2d4_datum {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (M : Ih8Model 3 1 Ω t k e) (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (ht : t = .G2 ∨ t = .trialityD4) : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  rcases ht with ht2 | ht2
  · subst ht2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    subst hk
    exact G2D4Models.noTwins_of_model M.ψ hinj M.surj M.mem_iff htrans fun R hR =>
      G2D4Models.noTwins_g2 hp2 he R (M.cls_sub hR)
  · subst ht2
    have hk : k = 0 := M.admissible.2.2
    subst hk
    exact G2D4Models.noTwins_of_model M.ψ hinj M.surj M.mem_iff htrans fun R hR c hc g hg =>
      G2D4Models.noTwinsFund_td4 hp2 M.admissible R (M.cls_sub hR) c hc g hg

end G2D4

section Inputs

@[expose] def Ih8TwinShapeU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) →
      (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
        ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ), Ih8Model 3 1 Ω t k e →
          t ≠ .G2 → t ≠ .trialityD4 → (∃ K ∈ Ω, ∃ K' ∈ twinSet Ω K, K' ≠ K) →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ IsOrthTag d ε t k

end Inputs

section Thm7

theorem thm7TypedBelowU_three_of (hTwin : Ih8TwinShapeU) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) : Thm7TypedBelowU 3 1 n := by
  intro hp2 _ G _ _ _ hlt Ω hΩ hA htrans K hK hK'
  obtain ⟨K', hK'Ω, hne'⟩ := hK'
  obtain ⟨D, hcard⟩ := exists_omegaLieU_of_simple hn hlt hΩ ⟨K, hK⟩
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Ω t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    let M := D.toIh8Model hΩ ⟨K, hK⟩ hcard i ht hadm he hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exact absurd (noTwins_of_g2d4_datum M htrans hG2d4 K hK K' hK'Ω) hne'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    obtain ⟨d, ε, hd, hdε⟩ := hTwin G Ω hΩ hA htrans t k e M hG2 hD4 ⟨K, hK, K', hK'Ω, hne'⟩
    exact ⟨d, ε, hd, t, k, hdε, hLie⟩
  · exact (false_of_sl23_component D hΩ ⟨K, hK⟩ hcard i hc).elim
  · obtain ⟨e⟩ := exists_mulEquiv_m11 D hΩ ⟨K, hK⟩ i hc
    exact absurd (noTwins_of_mulEquiv_m11 e hΩ K hK K' hK'Ω) hne'

end Thm7

end CFSG.ClassicalInvolution.Uniform
