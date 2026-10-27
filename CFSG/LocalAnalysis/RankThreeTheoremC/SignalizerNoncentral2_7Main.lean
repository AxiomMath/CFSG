module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Glue
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentralLocalNarrow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SignalizerNoncentralFused (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
        ¬ K ≤ centralizer ({z} : Set G) →
        ∀ q : ℕ, q.Prime → q ≠ p → IsPGroup q K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) → K' ≤ M) →
        ⁅K, (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))⁆ = K →
        (frattini K).map K.subtype < K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) →
          K' ≤ (frattini K).map K.subtype) →
        (∀ a ∈ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)),
          (∀ k ∈ K, (a * k * a⁻¹)⁻¹ * k ∈ (frattini K).map K.subtype) → a = 1) →
        ¬ (P : Subgroup G) ≤ normalizer (K : Set G) →
        ∀ U : Subgroup G, U < D → (P : Subgroup G) ≤ normalizer (U : Set G) →
          IsElemAbelian p U → Nat.card U = p ^ 2 →
          3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer (U : Set G)) →
          normalizer (U : Set G) ≤ M →
          ∀ u ∈ U, u ≠ 1 → u ∉ (center D).map D.subtype → ¬ centralizer ({u} : Set G) ≤ M →
            (∃ g : G, g * u * g⁻¹ ∈ (center D).map D.subtype) →
            ¬ normalizer ((zpowers z : Subgroup G) : Set G) ≤ M →
            (¬ HasPrimeConstraint (G := centralizer ({u} : Set G)) p ∨
              ((¬ ∀ x ∈ centralizer ({u} : Set G),
                  x ∈ centralizer ((((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))) ⊓
                    centralizer ({u} : Set G) : Subgroup G) : Set G) → orderOf x = p →
                  x ∈ ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))) ⊓
                    centralizer ({u} : Set G)) ∧
                ¬ ∃ T : Sylow p (centralizer ({u} : Set G)),
                  (T : Subgroup (centralizer ({u} : Set G))).map
                    (centralizer ({u} : Set G)).subtype ≤ (P : Subgroup G) ∧
                  3 ≤ CFSG.Open.pRank p ((T : Subgroup (centralizer ({u} : Set G))).map
                    (centralizer ({u} : Set G)).subtype) ∧
                  ∀ a b : centralizer ({u} : Set G),
                    a ∈ (T : Subgroup (centralizer ({u} : Set G))) →
                    b ∈ (T : Subgroup (centralizer ({u} : Set G))) → a * b = b * a)) →
            K ⊓ centralizer ({u} : Set G) ≤ M

theorem signalizerNoncentralLocalNarrow_of_fused (hS : Setting G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (hno : NoExcludedSection3 G) (KF : SignalizerTwoGroupKFact)
    (h : SignalizerNoncentralFused G) : SignalizerNoncentralLocalNarrow G := by
  intro p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith hPK
    U hUD hPU hUe hUc hU3 hNU u huU hu1 huZ hC hOr
  have hc : NoncentralConfig G p P M D U u :=
    ⟨hS, hp, hext, hPD, hUD, hPU, hUe, hUc, hU3, hNU, huU, hu1, huZ⟩
  rcases hc.sylow_or_fused with hsyl | ⟨g, hgM, hgZ⟩
  · exact inf_le_right.trans (hc.centralizer_le_of_sylow hD1 K1 K2 hno KF hsyl)
  · by_cases hN : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M
    · exact inf_le_right.trans (hc.centralizer_le_of_fused hzZ hz1 hgM hgZ hN)
    · exact h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith
        hPK U hUD hPU hUe hUc hU3 hNU u huU hu1 huZ hC ⟨g, hgZ⟩ hN hOr

end CFSG.LocalAnalysis.RankThreeTheoremC
