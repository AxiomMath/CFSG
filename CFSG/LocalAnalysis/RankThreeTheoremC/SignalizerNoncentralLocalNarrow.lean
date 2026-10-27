module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentralLocal
import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerLocalBT
import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerAbelianSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SignalizerNoncentralLocalNarrow (G : Type) [Group G] [Finite G] : Prop :=
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

theorem signalizerNoncentralLocal_of_narrow (hS : Setting G)
    (h : SignalizerNoncentralLocalNarrow G) : SignalizerNoncentralLocal G := by
  intro p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith hPK
    U hUD hPU hUe hUc hU3 hNU u huU hu1 huZ hC
  have hprime := sigmaA_prime p hp
  have hM := hext.obstruction.1
  have hA : IsPGroup p ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) : Subgroup G) :=
    P.isPGroup'.to_le inf_le_left
  have h3u : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({u} : Set G)) :=
    hU3.trans (pRank_mono p hprime.one_lt (inf_le_inf_left _
      (centralizer_le (Set.singleton_subset_iff.mpr huU))))
  by_cases hcon : HasPrimeConstraint (G := centralizer ({u} : Set G)) p
  · by_cases hbt : ∀ x ∈ centralizer ({u} : Set G),
        x ∈ centralizer ((((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))) ⊓
          centralizer ({u} : Set G) : Subgroup G) : Set G) → orderOf x = p →
        x ∈ ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))) ⊓ centralizer ({u} : Set G)
    · exact inf_centralizer_le_of_bt hS hp hM hA hAK hK h3u hcon hbt
    · by_cases habs : ∃ T : Sylow p (centralizer ({u} : Set G)),
          (T : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype ≤
            (P : Subgroup G) ∧
          3 ≤ CFSG.Open.pRank p ((T : Subgroup (centralizer ({u} : Set G))).map
            (centralizer ({u} : Set G)).subtype) ∧
          ∀ a b : centralizer ({u} : Set G), a ∈ (T : Subgroup (centralizer ({u} : Set G))) →
            b ∈ (T : Subgroup (centralizer ({u} : Set G))) → a * b = b * a
      · exfalso
        obtain ⟨T, hTP, hT3, hTab⟩ := habs
        exact hC (centralizer_le_of_abelian_sylow hS hp hM T hTP hT3 hTab hcon)
      · exact h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith
          hPK U hUD hPU hUe hUc hU3 hNU u huU hu1 huZ hC (Or.inr ⟨hbt, habs⟩)
  · exact h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith
      hPK U hUD hPU hUe hUc hU3 hNU u huU hu1 huZ hC (Or.inl hcon)

theorem signalizerNoncentralIrreducible_of_narrow (hS : Setting G)
    (h : SignalizerNoncentralLocalNarrow G) : SignalizerNoncentralIrreducible G :=
  signalizerNoncentralIrreducible_of_local hS (signalizerNoncentralLocal_of_narrow hS h)

end CFSG.LocalAnalysis.RankThreeTheoremC
