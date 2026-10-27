module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Thompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_PCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Opt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsRelPairCandidate.not_hasPrimeConstraint (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D R T H : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hH : IsRelPairCandidate p D R T H) : ¬ HasPrimeConstraint (G := H) p := by
  intro hcon
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  obtain ⟨hDab, -, -, -, -, -, -, hCD, -⟩ := hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  have hcontains : ∀ x : G, x ∈ H → x ∈ centralizer (D : Set G) → orderOf x = p → x ∈ D :=
    fun x _ hxC hxo => hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x)
  have hall : ∀ A : Subgroup G, A ≤ H → IsPGroup 2 A → D ≤ normalizer (A : Set G) →
      A ≤ (primeComplementCore (G := H) p).map H.subtype := by
    intro A hAH hA2 hDA
    have hcop : p.Coprime (Nat.card A) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA2
      rw [hn]
      exact ((Nat.coprime_primes hprime Nat.prime_two).mpr hodd).pow_right n
    exact ambient_prime_constraint_signalizer_le_core p hprime hodd H D A hcon
      (P.isPGroup'.to_le hDP) hDH hcop hAH hDA hcontains
  have hjoin := invariantTwoJoinIn_le_of_forall hall
  have hdvd : p ∣ Nat.card ((primeComplementCore (G := H) p).map H.subtype) :=
    hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin)
  rw [card_map_of_injective H.subtype_injective] at hdvd
  exact (hprime.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) hdvd

structure OptimalRelPairFacts (p : ℕ) (M D H V : Subgroup G) : Prop where
  not_constrained : ¬ HasPrimeConstraint (G := H) p
  exists_component : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
    L ≤ centralizer (CFSG.Open.pCore p (H ⧸ primeComplementCore (G := H) p) : Set _) ∧
    ¬ L ≤ CFSG.Open.pCore p (H ⧸ primeComplementCore (G := H) p) ∧ p ∣ Nat.card L ∧
    p ∣ Nat.card (L ⧸ center L) ∧ IsCatalogGroup (L ⧸ center L)
  pCore_quotient : CFSG.Open.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥
  pRank_eq : CFSG.Open.pRank p H = 2
  normalizer_pCore : normalizer (pCoreOf 2 H : Set G) = H
  sylow : IsSylowOf 2 (pCoreOf 2 H) ((primeComplementCore (G := H) p).map H.subtype)
  pCore_le : pCoreOf 2 H ≤ V
  le_M : V ≤ M
  maximal : invariantTwoMaximalWithin D H V
  not_dvd : ∀ Y : Subgroup G, Y ≤ V → Y ≠ ⊥ → normalizer (V : Set G) ≤ normalizer (Y : Set G) →
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (H ⊓ normalizer (Y : Set G)))
  signalizer : ∀ d ∈ D, d ≠ 1 → ∃ K : Subgroup G,
    K ≤ normalizer ((zpowers d : Subgroup G) : Set G) ∧
      normalizer ((zpowers d : Subgroup G) : Set G) ≤ normalizer (K : Set G) ∧
      p.Coprime (Nat.card K) ∧ ∀ Y : Subgroup G,
        Y ≤ normalizer ((zpowers d : Subgroup G) : Set G) → p.Coprime (Nat.card Y) →
          D ≤ normalizer (Y : Set G) → Y ≤ K

theorem IsOptimalRelPair.facts (hS : Setting G) (hD1 : TheoremD1 G) (hK : KFactLemma212)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T)
    (hopt : IsOptimalRelPair p M D R T H V) : OptimalRelPairFacts p M D H V where
  not_constrained := hopt.pair.cand.not_hasPrimeConstraint hS hD1 hp hd.ext hd.not_le_normalizer
    hR h13
  exists_component := by
    have := hS.simple
    exact CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper H
      (twoLocal_ne_top hS.nonab H hopt.pair.cand.twoLocal) p (sigmaA_prime p hp)
      (hopt.pair.cand.not_hasPrimeConstraint hS hD1 hp hd.ext hd.not_le_normalizer hR h13)
  pCore_quotient := hopt.pair.cand.pCore_quotient_eq_bot hS hD1 hK hp hd.ext
    hd.not_le_normalizer hR h13
  pRank_eq := hopt.pair.cand.pRank_eq_two hS hD1 hp hd.ext hd.not_le_normalizer hR h13
  normalizer_pCore := hopt.normalizer_pCoreOf_eq
  sylow := hopt.isSylowOf_pCoreOf (sigmaA_prime p hp) (sigmaA_odd p hp)
    (P.isPGroup'.to_le hd.ext.obstruction.2.1)
  pCore_le := hopt.pCoreOf_le_V hd
  le_M := (hopt.invariantTwoMaximalWithin_H hd).1
  maximal := (hopt.invariantTwoMaximalWithin_H hd).2
  not_dvd := fun _ hYV hY1 hY => hopt.not_dvd_card_invariantTwoJoinIn_normalizer hS hD1 hp
    hd.ext hd.not_le_normalizer hR h13 hYV hY1 hY
  signalizer := fun _ hdD hd1 => hd.ext.exists_normal_coprime_signalizer hS hD1 hK hp
    hd.not_le_normalizer hR h13 hdD hd1

end CFSG.LocalAnalysis.RankThreeTheoremC
