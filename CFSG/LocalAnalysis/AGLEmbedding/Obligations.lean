module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1ConstrainedCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → HasPrimeConstraint (G := H) p → False

@[expose] def D1ComponentCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → ¬ HasPrimeConstraint (G := H) p → False

theorem d1ExtremalCase_of_cases (hcon : D1ConstrainedCase) (hcomp : D1ComponentCase) :
    D1ExtremalCase := by
  intro G _ _ hglob p P M hloc H R h
  by_cases hc : HasPrimeConstraint (G := H) p
  · exact hcon G hglob p P M hloc H R h hc
  · exact hcomp G hglob p P M hloc H R h hc

theorem d1_of_cases (hcon : D1ConstrainedCase) (hcomp : D1ComponentCase) (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) (p : ℕ)
    (hp : p ∈ GLBBetaFour G) (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_extremalCase (d1ExtremalCase_of_cases hcon hcomp) G hnonab hK hchar he hpre p hp P M hM
    hWM H hH hHM

@[expose] def D1CentralizerCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → HasPrimeConstraint (G := H) p →
      ∀ z : G, z ∈ R → orderOf z = p → z ∈ Subgroup.centralizer (P : Set G) →
      (∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ (P : Subgroup G) → orderOf y = p →
        y ∈ Subgroup.zpowers z) →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ M →
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M →
      Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) →
      ∀ Pbar : Sylow p (Subgroup.centralizer ({z} : Set G) ⧸
          primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
        (Pbar : Subgroup _) = ((P : Subgroup G).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)) →
        ReducedNongeneration p (Subgroup.centralizer ({z} : Set G) ⧸
            primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) Pbar
          (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map
              (QuotientGroup.mk' (primeComplementCore p))) →
        (∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
          QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC ∈
            Subgroup.center (Subgroup.centralizer ({z} : Set G) ⧸
              primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ∧
          orderOf (QuotientGroup.mk'
            (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC) = p) →
        ∀ K : Subgroup (Subgroup.centralizer ({z} : Set G) ⧸
            primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
          IsComponentOf K ⊤ → K.Normal → (∀ L, IsComponentOf L ⊤ → L = K) → False

theorem d1ConstrainedCase_of_centralizerCase (h : D1CentralizerCase) : D1ConstrainedCase := by
  intro G _ _ hglob p P M hloc H R hext hcon
  obtain ⟨z, hzR, hzp, hzc, huniq, hCM, hcoreM, hodd, Pbar, hPbar, hred, hzbar, K, hK, hKn,
    hKu⟩ := hext.exists_reducedNongeneration_of_hasPrimeConstraint hloc hcon
  exact h G hglob p P M hloc H R hext hcon z hzR hzp hzc huniq hCM hcoreM hodd Pbar hPbar hred
    hzbar K hK hKn hKu

end CFSG.AGLEmbedding
