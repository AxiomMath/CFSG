module

public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

namespace D1SocleConfig

variable {G : Type} [Group G] [Finite G] {T : Type} [Group T] [Finite T] {p a b : ℕ}
  [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}

theorem exists_competitorHom_of_mulEquiv (h : D1SocleConfig T p P M H R X)
    (hT : JStarTargetBase p b T) (hTc : JStarTargetCard p a b T)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal) (e : K ≃* T)
    (hXK : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K)
    {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        T,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      (∀ j : H', (j : G) ∈ nclIn H X →
        (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
            φ.ker.map (((nclIn H X).subgroupOf H').map
              (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
          (j : G) ∈ GLBPrimeCore p H)) ∧
      ∀ (j : H') (hj : j ∈ (nclIn H X).subgroupOf H'),
        ((e.symm (φ ⟨QuotientGroup.mk' (primeComplementCore (G := H') p) j,
            Subgroup.mem_map_of_mem _ hj⟩) : K) : H ⧸ primeComplementCore (G := H) p) =
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H X hj⟩ :=
  exists_competitorHom_of_map_nclIn_eq (h.map_nclIn_eq hT hTc hKn ⟨e⟩ hXK) e hJH'

theorem exists_competitorHom (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
        T,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) ∧
      ∀ j : H', (j : G) ∈ nclIn H X →
        (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
            φ.ker.map (((nclIn H X).subgroupOf H').map
              (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
          (j : G) ∈ GLBPrimeCore p H) := by
  obtain ⟨K, hKn, ⟨e⟩, -, hXK⟩ := h.socle
  obtain ⟨φ, hs, hc, hk, -⟩ := h.exists_competitorHom_of_mulEquiv hT hTc hKn e hXK hJH'
  exact ⟨φ, hs, hc, hk⟩

theorem nclIn_map_eq (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    nclIn (((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
        ((X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))) =
      ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) :=
  CFSG.AGLEmbedding.nclIn_map_eq _ (le_nclIn h.le_H) hJH' (h.nclIn_nclIn hT hTc)

omit [Finite T] in
theorem map_le_normalizer_map (h : D1SocleConfig T p P M H R X) {H' : Subgroup G}
    (hJH' : nclIn H X ≤ H') :
    (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≤
      Subgroup.normalizer ((((nclIn H X).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p)) : Subgroup _) : Set _) :=
  CFSG.AGLEmbedding.map_le_normalizer_map _ hJH' (h.ext.le_H.trans (le_normalizer_nclIn H X))

theorem faithful_of_mem_ker_iff (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H')
    {φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) →*
      T}
    (hker : ∀ j : H', (j : G) ∈ nclIn H X →
      (QuotientGroup.mk' (primeComplementCore (G := H') p) j ∈
          φ.ker.map (((nclIn H X).subgroupOf H').map
            (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype ↔
        (j : G) ∈ GLBPrimeCore p H)) :
    ∀ z ∈ (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)),
      (∀ y ∈ ((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p)),
        z * y * z⁻¹ * y⁻¹ ∈ φ.ker.map (((nclIn H X).subgroupOf H').map
          (QuotientGroup.mk' (primeComplementCore (G := H') p))).subtype) → z = 1 :=
  faithful_of_mem_ker_iff_of h.ext.le_H (h.eq_one_of_forall_commutator_mem hT hTc) hJH' hker

end D1SocleConfig

end CFSG.AGLEmbedding
