module

public import CFSG.CharacterTheory.Semidihedral.StationaryLayerCover
public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups

public section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups

variable {G : Type} [Group G]

@[expose] def ordinaryLocalSylow (t s : G) {ell : ℕ} (P : Sylow ell (N t)) : Prop :=
  let Pa := LocalSylowNormalizerFactorization.localSylowAmbient t P
  let H := Subgroup.normalizer (Pa : Set G)
  Subgroup.closure ({t, s} : Set G) ≤ H ∧
    (∃ P0 : Sylow ell (CFSG.pPrimeCore 2 H),
      ((P0 : Subgroup (CFSG.pPrimeCore 2 H)).map
        (H.subtype.comp (CFSG.pPrimeCore 2 H).subtype)) = Pa) ∧
    ((∀ x ∈ Pa, s * x * s⁻¹ = x) ∨ (∀ x ∈ Pa, s * x * s⁻¹ = x⁻¹))

@[expose] def allLocalPrimesOrdinary (t s : G) : Prop :=
  ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (N t) → ∃ P : Sylow ell (N t), ordinaryLocalSylow t s P

theorem allLocalPrimeStationaryCovers_of_allLocalPrimesOrdinary
    [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrec : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hord : allLocalPrimesOrdinary t (fS (s n) : G)) :
    allLocalPrimeStationaryCovers t (fS (s n) : G) := by
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  intro ell hell hdiv
  obtain ⟨P, hV, ⟨P0, hP0⟩, hact⟩ := hord ell hell hdiv
  refine ⟨P, hV, ⟨P0, hP0⟩, ?_⟩
  have hstat : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer
      ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer
        ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G))).subtype).map
          (Subgroup.normalizer
            ((((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype) : Set G)).subtype =
              ((P : Subgroup (N t)).map (N t).subtype).map (C t).subtype := by
    refine ⟨P0, ?_⟩
    rw [Subgroup.map_map]
    exact hP0
  exact ((StationaryLayerCover.stationary_layer_cover_local_prime_is_centralized_or_inverted
    hGnonab hrec n hn S fS t (fS (s n) : G) ht2 hs2 hsC hst.symm hnonab hcentral hnc p f hp
    hpodd hf hq hmodel hell P hdiv hV hstat).1).mpr hact

end CFSG.Semidihedral.AllPrime
