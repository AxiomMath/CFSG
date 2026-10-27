module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPAb

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.orbit_sizes_fi22 (hF : KFactFi22Orbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hFi : p = 5 ∧ IsFi22 K) :
    ∀ S, D1InvSubset p H R K z S → S.ncard = 0 ∨ S.ncard = p ^ 2 - 1 := by
  obtain ⟨T₁, hT₁, -, -, -, -, -, -⟩ := hd.exists_sylow
  intro S hS
  obtain ⟨O, hO1, hO2, hO3⟩ := hd.exists_transport hz hdec hT₁ hS.1 hS.2
  rw [← hO3]
  obtain ⟨rfl, hK⟩ := hFi
  exact hF K hK T₁ O hO1 hO2

theorem D1OneSmallData.false_of_twoCore_le_of_ab (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShape : KFactSmallSylowShape)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hLa : D1SmallLa p M H Rbar K)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hab : (∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i) → (∀ r ∈ R, r ^ p = 1) →
      Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) =
        p ^ 2 → False) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 hLa
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc' : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc'.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  obtain ⟨T₁, hT₁, hs, hnab, hcK, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  rcases hShape K hs hnab hcK p hp hp2 T₁ hT₁nc hΓ hd.small with h2 | ⟨-, hZ⟩
  · exact hab hdec hexpR (by rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, h2])
  · exact hd.false_of_na hz hB0 hQz hdec hexpR hT₁ hZ

theorem D1OneSmallData.false_of_twoCore_le (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hFO : KFactFi22Orbits) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hLa : D1SmallLa p M H Rbar K)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G)) :
    False := by
  refine hd.false_of_twoCore_le_of_ab hOut hExp hShape hz hB0 hLa hQz fun hdec hexpR hcard => ?_
  by_cases hFi : p = 5 ∧ IsFi22 K
  · exact hd.false_of_ab_of_sizes hz hB0 hQz hdec hexpR
      (Or.inl (hd.orbit_sizes_fi22 hFO hz hdec hFi))
      (fun h => absurd (h.1.symm.trans hFi.1) (by decide)) hcard
  · exact hd.false_of_ab' hOrb hz hB0 hQz hdec hexpR hFi hcard

theorem D1OneSmallData.false_of_twoCore_le_fi22 (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShape : KFactSmallSylowShape) (hFO : KFactFi22Orbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hFi : p = 5 ∧ IsFi22 K)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G)) :
    False := by
  have h3 : p ≠ 3 := by rw [hFi.1]; decide
  refine hd.false_of_twoCore_le_of_ab hOut hExp hShape hz hB0 (fun h => absurd h h3) hQz
    fun hdec hexpR hcard => ?_
  exact hd.false_of_ab_of_sizes hz hB0 hQz hdec hexpR
    (Or.inl (hd.orbit_sizes_fi22 hFO hz hdec hFi)) (fun h => h3 h.1) hcard

end Config

end CFSG.AGLEmbedding
