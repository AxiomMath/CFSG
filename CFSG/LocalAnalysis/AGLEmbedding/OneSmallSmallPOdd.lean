module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVEven
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPAb

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.rbar_le_sup_centralizer_of_not_outerR (hOut : KFactSmallOutPPrime)
    (hd : D1OneSmallData p P M H R Rbar K)
    (hOR : p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K) :
    (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      K ⊔ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  by_cases hL : p = 3 ∧ IsLinThreeFour K
  · by_contra hn
    exact hOR hL.1 hL.2 hn
  · exact hd.rbar_le_sup_centralizer hOut (d1SmallLa_of_not hL)

theorem D1OneSmallData.false_of_b0_odd (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hodd : ¬ D1CzEven p z) (hIso : D1CzIso p z K)
    (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hOR : p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨hcardR, hdec⟩ := hd.card_le_and_decomp_of_b0_of_le_sup hExp hz hB0
    (hd.rbar_le_sup_centralizer_of_not_outerR hOut hOR)
  have hQz := hd.twoCore_inf_centralizer_le hNo2 hz hB0 hodd hIso hFi hcardR
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  rcases hShape K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small with h2 | ⟨-, hZ⟩
  · have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) = p ^ 2 := by
      rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, h2]
    exact hd.false_of_ab' hOrb hz hB0 hQz hdec hexpR hFi hcard
  · exact hd.false_of_na hz hB0 hQz hdec hexpR hT₁ hZ

end Config

end CFSG.AGLEmbedding
