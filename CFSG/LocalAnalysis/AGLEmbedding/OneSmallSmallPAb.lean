module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_ab' (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z)
    (hQz : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G))
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hexpR : ∀ r ∈ R, r ^ p = 1) (hFi : ¬ (p = 5 ∧ IsFi22 K))
    (hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2) : False := by
  refine hd.false_of_ab_of_sizes_of_exotic hz hB0 hQz hdec hexpR
    (hd.orbit_sizes hOrb hz hdec hFi hcard) ?_ hcard
  rintro rfl - hO hS₁4 hZ
  have hp := hd.cfg.red.prime
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set T := d1LiftX 3 H R K
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzR : z ∈ R := hz.1
  have hzp : orderOf z = 3 := hz.2.1
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
  obtain ⟨hzT, hTcard'⟩ := hd.d1LiftX_facts hz
  have hTcard : Nat.card T = 3 ^ 2 := hTcard'.trans hcard
  have hTab : IsElemAbelian 3 T :=
    ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hTcard, fun t ht => hexpR t (hTR ht)⟩
  have hZT : ∀ w ∈ fusionSet R z, w ∉ T → w ∈ Subgroup.zpowers z := fun w hw hwT =>
    mem_zpowers_of_mem_fusionSet_of_not_mem hp hTR hzR hRz hexpR hdec hO hw hwT
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨t, ht, i, rfl⟩ := hdec a ha
    obtain ⟨s, hs, j, rfl⟩ := hdec b hb
    have hts : t * s = s * t :=
      congrArg Subtype.val (hTab.1.is_comm.comm ⟨t, ht⟩ ⟨s, hs⟩)
    have hzs : Commute (z ^ i) s := (Commute.pow_left
      (show Commute z s from (hRz s (hTR hs)).symm) i)
    have hzt : Commute (z ^ j) t := (Commute.pow_left
      (show Commute z t from (hRz t (hTR ht)).symm) j)
    calc t * z ^ i * (s * z ^ j) = t * (z ^ i * s) * z ^ j := by group
      _ = t * (s * z ^ i) * z ^ j := by rw [hzs.eq]
      _ = (t * s) * (z ^ i * z ^ j) := by group
      _ = (s * t) * (z ^ j * z ^ i) := by rw [hts, ← pow_add, ← pow_add, add_comm]
      _ = s * (t * z ^ j) * z ^ i := by group
      _ = s * (z ^ j * t) * z ^ i := by rw [hzt.eq]
      _ = s * z ^ j * (t * z ^ i) := by group
  have hRcard : Nat.card R = 27 := by
    refine le_antisymm ?_ ?_
    · have h1 := card_le_mul_of_decomp (K := T) (Subgroup.zpowers_le.mpr hzR) fun r hr => by
        obtain ⟨t, ht, i, rfl⟩ := hdec r hr
        exact ⟨t, ⟨hTR ht, ht⟩, z ^ i, Subgroup.npow_mem_zpowers z i, rfl⟩
      have h2 := Subgroup.card_le_of_le (inf_le_right : R ⊓ T ≤ T)
      rw [Nat.card_zpowers, hzp] at h1
      rw [hTcard] at h2
      calc Nat.card R ≤ Nat.card (R ⊓ T : Subgroup G) * 3 := h1
        _ ≤ 3 ^ 2 * 3 := Nat.mul_le_mul_right 3 h2
        _ = 27 := by norm_num
    · have hinf : T ⊓ Subgroup.zpowers z = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
        by_contra hy1
        have := mem_zpowers_of_mem_zpowers_of_prime hp hzp hy.2 hy1
        exact hzT ((Subgroup.zpowers_le.mpr hy.1) this)
      have h1 := mul_card_le_of_inf_eq_bot hTR (Subgroup.zpowers_le.mpr hzR) hinf
      rw [hTcard, Nat.card_zpowers, hzp] at h1
      simpa using h1
  have hB0' : ∀ g ∈ (P : Subgroup G), g * z = z * g → g ∈ R := fun g hg hgz =>
    hd.inf_centralizer_le_of_b0 hB0 ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgz⟩
  have h4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  exact false_of_frame P.isPGroup' hd.cfg.ext.le_P hRcomm hexpR hRcard hTR
    (by simpa using hTcard) hzR hzT hzp hB0' hZ hZT h4

end Config

end CFSG.AGLEmbedding
