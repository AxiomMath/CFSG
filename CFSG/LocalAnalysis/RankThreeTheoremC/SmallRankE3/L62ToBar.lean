module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerBalance

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
  (qs_injOn qs_ker qs_inf_ker qs_not_dvd_core qs_pRank centralizer_map_quotient
    pRank_map_eq_of_coprime_ker)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3 (k3_no_index_three)

theorem l62Data_toBar {X : Type} [Group X] [Finite X] {S : Sylow 3 X} {x z : X}
    (h : L62Data X S x z) :
    ∃ (S' : Sylow 3 (Bar X)) (x' z' : Bar X), L62Bar (Bar X) S' x' z' := by
  have hsurj : Function.Surjective (barMk X) :=
    QuotientGroup.mk'_surjective (primeComplementCore (G := X) 3)
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := qs_not_dvd_core
  have hS'map : ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)) =
      (S : Subgroup X).map (barMk X) := Sylow.coe_mapSurjective _ _
  have hrank' : CFSG.Open.pRank 3
      ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)) = 3 := by
    rw [hS'map, qs_pRank (Q := (S : Subgroup X)) S.isPGroup' le_rfl]
    exact h.rank
  have hrank_top' : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) ≤ 3 :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.pRank_le_pRank_sylow Nat.prime_three
      (S.mapSurjective hsurj) ⊤).trans hrank'.le
  have hxS' : barMk X x ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)) := by
    rw [hS'map]
    exact Subgroup.mem_map_of_mem (barMk X) h.x_mem
  have hzS' : barMk X z ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)) := by
    rw [hS'map]
    exact Subgroup.mem_map_of_mem (barMk X) h.z_mem
  have hx1' : barMk X x ≠ 1 := by
    intro h1
    have hk : x ∈ (barMk X).ker := MonoidHom.mem_ker.mpr h1
    have hbot : x ∈ (S : Subgroup X) ⊓ (barMk X).ker := Subgroup.mem_inf.mpr ⟨h.x_mem, hk⟩
    rw [qs_inf_ker (Q := (S : Subgroup X)) S.isPGroup' le_rfl, Subgroup.mem_bot] at hbot
    exact h.x_ne hbot
  have hz1' : barMk X z ≠ 1 := by
    intro h1
    have hk : z ∈ (barMk X).ker := MonoidHom.mem_ker.mpr h1
    have hbot : z ∈ (S : Subgroup X) ⊓ (barMk X).ker := Subgroup.mem_inf.mpr ⟨h.z_mem, hk⟩
    rw [qs_inf_ker (Q := (S : Subgroup X)) S.isPGroup' le_rfl, Subgroup.mem_bot] at hbot
    exact h.z_ne hbot
  have hx3' : barMk X x ^ 3 = 1 := by
    rw [← map_pow, h.x_pow, map_one]
  have hz3' : barMk X z ^ 3 = 1 := by
    rw [← map_pow, h.z_pow, map_one]
  have hcent' : CFSG.Open.pRank 3 (centralizer ({barMk X x} : Set (Bar X))) ≤ 2 := by
    have hxord : orderOf x = 3 := orderOf_eq_prime h.x_pow h.x_ne
    have hS : ¬ 3 ∣ Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) := by
      intro hdvd
      have h1 : Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) ∣
          Nat.card ↥((barMk X).ker) :=
        Subgroup.card_dvd_of_le inf_le_right
      have h2 : Nat.card ↥((barMk X).ker) = Nat.card (primeComplementCore (G := X) 3) := by
        rw [qs_ker]
      rw [h2] at h1
      exact hO (hdvd.trans h1)
    have hc : centralizer ({barMk X x} : Set (Bar X)) =
        (centralizer ({x} : Set X)).map (barMk X) :=
      centralizer_map_quotient (primeComplementCore (G := X) 3) hO hxord
    rw [hc, pRank_map_eq_of_coprime_ker (barMk X) Nat.prime_three hS]
    exact h.cent
  have hzc' : ∀ g ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)),
      g * barMk X z = barMk X z * g := by
    intro g hg
    rw [hS'map] at hg
    obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← map_mul, ← map_mul, h.z_central g0 hg0]
  have hzg' : ∀ w ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)),
      (∀ g ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)),
        g * w = w * g) → w ^ 3 = 1 → w ∈ Subgroup.zpowers (barMk X z) := by
    intro w' hw' hcomm' hw3'
    rw [hS'map] at hw'
    obtain ⟨w, hwS, hwim⟩ := Subgroup.mem_map.mp hw'
    have hwcent : ∀ g ∈ (S : Subgroup X), g * w = w * g := by
      intro g hg
      have hcg : barMk X g ∈ ((S.mapSurjective hsurj : Sylow 3 (Bar X)) : Subgroup (Bar X)) := by
        rw [hS'map]
        exact Subgroup.mem_map_of_mem (barMk X) hg
      have himg : barMk X (g * w) = barMk X (w * g) := by
        rw [map_mul, map_mul, hwim]
        exact hcomm' (barMk X g) hcg
      exact qs_injOn (Q := (S : Subgroup X)) S.isPGroup' (mul_mem hg hwS) (mul_mem hwS hg) himg
    have hw3X : w ^ 3 = 1 := by
      have hp3 : w ^ 3 ∈ (S : Subgroup X) := pow_mem hwS 3
      have h1X : (1 : X) ∈ (S : Subgroup X) := one_mem _
      have himg3 : barMk X (w ^ 3) = barMk X 1 := by
        rw [map_pow, hwim, hw3', map_one]
      exact qs_injOn (Q := (S : Subgroup X)) S.isPGroup' hp3 h1X himg3
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (h.z_gen w hwS hwcent hw3X)
    rw [← hwim]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← map_zpow, hn]⟩
  have hL62 : L62Bar (Bar X) (S.mapSurjective hsurj) (barMk X x) (barMk X z) :=
    { catalog := h.catalog.quotient (primeComplementCore (G := X) 3)
      core := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.primeComplementCore_bar
        (G := X)
      rank := hrank'
      rank_top := hrank_top'
      x_mem := hxS'
      x_ne := hx1'
      x_pow := hx3'
      cent := hcent'
      z_mem := hzS'
      z_central := hzc'
      z_ne := hz1'
      z_pow := hz3'
      z_gen := hzg'
      no_normal_three := k3_no_index_three h.no_normal_three }
  exact ⟨S.mapSurjective hsurj, barMk X x, barMk X z, hL62⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
