module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup M11Model CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.AGLEmbeddingD2

theorem m11TwoSignalizer_proved :
    KFactM11TwoSignalizer := by
  intro K _ _ hK Q
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e' : K ≃* ↥NativeSporadic.M11 := e.trans eC.symm
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e' (IsPGroup.of_card sylowR_card) sylowR_index Q
  have hcard : Nat.card (Q : Subgroup K) = 3 ^ 2 := by
    rw [hΦ, ← sylowR_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Φ.injective).symm.toEquiv
  have hel : IsElemAbelian 3 (Q : Subgroup K) := by
    have hT : ∀ t ∈ sylowR.map Φ.toMonoidHom, ∃ r ∈ sylowR, t = Φ r := fun t ht => by
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ht
      exact ⟨r, hr, rfl⟩
    rw [hΦ]
    refine ⟨?_, fun t ht => ?_⟩
    · rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      intro s hs
      rw [mem_centralizer_iff]
      intro t ht
      obtain ⟨r, hr, rfl⟩ := hT s hs
      obtain ⟨r', hr', rfl⟩ := hT t ht
      rw [← map_mul, ← map_mul, sylowR_comm r' hr' r hr]
    · obtain ⟨r, hr, rfl⟩ := hT t ht
      rw [← map_pow, sylowR_cube r hr, map_one]
  refine ⟨hel, fun u huQ hu3 => ?_⟩
  have hmax : ∀ Y : Subgroup K, normalizer ((Q : Subgroup K) : Set K) ≤ Y →
      Y = normalizer ((Q : Subgroup K) : Set K) ∨ Y = ⊤ := by
    obtain ⟨R₀, hR₀⟩ := m11_three_localData
    have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_three (by norm_num)
    exact (torusLocal_sylow e' hT (by
      rw [hT.1, card_M11, factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num)
        (by norm_num) (by norm_num)]) Q).2.1
  have hrank : 1 ≤ CFSG.Open.pRank 3 (Q : Subgroup K) :=
    (show 1 ≤ 2 by norm_num).trans (pRank_ge_of_elemAbelian_card (by norm_num) le_rfl hel hcard)
  have hu' : u ∈ sylowR.map Φ.toMonoidHom := hΦ ▸ huQ
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu'
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h1 : Φ.toMonoidHom 1 = 1 := map_one _
    rw [h1, orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  obtain ⟨x, y, hx, hy, hxy, hzx, hzy, hxN⟩ := sylowR_klein z hz hz1
  refine top_le_gamma_sup_of_klein (x := Φ x) (y := Φ y) hrank hmax ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, hx, map_one]
  · rw [← map_mul, hy, map_one]
  · rw [← map_mul, ← map_mul, hxy]
  · change Φ z * Φ x * (Φ z)⁻¹ = Φ y
    rw [← map_inv, ← map_mul, ← map_mul, hzx]
  · change Φ z * Φ y * (Φ z)⁻¹ = Φ x * Φ y
    rw [← map_inv, ← map_mul, ← map_mul, hzy, map_mul]
  · intro hn
    apply hxN
    rw [hΦ, ← Subgroup.map_equiv_normalizer_eq] at hn
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hn
    rwa [← Φ.injective hwx]

end CFSG.LocalAnalysis.RankThreeTheoremC
