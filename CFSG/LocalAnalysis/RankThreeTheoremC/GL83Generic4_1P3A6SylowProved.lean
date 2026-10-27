module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup A6Model

private theorem factor_of_dvd_ten {n : ℕ} (hn : n ∣ 10) (m d : ℕ) (hmd : m * d = n)
    (hm : m ≡ 1 [MOD 3]) : m = 1 ∨ d = 1 := by
  have hn' : n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10 := by
    have h : n ∈ Nat.divisors 10 := Nat.mem_divisors.2 ⟨hn, by norm_num⟩
    have h10 : Nat.divisors 10 = {1, 2, 5, 10} := by decide
    rw [h10] at h
    simpa using h
  have hm10 : m ≤ 10 := Nat.le_of_dvd (by norm_num) ((Dvd.intro d hmd).trans hn)
  unfold Nat.ModEq at hm
  interval_cases m <;> omega

private theorem elemAbelian_of_map {K : Type} [Group K] (Φ : PSL29 ≃* K) :
    IsElemAbelian 3 (uHom.range.map Φ.toMonoidHom) ∧
      Nat.card (uHom.range.map Φ.toMonoidHom) = 3 ^ 2 := by
  have hT : ∀ t ∈ uHom.range.map Φ.toMonoidHom, ∃ a, t = Φ (ut a) := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨a, rfl⟩ := mem_range_iff.mp hz
    exact ⟨a, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← Subgroup.le_centralizer_iff_isMulCommutative]
    intro s hs
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨a, rfl⟩ := hT s hs
    obtain ⟨b, rfl⟩ := hT t ht
    rw [← map_mul, ← map_mul, ut_mul, ut_mul, add_comm]
  · intro t ht
    obtain ⟨a, rfl⟩ := hT t ht
    rw [← map_pow, pow_succ, pow_two, ut_cube, map_one]
  · rw [← uHom_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ Φ.injective).symm.toEquiv

theorem a6SylowData_proved : A6SylowData := by
  intro K _ _ hK T
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, hΦ⟩ := exists_equiv_of_sylow hK T
  have hK360 : Nat.card K = 360 := by rw [← Nat.card_congr Φ.toEquiv, psl29_card]
  have hT := elemAbelian_of_map Φ
  rw [← hΦ] at hT
  refine ⟨hT.1, hT.2, fun Y hY => ?_⟩
  obtain ⟨n, hnN, hn4⟩ := exists_order_four
  have hΦn : Φ n ∈ normalizer ((T : Subgroup K) : Set K) := by
    rw [hΦ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem Φ.toMonoidHom hnN
  have h4 : 4 ∣ Nat.card (normalizer ((T : Subgroup K) : Set K)) := by
    have h := Subgroup.orderOf_dvd_natCard (normalizer ((T : Subgroup K) : Set K)) hΦn
    rwa [MulEquiv.orderOf_eq, hn4] at h
  have h9 : 9 ∣ Nat.card (normalizer ((T : Subgroup K) : Set K)) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (T : Subgroup K)))
    rwa [hT.2] at h
  have h36 : 36 ∣ Nat.card (normalizer ((T : Subgroup K) : Set K)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 9) h4 h9
  have hdvd : (normalizer ((T : Subgroup K) : Set K)).index ∣ 10 := by
    obtain ⟨c, hc⟩ := h36
    have h := (normalizer ((T : Subgroup K) : Set K)).index_mul_card
    rw [hK360, hc] at h
    have h' : 36 * ((normalizer ((T : Subgroup K) : Set K)).index * c) = 36 * 10 := by
      calc 36 * ((normalizer ((T : Subgroup K) : Set K)).index * c)
          = (normalizer ((T : Subgroup K) : Set K)).index * (36 * c) := by ring
        _ = 36 * 10 := by rw [h]
    exact ⟨c, (Nat.eq_of_mul_eq_mul_left (by norm_num) h').symm⟩
  exact eq_normalizer_or_top_of_index T rfl (factor_of_dvd_ten hdvd) hY

end CFSG.LocalAnalysis.RankThreeTheoremC
