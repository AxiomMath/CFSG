module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HypOne

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sol78Generate_of_gen {L K : Subgroup G} {u : G}
    (hu : u ∈ centralizer (K : Set G)) (hu2 : orderOf u = 2)
    (hZ : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u)
    (hgen : ∀ l ∈ L, K.map (conjHom l) ≠ K → K ⊔ K.map (conjHom l) = L) :
    Sol78Generate L K u := by
  intro l hl hw
  obtain ⟨v, hv, hwv, -⟩ := hw
  have hu' : ∀ k ∈ K, k * u = u * k := fun k hk => mem_centralizer_iff.1 hu k hk
  have huu : u * u = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at this
  have hne : K.map (conjHom l) ≠ K := by
    intro heq
    have hwK : ∀ k ∈ K, k * (l * u * l⁻¹) = (l * u * l⁻¹) * k := by
      intro k hk
      have hk' := conj_inv_mem_of_map_eq heq hk
      have h1 := hu' _ hk'
      calc k * (l * u * l⁻¹) = l * ((l⁻¹ * k * l) * u) * l⁻¹ := by group
        _ = l * (u * (l⁻¹ * k * l)) * l⁻¹ := by rw [h1]
        _ = (l * u * l⁻¹) * k := by group
    have hvK : ∀ k ∈ K, k * v = v * k := by
      intro k hk
      have h2 : v = u * (l * u * l⁻¹) := by
        rw [hwv, ← mul_assoc, huu, one_mul]
      rw [h2, ← mul_assoc, hu' k hk, mul_assoc, hwK k hk, ← mul_assoc]
    obtain ⟨k₀, hk₀, n, hvn⟩ := exists_mul_zpow_of_mem_sup hu' hv.1.1
    have hk₀c : ∀ k ∈ K, k₀ * k = k * k₀ := by
      intro k hk
      have hcu : Commute u k := (hu' k hk).symm
      have hcv : Commute v k := (hvK k hk).symm
      have hk0 : k₀ = v * u ^ (-n) := by rw [hvn, mul_assoc, ← zpow_add]; simp
      rw [hk0]
      exact (hcv.mul_left (hcu.zpow_left (-n))).eq
    have hkz : k₀ ∈ (center K).map K.subtype := mem_center_map_iff.2 ⟨hk₀, hk₀c⟩
    have hun : u ^ n = 1 ∨ u ^ n = u := by
      have h : u ^ (n % 2) = u ^ n := by simpa [hu2] using zpow_mod_orderOf u n
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · left
        rw [← h, h0]
        simp
      · right
        rw [← h, h1]
        simp
    rcases hun with h1 | h1
    · apply hv.1.2.1
      have hvk : v = k₀ := by rw [hvn, h1, mul_one]
      rw [hvk]
      exact hkz
    · have hv1 : v = k₀ * u := by rw [hvn, h1]
      have hvv : v * v = 1 := by
        have : v ^ 2 = 1 := by rw [← hv.1.2.2]; exact pow_orderOf_eq_one v
        rwa [pow_two] at this
      have hkk : k₀ * k₀ = 1 := by
        have h2 : v * v = k₀ * k₀ * (u * u) := by
          rw [hv1]
          calc k₀ * u * (k₀ * u) = k₀ * (u * k₀) * u := by simp only [mul_assoc]
            _ = k₀ * (k₀ * u) * u := by rw [hu' k₀ hk₀]
            _ = k₀ * k₀ * (u * u) := by simp only [mul_assoc]
        rwa [h2, huu, mul_one] at hvv
      rcases hZ k₀ hkz hkk with h0 | h0
      · have hv_eq : v = u := by rw [hv1, h0, one_mul]
        have hw1 : l * u * l⁻¹ = 1 := by rw [hwv, hv_eq, huu]
        have hu1 : u = 1 := by
          have := congrArg (fun x => l⁻¹ * x * l) hw1
          simpa [mul_assoc] using this
        rw [hu1, orderOf_one] at hu2
        exact absurd hu2 (by decide)
      · have hv_eq : v = 1 := by rw [hv1, h0, huu]
        have h2 := hv.1.2.2
        rw [hv_eq, orderOf_one] at h2
        exact absurd h2 (by decide)
  exact hgen l hl hne

theorem sol78Local39Q_of_squareFacts {L K S : Subgroup G} {u d : G} (hu2 : orderOf u = 2)
    (hKL : K ≤ L) (hKcen : u ∈ centralizer (K : Set G)) (h35 : K = componentProduct K u)
    (hKC : ∀ S' : Subgroup G, S' ≤ L ⊓ centralizer ({u} : Set G) → IsPGroup 2 S' → S' ≤ K)
    (hgen : ∀ l ∈ L, K.map (conjHom l) ≠ K → K ⊔ K.map (conjHom l) = L)
    (hlt : twoAdic K < twoAdic L) (hSq : SquareFacts K S u d) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u := fun z hz hzz =>
    hSq.central_inv z (mem_center_map_iff.1 hz).1 hzz (mem_center_map_iff.1 hz).2
  have hSa : twoAdic K = twoAdic S := by
    unfold twoAdic
    rw [hSq.S_card, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  refine ⟨?_, ?_, sol78Generate_of_gen hKcen hu2 hZ hgen⟩
  · have hSp : IsPGroup 2 S := IsPGroup.of_card hSq.S_card
    have hu4 : u ^ 4 = 1 := by
      calc u ^ 4 = (u * u) * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hSq.u_sq, one_mul]
    obtain ⟨x, hxK, hxS⟩ := exists_conj_mem_of_card_pow_four hSq.S_le hSq.S_card hSq.u_mem hu4
    have hcx : x⁻¹ * u * x = u := by
      calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
        _ = x⁻¹ * (x * u) := by rw [(hSq.u_central x hxK).symm]
        _ = u := by group
    have huS : u ∈ S := hcx ▸ hxS
    have hcardS : Nat.card S < 2 ^ (Nat.card L).factorization 2 := by
      rw [hSq.S_card]
      exact Nat.pow_lt_pow_right (by norm_num) hlt
    obtain ⟨T, hTL, hTp, hST⟩ := exists_lt_of_card_lt (hSq.S_le.trans hKL) hSp hcardS
    refine vPairs_nonempty_of_sylow hu2 huS (fun s hs => ?_) ?_ hTL hTp hST
      (fun z hz _ => (le_sup_left : K ≤ K ⊔ zpowers u) (hSq.S_le hz)) hZ ?_
    · exact ⟨hKL (hSq.S_le hs),
        mem_centralizer_singleton_iff.2 (hSq.u_central s (hSq.S_le hs))⟩
    · intro S' hS'le hS'p hSS'
      have hS'K : S' ≤ K := hKC S' hS'le hS'p
      have hc := card_le_two_pow_of_isPGroup hS'p hS'K
      exact (Subgroup.eq_of_le_of_card_ge hSS' (by rw [hSq.S_card]; exact hc)).symm
    · rw [inf_eq_left.2 hSq.S_le]
      exact hSa.le
  · intro v hv g hg
    obtain ⟨hug, hKg⟩ := map_conj_eq_of_hyp35 h35 hg
    have hw := vMaximal_conj hKg hug hv
    have hsq : (∃ x ∈ K, x * x = v) ↔ (∃ y ∈ K, y * y = g * v * g⁻¹) := by
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨g * x * g⁻¹, conj_mem_of_map_eq hKg hx, by group⟩
      · rintro ⟨y, hy, hyw⟩
        refine ⟨g⁻¹ * y * g, conj_inv_mem_of_map_eq hKg hy, ?_⟩
        calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
          _ = v := by rw [hyw]; group
    obtain ⟨c, hcK, hc⟩ := hSq.exists_conj hv hw hsq
    exact ⟨c, ⟨hKL hcK, mem_centralizer_singleton_iff.2 (hSq.u_central c hcK)⟩, hc.symm⟩

end CFSG.EvenSporadicStandard.Induction
