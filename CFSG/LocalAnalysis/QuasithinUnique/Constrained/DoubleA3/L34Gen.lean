module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1A4

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eight_dvd_card_of_four {U U' : Subgroup G} (hU : Nat.card U = 4) (hU' : Nat.card U' = 4)
    (hUU' : U ≠ U') (h2 : IsPGroup 2 ↥(U ⊔ U')) : 8 ∣ Nat.card ↥(U ⊔ U') := by
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have h4 : 4 ∣ Nat.card ↥(U ⊔ U') := hU ▸ Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ U')
  have hne : Nat.card ↥(U ⊔ U') ≠ 4 := by
    intro h4'
    have hUeq : U = U ⊔ U' :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : U ≤ U ⊔ U') (by rw [h4', hU])
    have hU'le : U' ≤ U := by rw [hUeq]; exact le_sup_right
    exact hUU' (Subgroup.eq_of_le_of_card_ge hU'le (by rw [hU, hU'])).symm
  rw [hn] at h4 hne ⊢
  have h2n : 2 ≤ n := by
    have : 2 ^ 2 ∣ 2 ^ n := by simpa using h4
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have h3n : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · exfalso
      apply hne
      have : n = 2 := by omega
      rw [this]; norm_num
    · exact h
  exact (Nat.pow_dvd_pow 2 h3n : 2 ^ 3 ∣ 2 ^ n)

theorem sup_eq_of_two_A4 {K L U L' U' : Subgroup G} (hK : IsSimpleGroup ↥K)
    (hKcard : Nat.card K = 168 ∨ Nat.card K = 360) (hL : IsA4Block L U) (hL' : IsA4Block L' U')
    (hLK : L ≤ K) (hL'K : L' ≤ K) (hUU' : U ≠ U') (h2 : IsPGroup 2 ↥(U ⊔ U')) :
    L ⊔ L' = K := by
  have hW : L ⊔ L' ≤ K := sup_le hLK hL'K
  by_contra hne
  have h8 : 8 ∣ Nat.card ↥(L ⊔ L') := by
    have h8' := eight_dvd_card_of_four hL.card_U hL'.card_U hUU' h2
    exact h8'.trans (Subgroup.card_dvd_of_le (sup_le (hL.le.trans le_sup_left)
      (hL'.le.trans le_sup_right)))
  have h12 : 12 ∣ Nat.card ↥(L ⊔ L') :=
    hL.card_L ▸ Subgroup.card_dvd_of_le (le_sup_left : L ≤ L ⊔ L')
  have h24 : 24 ∣ Nat.card ↥(L ⊔ L') := by
    have := Nat.lcm_dvd h8 h12
    have e : Nat.lcm 8 12 = 24 := by norm_num
    rwa [e] at this
  have hdvdK : Nat.card ↥(L ⊔ L') ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hW
  have hlt : ¬ Nat.card ↥K ≤ Nat.card ↥(L ⊔ L') := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hW h)
  have hpos : 0 < Nat.card ↥(L ⊔ L') := Nat.card_pos
  have hW24 : Nat.card ↥(L ⊔ L') = 24 := by
    obtain ⟨k, hk⟩ := h24
    rcases hKcard with h168 | h360
    · rw [h168] at hdvdK hlt
      rw [hk] at hdvdK hlt
      have hk7 : k ∣ 7 := by
        have : 24 * k ∣ 24 * 7 := by simpa using hdvdK
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      rcases (Nat.dvd_prime Nat.prime_seven).mp hk7 with h1 | h7
      · omega
      · exact (hlt (by omega)).elim
    · have hKtop : (L ⊔ L').subgroupOf K ≠ ⊤ := by
        intro htop
        exact hne (le_antisymm hW (Subgroup.subgroupOf_eq_top.mp htop))
      have hle60 : Nat.card ↥(L ⊔ L') ≤ 60 := by
        have := card_le_sixty_of_simple hK h360 hKtop
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv] at this
      rw [h360] at hdvdK
      have hk' : k ≤ 2 := by omega
      interval_cases k
      · omega
      · omega
      · exfalso
        rw [hk] at hdvdK
        norm_num at hdvdK
  have hLW : L ≤ L ⊔ L' := le_sup_left
  have hrel : L.relIndex (L ⊔ L') = 2 := by
    have := C5.card_eq_card_mul_relIndex hLW
    rw [hW24, hL.card_L] at this
    omega
  have hN : L ⊔ L' ≤ normalizer (L : Set G) := normalizer_of_relIndex_two hLW hrel
  have hL'N : L' ≤ normalizer (L : Set G) := le_sup_right.trans hN
  have h144 := C5.card_sup_mul_card_inf_of_le_normalizer hL'N
  rw [sup_comm, hW24, hL.card_L, hL'.card_L] at h144
  have h6 : Nat.card ↥(L' ⊓ L) = 6 := by omega
  exact hL.card_ne_six (inf_le_right : L' ⊓ L ≤ L) h6

end CFSG.QuasithinUnique.DoubleA3
