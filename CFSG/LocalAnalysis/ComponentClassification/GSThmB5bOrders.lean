module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTable
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit
public import CFSG.ClassicalInvolution.Orders.Classical

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem statedClassicalModel_of_lieModel_ne_zero {G : Type} [Group G]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : Blueprint.LieModel G t n p f) : Assembly.LowTwoRank.StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem lt_div_of_mul_succ_le {X d k N : ℕ} (hd0 : 0 < d) (hdk : d ≤ k)
    (hX : k * (N + 1) ≤ X) : N < X / d := by
  have h1 : N + 1 ≤ X / k := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hX)
  have h2 : X / k ≤ X / d := Nat.div_le_div_left hdk hd0
  omega

theorem ordA_one_ne_2520 (m : ℕ) : Open.ordA 1 m ≠ 2520 := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  rcases Nat.lt_or_ge m 18 with hm | hm
  · interval_cases m <;> decide
  · have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (2520 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 18 * 323 ≤ m * (m ^ 2 - 1) := by
        have h2 : 323 ≤ m ^ 2 - 1 := by
          have : 18 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    exact (lt_div_of_mul_succ_le hg hle hX).ne'

theorem le_prod_of_mem {s : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ i ∈ s, 1 ≤ g i) {j : ℕ} (hj : j ∈ s) :
    g j ≤ ∏ i ∈ s, g i :=
  Finset.single_le_prod hg hj

theorem ordBC_two_gt {q : ℕ} (hq : 3 ≤ q) : 2520 < Open.ordBC 2 q := by
  unfold Open.ordBC
  have hg : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  refine lt_div_of_mul_succ_le hg hle ?_
  have h4 : 81 ≤ q ^ (2 * 2) := by
    calc 81 = 3 ^ (2 * 2) := by norm_num
      _ ≤ q ^ (2 * 2) := Nat.pow_le_pow_left hq _
  have hpos : ∀ i ∈ Finset.Icc 1 2, 1 ≤ q ^ (2 * i) - 1 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : 3 ≤ q ^ (2 * i) := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  have hprod : q ^ (2 * 2) - 1 ≤ ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) :=
    le_prod_of_mem hpos (by decide)
  have h80 : 80 ≤ q ^ (2 * 2) - 1 := by omega
  calc 2 * (2520 + 1) ≤ 81 * 80 := by norm_num
    _ ≤ q ^ (2 * 2) * (q ^ (2 * 2) - 1) := Nat.mul_le_mul h4 h80
    _ ≤ q ^ (2 * 2) * ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) := Nat.mul_le_mul_left _ hprod

theorem ordA_three_gt {q : ℕ} (hq : 3 ≤ q) : 2520 < Open.ordA 3 q := by
  unfold Open.ordA
  have hg : 0 < Nat.gcd (3 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : Nat.gcd (3 + 1) (q - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  refine lt_div_of_mul_succ_le hg hle ?_
  have h6 : 729 ≤ q ^ (3 * (3 + 1) / 2) := by
    calc 729 = 3 ^ (3 * (3 + 1) / 2) := by norm_num
      _ ≤ q ^ (3 * (3 + 1) / 2) := Nat.pow_le_pow_left hq _
  have hpos : ∀ i ∈ Finset.Icc 2 (3 + 1), 1 ≤ q ^ i - 1 := by
    intro i hi
    have hi1 : 1 ≤ i := le_trans (by norm_num) (Finset.mem_Icc.mp hi).1
    have : 3 ≤ q ^ i := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  have hprod : q ^ 4 - 1 ≤ ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) :=
    le_prod_of_mem (g := fun i => q ^ i - 1) hpos (by decide)
  have h80 : 80 ≤ q ^ 4 - 1 := by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq _
    omega
  calc 4 * (2520 + 1) ≤ 729 * 80 := by norm_num
    _ ≤ q ^ (3 * (3 + 1) / 2) * (q ^ 4 - 1) := Nat.mul_le_mul h6 h80
    _ ≤ q ^ (3 * (3 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) :=
      Nat.mul_le_mul_left _ hprod

theorem ordTwistedA_three_gt {q : ℕ} (hq : 3 ≤ q) : 2520 < Open.ordTwistedA 3 q := by
  unfold Open.ordTwistedA
  have hg : 0 < Nat.gcd (3 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : Nat.gcd (3 + 1) (q + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  refine lt_div_of_mul_succ_le hg hle ?_
  have h6 : 729 ≤ q ^ (3 * (3 + 1) / 2) := by
    calc 729 = 3 ^ (3 * (3 + 1) / 2) := by norm_num
      _ ≤ q ^ (3 * (3 + 1) / 2) := Nat.pow_le_pow_left hq _
  have hpos : ∀ i ∈ Finset.Icc 2 (3 + 1), 1 ≤ ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    intro i hi
    have hi1 : 1 ≤ i := le_trans (by norm_num) (Finset.mem_Icc.mp hi).1
    have h3 : (3 : ℤ) ≤ (q : ℤ) ^ i := by
      have : 3 ≤ q ^ i := le_trans hq (Nat.le_self_pow (by omega) q)
      exact_mod_cast this
    have h1 : (-1 : ℤ) ^ i ≤ 1 := by
      rcases neg_one_pow_eq_or ℤ i with h | h
      · rw [h]
      · rw [h]; norm_num
    omega
  have hprod : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat ≤
      ∏ i ∈ Finset.Icc 2 (3 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
    le_prod_of_mem (g := fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hpos (by decide)
  have h28 : 28 ≤ ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat := by
    have : (27 : ℤ) ≤ (q : ℤ) ^ 3 := by
      have : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq _
      exact_mod_cast this
    omega
  calc 4 * (2520 + 1) ≤ 729 * 28 := by norm_num
    _ ≤ q ^ (3 * (3 + 1) / 2) * ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat := Nat.mul_le_mul h6 h28
    _ ≤ q ^ (3 * (3 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (3 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
      Nat.mul_le_mul_left _ hprod

theorem ordTwistedD_four_gt {q : ℕ} (hq : 3 ≤ q) : 2520 < Open.ordTwistedD 4 q := by
  unfold Open.ordTwistedD
  have hg : 0 < Nat.gcd 4 (q ^ 4 + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hle : Nat.gcd 4 (q ^ 4 + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  refine lt_div_of_mul_succ_le hg hle ?_
  have h12 : 4 * (2520 + 1) ≤ q ^ (4 * (4 - 1)) := by
    calc 4 * (2520 + 1) ≤ 3 ^ (4 * (4 - 1)) := by norm_num
      _ ≤ q ^ (4 * (4 - 1)) := Nat.pow_le_pow_left hq _
  have hpos : 1 ≤ ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) := by
    refine Finset.one_le_prod fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : 3 ≤ q ^ (2 * i) := le_trans hq (Nat.le_self_pow (by omega) q)
    omega
  calc 4 * (2520 + 1) ≤ q ^ (4 * (4 - 1)) := h12
    _ ≤ q ^ (4 * (4 - 1)) * (q ^ 4 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ q ^ (4 * (4 - 1)) * (q ^ 4 + 1) * ∏ i ∈ Finset.Icc 1 (4 - 1), (q ^ (2 * i) - 1) :=
      Nat.le_mul_of_pos_right _ hpos

theorem three_le_pow_of_odd_prime {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact le_trans h3 (Nat.le_self_pow (by omega) p)

theorem fusionZStar_eq_of_center_eq_bot {Y : Type*} [Group Y]
    (hZ : center (Y ⧸ pPrimeCore 2 Y) = ⊥) : Open.fusionZStar Y = pPrimeCore 2 Y := by
  have hN : Open.fusionOddCore Y = pPrimeCore 2 Y := fusionOddCore_eq_pPrimeCore Y
  have hcen : center (Y ⧸ Open.fusionOddCore Y) = ⊥ :=
    center_eq_bot_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hN).symm hZ
  unfold Open.fusionZStar
  rw [hcen, MonoidHom.comap_bot, QuotientGroup.ker_mk', hN]

theorem card_zStarBar_of_center_eq_bot {H : Type} [Group H] {K : Subgroup H}
    (hZ : center (OddBar K) = ⊥) : Nat.card (ZStarBar K) = Nat.card (OddBar K) := by
  have h := fusionZStar_eq_of_center_eq_bot hZ
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq h).toEquiv

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem oddBar_J_A5_of_oddBar_K_A7 (hB1 : ConjFixStatement) (hCF : CFProp23Fusion)
    (hKa : conjugate h.K h.a = h.K)
    (hK : Nonempty (OddBar h.K ≃* alternatingGroup (Fin 7))) :
    Nonempty (OddBar h.J ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hK
  have hcard : Nat.card (OddBar h.K) = 2520 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_seven]
  have hZ : center (OddBar h.K) = ⊥ :=
    center_eq_bot_of_mulEquiv e.symm (alternatingGroup.center_eq_bot (by simp))
  have hcardZ : Nat.card (ZStarBar h.K) = 2520 := by
    rw [card_zStarBar_of_center_eq_bot hZ, hcard]
  rcases h.table hB1 hCF with ⟨n, hn, hJ, (⟨-, hK' | hK'⟩ | ⟨hKa', -⟩)⟩ |
      ⟨-, -, hZ', -⟩ | ⟨-, -, hZ', -⟩ | ⟨p, f, hp, hp2, hf, -, -, hK'⟩ |
      ⟨p, f, hp, hp2, hf, -, -, -, hK'⟩ | ⟨-, -, -, -, -, -, -, hKa', -⟩ |
      ⟨p, f, hp, hp2, hf, -, -, hK'⟩
  ·
    obtain ⟨e'⟩ := hK'
    have h1 : Nat.card (alternatingGroup (Fin (n + 2))) = 2520 := by
      rw [← Nat.card_congr e'.toEquiv, hcard]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : n + 2 = 7 := by
      rcases hn with rfl | rfl | rfl
      · rfl
      · exact absurd h1 (by decide)
      · exact absurd h1 (by decide)
    have h5 : n = 5 := by omega
    subst h5
    exact hJ
  ·
    obtain ⟨e'⟩ := hK'
    have h1 : Nat.card (alternatingGroup (Fin (n + 4))) = 2520 := by
      rw [← Nat.card_congr e'.toEquiv, hcard]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    rcases hn with rfl | rfl | rfl <;> exact absurd h1 (by decide)
  · exact absurd hKa hKa'
  · exact absurd hZ hZ'
  · exact absurd hZ hZ'
  ·
    have hq := three_le_pow_of_odd_prime hp hp2 hf
    rcases hK' with hL | hL | ⟨e', hfe, hL⟩
    · have := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL)).1 rfl
      rw [hcardZ] at this
      exact absurd this (ordA_three_gt hq).ne
    · have := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL)).2.1 rfl
      rw [hcardZ] at this
      exact absurd this (ordTwistedA_three_gt hq).ne
    · have := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL)).2.2.2.2.2 rfl
      rw [hcardZ] at this
      have hq' : 3 ≤ p ^ e' := three_le_pow_of_odd_prime hp hp2 (by omega)
      exact absurd this (ordTwistedD_four_gt hq').ne
  ·
    have := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hK')).1 rfl
    rw [hcard] at this
    exact absurd this.symm (ordA_one_ne_2520 _)
  · exact absurd hKa hKa'
  ·
    have hq := three_le_pow_of_odd_prime hp hp2 hf
    have := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hK')).2.2.1 rfl
    rw [hcard] at this
    exact absurd this (ordBC_two_gt hq).ne

end Hyp52

end CFSG.ComponentClassification.GSThmB
