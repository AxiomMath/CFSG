module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCount
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Final
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_RedDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem i112f_of_tenElevenOne {K : Type*} [Group K] (h : IsTenElevenOne K)
    (h9 : ¬ IsThreeNine K) :
    IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K ∨ IsSLThreeExc K ∨ IsSUThreeExc K := by
  rcases h with h | h | h | ⟨F, hF, hfin, hq, he⟩ | ⟨F, hF, hfin, q, hFq, hq, he⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · have h3 : Nat.card F % 9 = 1 ∨ Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7 := by omega
    rcases h3 with h1 | h47
    · exact absurd (Or.inl ⟨F, hF, hfin, h1, he⟩) h9
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨F, hF, hfin, h47, he⟩)))
  · have h3 : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
    rcases h3 with h25 | h25 | h8
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F, hF, hfin, q, hFq, Or.inl h25, he⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F, hF, hfin, q, hFq, Or.inr h25, he⟩)))
    · exact absurd (Or.inr ⟨F, hF, hfin, q, hFq, h8, he⟩) h9

section Core

variable {X : Type} [Group X] [Finite X]

theorem i112f_pRank_center_eq_one {L : Type} [Group L] [Finite L]
    (hZ3 : Nat.card ↥(Subgroup.center L) = 3) :
    CFSG.Open.pRank 3 (Subgroup.center L) = 1 := by
  have hE : IsElemAbelian 3 (Subgroup.center L) := by
    refine isElemAbelian_of_forall (fun a _ b hb => (Subgroup.mem_center_iff.1 hb a)) ?_
    intro z hz
    have h1 : orderOf (⟨z, hz⟩ : Subgroup.center L) ∣ 3 := hZ3 ▸ orderOf_dvd_natCard _
    have h2 : (⟨z, hz⟩ : Subgroup.center L) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_eq_of_card (by norm_num) hE
    (by rw [hZ3, pow_one])

theorem i112f_not_threeNine (T : Tables112) (TT : Tables112Types) (hX : CFSG.Open.IsKGroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hr : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) {L : Subgroup X}
    (hL : GLAPComponent 3 ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = 3)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3) : ¬ IsThreeNine ↥L := by
  intro h9
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hLc : CFSG.Open.IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hK : CFSG.Open.IsKGroup ↥L := isKGroup_of_le hX L
  have hm2 := TT.T10_6_1 ↥L hq hK h9
  have hD := T.T1b ↥L hq hK 3 hp (by norm_num) (Or.inr (by rw [hZ3]))
  obtain ⟨r, a, -, hrel, hHa, hHr, hBrank⟩ := i112_pRank_formula hp hB hnL
  have hr1 : r = 1 := by
    have h : (3 : ℕ) ^ r = 3 ^ 1 := by rw [← hrel, hidx, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  subst hr1
  have ha : a ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) :=
    hHr ▸ i112_pRank_H_le (by norm_num)
  have hc := i112_pRank_Z_inf_B_le_one hp rfl hO hB hL hnL hidx hZ3
  obtain ⟨T₀, P₀, Q₀, hT₀, hT₀2, hPT₀, ⟨eP₀⟩, ⟨eQ₀⟩⟩ := TT.T11_9 ↥L hq hK h9
  have h5 := i112f_count_five hB hLc hZ3 hnL hT₀ hT₀2 hPT₀ eP₀.symm eQ₀.symm
  have ha3 : a = 3 := by omega
  obtain ⟨ψ, hψH, hψ, T₁, P₁, Q₁, hT₁, hT₁2, hPT₁, ⟨eP₁⟩, ⟨eQ₁⟩, hPQ₁, hψT, k, hk⟩ :=
    TT.T11_9F ↥L hq hK h9 (i112H B L) (i112_isElemAbelian_H hB) (by rw [hHa, ha3]; norm_num)
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hψH
  have h6 := i112f_count_six hB hLc hZ3 hnL hT₁ hT₁2 hPT₁ eP₁.symm eQ₁.symm hPQ₁ hψ hψT hk
  omega

theorem i112f_types_three (T : Tables112) (TT : Tables112Types) (hX : CFSG.Open.IsKGroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hr : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) {L : Subgroup X}
    (hL : GLAPComponent 3 ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = 3)
    (hZ3 : Nat.card ↥(Subgroup.center ↥L) = 3)
    (hmZ : CFSG.Open.pRank 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) < 3) :
    IsHatSix ↥L ∨ IsHatSeven ↥L ∨ IsHatMTwentyTwo ↥L ∨ IsSLThreeExc ↥L ∨ IsSUThreeExc ↥L := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hLc : CFSG.Open.IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hK : CFSG.Open.IsKGroup ↥L := isKGroup_of_le hX L
  have h2 : ∃ t : ↥L, orderOf t = 2 := T.T0 ↥L hq hK
  have h9 := i112f_not_threeNine T TT hX hO hB hr hL hnL hidx hZ3
  obtain ⟨r, a, -, hrel, -, hHr, hmaster⟩ := i112_master hp hO hB hr hL hnL h2
  have hr1 : r = 1 := by
    have h : (3 : ℕ) ^ r = 3 ^ 1 := by rw [← hrel, hidx, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  subst hr1
  have hz := i112f_pRank_center_eq_one hZ3
  have hc := i112_pRank_Z_inf_B_le_one hp rfl hO hB hL hnL hidx hZ3
  have ha : a ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) :=
    hHr ▸ i112_pRank_H_le (by norm_num)
  have hD := T.T1b ↥L hq hK 3 hp (by norm_num) (Or.inr (by rw [hZ3]))
  have hm2 := T.T2 ↥L hq hK 3 hp (by norm_num)
  have hw := i112_pRank_center_le_twoLocal hp h2
  have hmZ1 : 1 ≤ CFSG.Open.pRank 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) := by
    rw [← hz, ← pRank_centreIn_eq_center (by norm_num) L]
    exact CFSG.SectionRank.pRank_mono (by norm_num) (i112_centreIn_le_Z hLc i112_self_mem_orbit)
  rw [hz] at hmaster hm2 hw
  simp only [pow_one] at hmaster
  by_cases hEq : 6 ≤ CFSG.Open.pRank 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) +
      GLATwoLocalRank 3 ↥L + CFSG.Open.pRank 3 (⊤ : Subgroup ↥L)
  ·
    have hDeq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) + 1 := by omega
    rcases TT.T10_6_8 ↥L hq hK hZ3 (by omega) hDeq with hON | hLie
    · have := TT.TON ↥L hq hK hON
      omega
    · rcases TT.T10_11_3 ↥L hq hK hZ3 hLie (by omega) with h1 | hG2
      · exact i112f_of_tenElevenOne h1 h9
      · exact absurd hDeq (TT.TG23 ↥L hq hK hG2)
  ·
    rcases TT.T10_11_2 ↥L hq hK hZ3 (by omega) with h1 | hON
    · exact i112f_of_tenElevenOne h1 h9
    · have := TT.TON ↥L hq hK hON
      omega

theorem i112f_core (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    p = 3 ∧ (Subgroup.normalizer (L : Set X)).relIndex B = 3 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) ≤ 2 ∧
      (IsElemAbelian 3 (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ∧
        Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ≤ 9) ∧
      (IsLTwoOddPow ↥L ∨ IsHatSix ↥L ∨ IsHatSeven ↥L ∨ IsHatMTwentyTwo ↥L ∨ IsSLThreeExc ↥L ∨
        IsSUThreeExc ↥L) := by
  obtain ⟨hidx, hz, hmZ⟩ := i112_ok_of_tables T hX hp hp2 hO hB hr hL hnL
  have hp3 : p = 3 := hz.elim (fun h => h.2.1) (fun h => h.1)
  subst hp3
  have hLc : CFSG.Open.IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hK : CFSG.Open.IsKGroup ↥L := isKGroup_of_le hX L
  have hZc : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = 3 :=
    hz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  have hE := i112_isElemAbelian_Z (B := B) hLc hZc
  obtain ⟨k, hk⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_card_eq_of_isElemAbelian hp hE
  have hk' := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_eq_of_card hp.one_lt hE hk
  have hcard : Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ≤ 9 := by
    rw [hk, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hz with ⟨hc1, -, hm, hw⟩ | ⟨-, hc3⟩
  · have hL2 := TL.T ↥L hq hK hc1 hm hw
    exact ⟨rfl, hidx, i112f_pRank_mulAut_L2 hL2, ⟨hE, hcard⟩,
      Or.inl (i112f_isLTwoOddPow_of_isL2 hL2)⟩
  · have htype := i112f_types_three T TT hX hO hB hr hL hnL hidx hc3 hmZ
    refine ⟨rfl, hidx, ?_, ⟨hE, hcard⟩, Or.inr htype⟩
    rcases htype with h6 | h7 | h22 | hSL | hSU
    · exact i112f_pRank_mulAut_hatSix h6
    · exact i112f_pRank_mulAut_hatSeven h7
    · exact TT.T10_10 ↥L hq hK (Or.inl h22)
    · obtain ⟨F, hF, hfin, hq9, he⟩ := hSL
      by_cases h4 : Nat.card F = 4
      · exact pRank_mulAut_le_two_of_isSLThreeFour ⟨F, hF, hfin, h4, he⟩ hq.1
      · exact TT.T10_10 ↥L hq hK (Or.inr (Or.inl ⟨F, hF, hfin, ⟨hq9, h4⟩, he⟩))
    · exact TT.T10_10 ↥L hq hK (Or.inr (Or.inr hSU))

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
