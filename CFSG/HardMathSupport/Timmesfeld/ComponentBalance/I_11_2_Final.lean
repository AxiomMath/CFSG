module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FinalAux
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Numerics
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Layer

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i112_ok_of_tables (T : Tables112) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) {L : Subgroup X}
    (hL : GLAPComponent p ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    (Subgroup.normalizer (L : Set X)).relIndex B = p ∧
      ((Nat.card ↥(Subgroup.center ↥L) = 1 ∧ p = 3 ∧ CFSG.Open.pRank p (⊤ : Subgroup ↥L) = 1 ∧
          GLATwoLocalRank p ↥L = 0) ∨ (p = 3 ∧ Nat.card ↥(Subgroup.center ↥L) = 3)) ∧
      CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) < p := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hK : CFSG.Open.IsKGroup ↥L := isKGroup_of_le hX L
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  have h2 : ∃ t : ↥L, orderOf t = 2 := T.T0 ↥L hq hK
  obtain ⟨r, a, hr1, hrel, hHa, hHr, hmaster⟩ := i112_master hp hO hB hr hL hnL h2
  have hcP : IsPGroup p ↥(Subgroup.center ↥L) := by
    have := Fact.mk hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1
      (i112_isPGroup_center_orbit (B := B) hp hO hLc (i112_self_mem_orbit (L := L)))
    exact IsPGroup.iff_card.2 ⟨n, by rw [← card_center_eq L]; exact hn⟩
  have hcard : ∃ n, Nat.card ↥(Subgroup.center ↥L) = p ^ n := by
    have := Fact.mk hp
    exact IsPGroup.iff_card.1 hcP
  have hmpos : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
    refine i112_one_le_pRank_of_dvd hp _ ?_
    rw [Subgroup.card_top]
    exact i116e_dvd_card hp hO hL
  have hzOrd : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ p ∣ Nat.card ↥(Subgroup.center ↥L) := by
    obtain ⟨n, hn⟩ := hcard
    rcases n with _ | n
    · left; simpa using hn
    · right; rw [hn]; exact dvd_pow_self p n.succ_ne_zero
  have hz0 : CFSG.Open.pRank p (Subgroup.center ↥L) = 0 ↔
      Nat.card ↥(Subgroup.center ↥L) = 1 := by
    constructor
    · intro h
      rcases hzOrd with h1 | h1
      · exact h1
      · have := i112_one_le_pRank_of_dvd hp _ h1
        omega
    · intro h
      exact i112_pRank_eq_zero_of_card_le_one hp.one_lt h.le
  have hmaster' : CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) +
      GLATwoLocalRank p ↥L + (p ^ r - 1) * CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤
      r + a + CFSG.Open.pRank p ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) +
        p ^ r * CFSG.Open.pRank p (Subgroup.center ↥L) := by
    have hPpos : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨Q, hQ⟩ : ∃ Q, p ^ r = Q + 1 := ⟨p ^ r - 1, by omega⟩
    rw [hQ] at hmaster ⊢
    simp only [Nat.add_sub_cancel]
    have e : (Q + 1) * CFSG.Open.pRank p (⊤ : Subgroup ↥L) =
        Q * CFSG.Open.pRank p (⊤ : Subgroup ↥L) + CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by ring
    omega
  have hZ0 : CFSG.Open.pRank p (Subgroup.center ↥L) = 0 →
      CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 0 ∧
      CFSG.Open.pRank p ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) = 0 := by
    intro h
    have h1 := i112_card_Z_eq_one (B := B) hLc (hz0.1 h)
    exact ⟨i112_pRank_eq_zero_of_card_le_one hp.one_lt h1.le,
      i112_pRank_eq_zero_of_card_le_one hp.one_lt
        ((Subgroup.card_le_of_le inf_le_left).trans h1.le)⟩
  have key := numerics_dichotomy hp3 (fun h => by subst h; norm_num at hp) hr1 hmaster'
    ((hHr ▸ i112_pRank_H_le hp.one_lt : a ≤ _)) (T.T1a ↥L hq hK p hp hp2)
    (T.T1b ↥L hq hK p hp hp2) (T.T2 ↥L hq hK p hp hp2) hmpos
    (i112_pRank_center_le_twoLocal hp h2) hzOrd hz0
    (fun h => T.T3 ↥L hq hK p hp hp2 hcP (by omega))
    (fun h => by
      obtain ⟨h3, h4, h5, h6⟩ := T.T11 ↥L hq hK p hp hp2 hcP h
      subst h3
      exact ⟨rfl, h4, h5, h6⟩)
    (fun hr1' hzp hp3' => by
      have hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p := by rw [hrel, hr1', pow_one]
      exact i112_pRank_Z_inf_B_le_one hp hp3' hO hB hL hnL hidx hzp)
    hZ0
    (fun hzp => by
      have h1 := i112_pRank_Z_le (B := B) hp hLc hrel hzp
      have h2' : 1 ≤ CFSG.Open.pRank p (Subgroup.center ↥L) :=
        i112_one_le_pRank_of_dvd hp _ (hzp ▸ dvd_rfl)
      exact h1.trans (Nat.le_mul_of_pos_right _ h2'))
    (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left)
    (fun h => by
      obtain ⟨h3, h4, h5, h6⟩ := h
      subst h3
      exact T.T9 ↥L hq hK h6 h4 h5)
  have hrelH : ∀ {r' : ℕ}, (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r' → r' = r :=
    fun h => Nat.pow_right_injective hp.two_le (h.symm.trans hrel)
  rcases key with hOK | ⟨hp3', hm1, hw1, hz0', hzO, ha2, hr1'⟩ |
      ⟨hp3', hm2, hw1, hz1, hzO, hmZ3, ha3, hc1, hr1'⟩
  ·
    have hzc := numerics_z_cases hOK
    obtain ⟨hr1', -, -, hmZlt, -⟩ := hOK
    have hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p := by rw [hrel, hr1', pow_one]
    refine ⟨hidx, ?_, hmZlt⟩
    exact hzc.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  ·
    exfalso
    subst hp3'
    have hmZ0 := (hZ0 hz0').1
    have hc0 := (hZ0 hz0').2
    have hind : iSupIndep (i112Fam B L) :=
      i112_iSupIndep_of_numbers hp hLc hrel (Or.inl hzO) (by rw [hmZ0, hzO]; simp)
    have hfb := T.TFA_a ↥L hq hK hzO hm1 hw1 (i112H B L) (i112_isElemAbelian_H hB)
      (by rw [hHa, ha2]; norm_num)
    obtain ⟨r', a', -, hrelB, -, hHr', hbon⟩ := i112_bonus hp hO hB hr hL hnL hind hfb
    have hr'' : r' = 1 := (hrelH hrelB).trans hr1'
    subst hr''
    have ha'' : a' = 2 := by omega
    rw [hw1, hm1, hc0, ha''] at hbon
    norm_num at hbon
  ·
    exfalso
    subst hp3'
    have hZc3 : Nat.card ↥(Subgroup.center ↥L) = 3 := hzO
    have hind : iSupIndep (i112Fam B L) :=
      i112_iSupIndep_of_numbers hp hLc hrel (Or.inr hZc3) (by rw [hmZ3, hzO, hr1']; norm_num)
    have hfb := T.TFA_b ↥L hq hK hzO hm2 hw1 (i112H B L) (i112_isElemAbelian_H hB)
      (by rw [hHa, ha3]; norm_num)
    obtain ⟨r', a', -, hrelB, -, hHr', hbon⟩ := i112_bonus hp hO hB hr hL hnL hind hfb
    have hr'' : r' = 1 := (hrelH hrelB).trans hr1'
    subst hr''
    have ha'' : a' = 3 := by omega
    rw [hw1, hm2, hc1, ha''] at hbon
    norm_num at hbon

theorem kernel11_2_of_tables (T : Tables112) : Kernel11_2 := by
  intro X _ _ hX p hp hp2 hO B hB hr L hL hnL
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨hidx, hzc, hmZlt⟩ := i112_ok_of_tables T hX hp hp2 hO hB hr hL hnL
  refine ⟨hidx, fun b hb hbn => ?_⟩
  have hZL : Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = 1 ∨
      Nat.card ↥(L ⊓ Subgroup.centralizer (L : Set X)) = p := by
    rw [card_center_eq L]
    rcases hzc with ⟨h, -⟩ | ⟨h3, h⟩
    · exact Or.inl h
    · exact Or.inr (by rw [h, h3])
  have hZc : Nat.card ↥(Subgroup.center ↥L) = 1 ∨ Nat.card ↥(Subgroup.center ↥L) = p := by
    rwa [← card_center_eq L]
  have hE := i112_isElemAbelian_Z (B := B) hLc hZc
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hE
  have hk' := pRank_eq_of_card hp.one_lt hE hk
  have hZlt : Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) < p ^ p := by
    rw [hk]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact i112_layer_simple hp hO hB hL hidx hb hbn hZL hZlt

theorem input11_6_of_tables (T : Tables112) (k : KernelT) : Input11_6 :=
  input11_6_of_kernels (kernel11_2_of_tables T) k

theorem kernelT_iff_isInnerAut : KernelT ↔
    ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsQuasisimple J → CFSG.Open.IsKGroup J →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        (∃ U : Subgroup J, U ≤ Subgroup.center J ∧ CFSG.Open.IsElemAbelian p U ∧
          Nat.card U = p ^ 2) →
        ∀ φ : MulAut J, IsPGroup p (Subgroup.zpowers φ) → IsInnerAut φ :=
  Iff.rfl

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
