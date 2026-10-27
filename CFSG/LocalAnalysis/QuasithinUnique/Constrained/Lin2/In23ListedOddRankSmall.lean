module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankBlk
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankMat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankL4
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.SectionRank

theorem false_of_two_pow_dvd {n c : ℕ} (hn : 2 ≤ n) (h : 2 ^ (3 * n) ∣ c) (hc : ¬ 64 ∣ c) :
    False := by
  have h6 : 2 ^ 6 ∣ 2 ^ (3 * n) := pow_dvd_pow 2 (by omega)
  exact hc (by simpa using h6.trans h)

theorem le_two_of_two_pow_dvd {n c : ℕ} (h : 2 ^ (3 * n) ∣ c) (hc : ¬ 512 ∣ c) : n ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have h9 : 2 ^ 9 ∣ 2 ^ (3 * n) := pow_dvd_pow 2 (by omega)
  exact hc (by simpa using h9.trans h)

theorem card_of_openPSL {X : Type} [Group X] {n p f : ℕ} (hn : 2 ≤ n)
    (h : CFSG.Open.StatedClassicalModel X .PSL n p f) :
    Nat.card X = ((p ^ f) ^ (n * (n - 1) / 2) * ∏ index ∈ Finset.Icc 2 n, ((p ^ f) ^ index - 1)) /
      Nat.gcd n (p ^ f - 1) :=
  CFSG.QuasithinUnique.Lin2.card_of_statedPSL hn h

theorem card_L33 {X : Type} [Group X] (h : CFSG.Open.StatedClassicalModel X .PSL 3 3 1) :
    Nat.card X = 5616 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three h

theorem card_L42 {X : Type} [Group X] (h : CFSG.Open.StatedClassicalModel X .PSL 4 2 1) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_alt {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m) (e : X ≃* alternatingGroup (Fin m)) :
    Nat.card X = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem card_of_cover_alt {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (hc : Nat.card (Subgroup.center X) = 3)
    (e : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin m)) :
    Nat.card X = 3 * (m.factorial / 2) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    card_of_alt hm e, mul_comm]

section Vacuous

variable {G : Type} [Group G] {K : Subgroup G} {n : ℕ}

theorem false_alt_six (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (e : ↥K ≃* alternatingGroup (Fin 6)) : False := by
  rw [card_of_alt (by norm_num) e] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

theorem false_cover_six (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (hc : Nat.card (Subgroup.center ↥K) = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) : False := by
  rw [card_of_cover_alt (by norm_num) hc e] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

theorem false_alt_seven (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (e : ↥K ≃* alternatingGroup (Fin 7)) : False := by
  rw [card_of_alt (by norm_num) e] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

theorem false_cover_seven (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (hc : Nat.card (Subgroup.center ↥K) = 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7)) : False := by
  rw [card_of_cover_alt (by norm_num) hc e] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

theorem false_L33 (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (h : CFSG.Open.StatedClassicalModel ↥K .PSL 3 3 1) : False := by
  rw [card_L33 h] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

theorem false_M11 (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (e : ↥K ≃* NativeSporadic.Carrier .M11) : False := by
  rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .M11) = 7920 from
    CFSG.Sporadic.Mathieu.card_M11] at hd
  exact false_of_two_pow_dvd hn hd (by decide)

end Vacuous


section Rank

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem two_le_pRank_top_of_hasElemAb {X : Type} [Group X] [Finite X] (h : Id2519.HasElemAb 3 9 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨A, hA, hc⟩ := h
  exact le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num)

theorem two_le_pRank_three_of_equiv {X : Type} [Group X] [Finite X] (e : ↥K ≃* X)
    (h : Id2519.HasElemAb 3 9 X) : 2 ≤ CFSG.Open.pRank 3 K := by
  exact le_pRank_of_equiv e (by norm_num) (two_le_pRank_top_of_hasElemAb h)

theorem two_le_pRank_of_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    2 ≤ CFSG.Open.pRank p K := by
  have : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥K) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  rw [pRank_quotient_eq (CFSG.pCore 2 ↥K) hN] at h
  exact le_pRank_of_equiv (MulEquiv.refl ↥K) hp.one_lt h

theorem isPGroup_two_of_isElemAbelian {X : Type} [Group X] {U : Subgroup X}
    (h : IsElemAbelian 2 U) : IsPGroup 2 U := CFSG.Open.IsElemAbelian.isPGroup h

end Rank

section Families

variable {G : Type} [Group G] [Finite G] {K L : Subgroup G} {n : ℕ}

theorem false_bender (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥) (hn : 2 ≤ n)
    (hLK : L ≤ K) (h : fusionIsBenderGroup ↥K) : False := by
  obtain ⟨q, k, hB⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup h
  obtain ⟨Ub, hU1, hUe, -, hnorm, hns⟩ := exists_blockU_K hs hl hZ hn hLK
  exact false_of_benderBorel hB hU1 (isPGroup_two_of_isElemAbelian hUe) hnorm hns

theorem ne_two_of_fermat_or_mersenne {p : ℕ} (h : Ch1.IsFermatOrMersennePrime p) : p ≠ 2 := by
  rcases h.2 with ⟨k, rfl⟩ | ⟨k, hk, rfl⟩
  · have : 2 ^ 1 ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  · have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

theorem false_L2p
    (hs : IsShort2 L) (hl : IsLin2Type L n) (hZ : blockZ L = ⊥) (hn : 2 ≤ n)
    (hLK : L ≤ K) {p : ℕ} (hp : Ch1.IsFermatOrMersennePrime p)
    (h : CFSG.Open.StatedClassicalModel ↥K .PSL 2 p 1) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp.1 le_rfl hF
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact ne_two_of_fermat_or_mersenne hp
  obtain ⟨Ub, -, hUe, hcard, -, -⟩ := exists_blockU_K hs hl hZ hn hLK
  have h4 : Nat.card (Ub.map e.toMonoidHom) ≤ 4 :=
    card_le_four_psl2 hF2 (isElemAbelian_map' hUe e.toMonoidHom)
  have h5 : Nat.card (Ub.map e.toMonoidHom) = Nat.card Ub :=
    card_map_of_inf_ker_eq_bot Ub e.toMonoidHom fun x _ hx =>
      e.injective ((show e x = 1 from hx).trans (map_one e).symm)
  rw [h5, hcard] at h4
  have : 2 ^ 2 * 2 ^ 2 ≤ 2 ^ (2 * n) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega


theorem eq_two_of_twoE {X : Type} [Group X] [Finite X] (hT : Unc25G2.M2x.TwoE X) {U : Subgroup X}
    (hUe : IsElemAbelian 2 U) (hcard : Nat.card U = 2 ^ (2 * n)) (hn : 2 ≤ n) : n = 2 := by
  by_contra hne
  have h5 : 2 ^ 5 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact false_of_twoE hT hUe (by omega)

theorem concl_M22
    (hn : 2 ≤ n) (e : ↥K ≃* NativeSporadic.Carrier .M22) {Ub : Subgroup ↥K}
    (hUe : IsElemAbelian 2 Ub) (hcard : Nat.card Ub = 2 ^ (2 * n)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p K := by
  have : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv _ e.toEquiv
  have hn2 : n = 2 := eq_two_of_twoE (Unc25G2.M2x.twoE_M22.of_equiv e.symm) hUe hcard hn
  subst hn2
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_three_of_equiv e Mat.hasElemAb_nine_M22⟩

theorem concl_M23
    (hn : 2 ≤ n) (e : ↥K ≃* NativeSporadic.Carrier .M23) {Ub : Subgroup ↥K}
    (hUe : IsElemAbelian 2 Ub) (hcard : Nat.card Ub = 2 ^ (2 * n)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p K := by
  have : Finite (NativeSporadic.Carrier .M23) := Finite.of_equiv _ e.toEquiv
  have hn2 : n = 2 := eq_two_of_twoE (Unc25G2.M2x.twoE_M23.of_equiv e.symm) hUe hcard hn
  subst hn2
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_three_of_equiv e Mat.hasElemAb_nine_M23⟩

theorem concl_M22_cover
    (hn : 2 ≤ n) (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* NativeSporadic.Carrier .M22)
    {Ub : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)} (hUe : IsElemAbelian 2 Ub)
    (hcard : Nat.card Ub = 2 ^ (2 * n)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p K := by
  have : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv _ e.toEquiv
  have hn2 : n = 2 := eq_two_of_twoE (Unc25G2.M2x.twoE_M22.of_equiv e.symm) hUe hcard hn
  subst hn2
  refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_quot Nat.prime_three (by norm_num) ?_⟩
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact two_le_pRank_top_of_hasElemAb Mat.hasElemAb_nine_M22

theorem concl_L42 (hn : 2 ≤ n) (hd : 2 ^ (3 * n) ∣ Nat.card K)
    (h : CFSG.Open.StatedClassicalModel ↥K .PSL 4 2 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p K := by
  have hn2 : n = 2 := by
    rw [card_L42 h] at hd
    exact le_antisymm (le_two_of_two_pow_dvd hd (by decide)) hn
  subst hn2
  obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := h
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_three_of_equiv e (hasElemAb_nine_psl_four F)⟩

end Families

end CFSG.QuasithinUnique.Lin2.OddRank
