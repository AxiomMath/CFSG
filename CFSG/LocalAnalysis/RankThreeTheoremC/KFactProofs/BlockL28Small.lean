module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem eq_top_of_card_lt_factorial_index {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    {J : Subgroup X} (h : Nat.factorial J.index < Nat.card X) : J = ⊤ := by
  by_contra hJ
  haveI : J.normalCore.Normal := J.normalCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J.normalCore with h0 | h1
  · have := J.index_normalCore_le_factorial_index
    change _ ≤ Nat.factorial J.index at this
    rw [h0, Subgroup.index_bot] at this
    omega
  · exact hJ (top_le_iff.mp (h1 ▸ J.normalCore_le))

theorem small_l28_void (hZ : OddCenterRest) {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (hS : IsSmallTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {N : Subgroup Y}
    (hNP : N ≤ P) {d : TauCeti.ValidLieTypeIndex} (ψ : ↥N →* CatGroup d)
    (hd : IsCaseTwoIndex 3 d) (hψ : Function.Surjective ψ) : False := by
  have hcase : IsCaseTwoGroup 3 (CatGroup d) := ⟨d, hd, ⟨MulEquiv.refl _⟩⟩
  have : IsSimpleGroup (CatGroup d) := isSimpleGroup_of_isCaseTwoGroup_three hcase
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have hcard := card_of_isCaseTwoGroup_three hcase
  have hPL : P ≤ L := hCP.parab.1
  have h1 := LeviBlock.card_dvd_card_centerQuotient (hNP.trans hPL) hCP.odd
    (by rw [hcard]; norm_num) ψ hψ
  rw [hcard] at h1
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    rcases hZ Y L hCP.comp hCP.odd (Or.inr (Or.inr (Or.inr (Or.inr hS)))) with h | ⟨-, ⟨e6⟩⟩
    · exact h
    · exfalso
      have h360 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
        rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      rw [h360] at h1
      norm_num at h1
  have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  let e : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hCP.comp.2.2.2
  have hLsimple : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLcard : Nat.card ↥L = Nat.card (↥L ⧸ Subgroup.center ↥L) := Nat.card_congr e.toEquiv
  obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNT⟩ := hCP.parab
  have hTP : T ≤ P := fun x hx => hNT ⟨hTL hx, Subgroup.le_normalizer hx⟩
  have hTcard : Nat.card ↥L = Nat.card ↥T * (T.subgroupOf L).index := by
    have h1 := Subgroup.card_mul_index (T.subgroupOf L)
    have h2 : Nat.card ↥(T.subgroupOf L) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hTodd : Nat.Coprime 2 (T.subgroupOf L).index := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    omega
  have h504P : 504 ∣ Nat.card ↥P := by
    have := Subgroup.card_dvd_of_surjective hψ
    rw [hcard] at this
    exact this.trans (Subgroup.card_dvd_of_le hNP)
  have hTP' : Nat.card ↥T ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hTP
  have hPcard : Nat.card ↥(P.subgroupOf L) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hidx := Subgroup.card_mul_index (P.subgroupOf L)
  rw [hPcard] at hidx
  have hne : P.subgroupOf L ≠ ⊤ := fun h => hCP.ne_top
    (le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp h))
  refine hne (eq_top_of_card_lt_factorial_index ?_)
  rcases LeviBlock.card_small_cases hS with h | h | h | h | h
  · rw [h] at h1; norm_num at h1
  · rw [h] at h1; norm_num at h1
  ·
    have hL : Nat.card ↥L = 20160 := hLcard.trans h
    have h64 : 64 ∣ Nat.card ↥T := by
      have : 2 ^ 6 ∣ Nat.card ↥T * (T.subgroupOf L).index := hTcard ▸ (by rw [hL]; norm_num)
      exact (Nat.Coprime.pow_left 6 hTodd).dvd_of_dvd_mul_right this
    have h4032 : 4032 ∣ Nat.card ↥P := by
      have := Nat.lcm_dvd (h64.trans hTP') h504P
      have hl : Nat.lcm 64 504 = 4032 := by norm_num
      rwa [hl] at this
    obtain ⟨c, hc⟩ := h4032
    rw [hc, hL] at hidx
    have h5 : c * (P.subgroupOf L).index = 5 := by
      have : 4032 * (c * (P.subgroupOf L).index) = 4032 * 5 := by linarith
      omega
    have hle : (P.subgroupOf L).index ≤ 5 :=
      Nat.le_of_dvd (by norm_num) ⟨c, by rw [← h5]; ring⟩
    calc Nat.factorial (P.subgroupOf L).index ≤ Nat.factorial 5 := Nat.factorial_le hle
      _ < Nat.card ↥L := by rw [hL]; decide
  · rw [h] at h1; norm_num at h1
  ·
    have hL : Nat.card ↥L = 6048 := hLcard.trans h
    have h32 : 32 ∣ Nat.card ↥T := by
      have : 2 ^ 5 ∣ Nat.card ↥T * (T.subgroupOf L).index := hTcard ▸ (by rw [hL]; norm_num)
      exact (Nat.Coprime.pow_left 5 hTodd).dvd_of_dvd_mul_right this
    have h2016 : 2016 ∣ Nat.card ↥P := by
      have := Nat.lcm_dvd (h32.trans hTP') h504P
      have hl : Nat.lcm 32 504 = 2016 := by norm_num
      rwa [hl] at this
    obtain ⟨c, hc⟩ := h2016
    rw [hc, hL] at hidx
    have h3 : c * (P.subgroupOf L).index = 3 := by
      have : 2016 * (c * (P.subgroupOf L).index) = 2016 * 3 := by linarith
      omega
    have hle : (P.subgroupOf L).index ≤ 3 :=
      Nat.le_of_dvd (by norm_num) ⟨c, by rw [← h3]; ring⟩
    calc Nat.factorial (P.subgroupOf L).index ≤ Nat.factorial 3 := Nat.factorial_le hle
      _ < Nat.card ↥L := by rw [hL]; decide

theorem kFactCompParabL28RankOn_small (hZ : OddCenterRest) :
    KFactCompParabL28RankOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS N hNP _ d ψ hd hψ
  exact (small_l28_void hZ hCP hS hNP ψ hd hψ).elim

theorem kFactCompParabL28TwoRankOn_small (hZ : OddCenterRest) :
    KFactCompParabL28TwoRankOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS N hNP _ d₁ d₂ ψ hd₁ _ hψ
  refine (small_l28_void hZ hCP hS hNP ((MonoidHom.fst _ _).comp ψ) hd₁ fun a => ?_).elim
  obtain ⟨n, hn⟩ := hψ (a, 1)
  exact ⟨n, by simp [hn]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
