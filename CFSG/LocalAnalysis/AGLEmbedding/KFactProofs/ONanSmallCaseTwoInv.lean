module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallSylow

public section

namespace CFSG.AGLEmbedding

open CFSG.Open KFactProofs.SmallIdent

theorem isSmallStrongP_of_rank (h : KFactSmallIdent) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hc : IsCatalogGroup K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow p K) (hT : ¬ IsCyclic (T : Subgroup K))
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) (hrk : Open.pRank p (⊤ : Subgroup K) ≤ 2) :
    IsSmallStrongP p K :=
  h K hs hnab hc p hp hp2 T hT hΓ
    ((CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp ⊤).le.trans hrk)

theorem not_dvd_forty_one_of_isSmallStrongP
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K) (hK : IsSmallStrongP 5 K) :
    ¬ 41 ∣ Nat.card K := by
  rcases hK with hL | hU | hA | ⟨h3, -⟩ | ⟨-, hT | hMcL | hFi⟩ | ⟨h11, -⟩
  · rw [card_of_isSmallLinTwo (by norm_num) (by norm_num) hL]
    norm_num
  · have h := card_mul_gcd_of_isSmallUnitary hU
    norm_num at h
    omega
  · rw [card_of_isAltTwoP (by norm_num) hA]
    norm_num [Nat.factorial]
  · omega
  · rw [card_of_isTitsGroup hT]
    norm_num
  · rw [card_of_isMcL hs hMcL]
    norm_num
  · rw [card_of_isFi22 hs hFi]
    norm_num
  · omega

theorem forty_one_dvd_card_of_isCaseTwoGroup_five
    {L : Type} [Group L] (hL : IsCaseTwoGroup 5 L) :
    41 ∣ Nat.card L := by
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hL
  rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
  · omega
  · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
    have hcard := (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie (S := L)
      ⟨hv, ⟨e⟩⟩).card
    rw [hcard]
    norm_num

theorem exists_orderOf_nine_of_isCaseTwoGroup_three {L : Type} [Group L]
    (hL : IsCaseTwoGroup 3 L) : ∃ g : L, orderOf g = 9 := by
  obtain ⟨e⟩ := KFactProofs.L28Local.nonempty_equiv_G8 hL
  exact ⟨e.symm CFSG.Quasithin.F6.L28Res.g9, by
    rw [MulEquiv.orderOf_eq]
    exact KFactProofs.L28Local.orderOf_g9⟩

theorem false_of_surjective_orderOf_sq {K L : Type} [Group K] [Finite K] [Group L] {p : ℕ}
    (hp : p.Prime) (hexp : ∀ t : K, (∃ n : ℕ, t ^ p ^ n = 1) → t ^ p = 1) (A : Subgroup K)
    (f : A →* L) (hf : Function.Surjective f) (g : L) (hg : orderOf g = p ^ 2) : False := by
  obtain ⟨a, rfl⟩ := hf g
  have hdvd : p ^ 2 ∣ orderOf a := hg ▸ orderOf_map_dvd f a
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < orderOf a := orderOf_pos a
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hord : orderOf (a ^ m) = p ^ 2 := by
    rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hm.symm), hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hordK : orderOf ((a ^ m : A) : K) = p ^ 2 := by
    rw [Subgroup.orderOf_coe, hord]
  have h1 : ((a ^ m : A) : K) ^ p = 1 := by
    apply hexp
    exact ⟨2, by rw [← hordK]; exact pow_orderOf_eq_one _⟩
  have h2 : orderOf ((a ^ m : A) : K) ∣ p := orderOf_dvd_of_pow_eq_one h1
  rw [hordK] at h2
  have h3 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos h2
  nlinarith [hp.two_le]

theorem kFactCaseTwoInv_of_smallIdent
    (h : KFactSmallIdent) : KFactCaseTwoInv := by
  intro K _ _ hs hnab hc p hp35 T hT hΓ hrk A L _ hL f hf
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hK : IsSmallStrongP p K := isSmallStrongP_of_rank h hs hnab hc hp hp2 T hT hΓ hrk
  rcases hp35 with rfl | rfl
  · obtain ⟨g, hg⟩ := exists_orderOf_nine_of_isCaseTwoGroup_three hL
    exact false_of_surjective_orderOf_sq hp (pow_eq_one_of_isSmallStrongP hp hp2 hs hK T hT) A f hf
      g (by simpa using hg)
  · have h1 : Nat.card L ∣ Nat.card A := Subgroup.card_dvd_of_surjective (f := f) hf
    have h2 : Nat.card A ∣ Nat.card K := Subgroup.card_subgroup_dvd_card A
    exact not_dvd_forty_one_of_isSmallStrongP hs hK
      ((forty_one_dvd_card_of_isCaseTwoGroup_five hL).trans (h1.trans h2))

end CFSG.AGLEmbedding
