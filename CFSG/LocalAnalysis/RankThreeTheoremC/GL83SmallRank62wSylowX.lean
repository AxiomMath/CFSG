module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wConjTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wPlaneRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr630e_exists_rank_three_of_sylow {p : ℕ} [Fact p.Prime] (P R : Sylow p G)
    (hA : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3) :
    ∃ A : Subgroup G, A ≤ (R : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
  obtain ⟨A, hAP, hAe, hAc⟩ := hA
  have hPs : IsSylowOf p (P : Subgroup G) ⊤ := isSylowOf_iff.mpr
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hRs : IsSylowOf p (R : Subgroup G) ⊤ := isSylowOf_iff.mpr
    ⟨le_top, R.isPGroup', by rw [Subgroup.relIndex_top_right]; exact R.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := hPs.exists_mem_conj hRs
  refine ⟨A.map (MulAut.conj g).toMonoidHom, ?_, sr630e_isElemAbelian_map hAe _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hg]
    simpa [MulAut.conj_apply, mul_assoc] using hAP ha
  · rw [Subgroup.card_map_of_injective (fun a b h => (MulAut.conj g).injective h), hAc]

theorem sr630e_zpowers_isSylowOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Sylow p G}
    {x z : G} (hpl : SmallRankPlane p (P : Subgroup G) x z)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hPx : IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)))
    (hCx : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 2)
    (hA3 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3)
    {C : Subgroup G} (hxC : x ∈ C) (hzC : z ∉ C) (hzN : z ∈ normalizer (C : Set G)) :
    IsSylowOf p (zpowers x) C := by
  have : Fact p.Prime := ⟨hp⟩
  have hBe : IsElemAbelian p (zpowers x ⊔ zpowers z) := hpl.isElemAbelian
  have hBc : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2 := hpl.card_eq
  have hBp : IsPGroup p ↥(zpowers x ⊔ zpowers z) := IsPGroup.of_card hBc
  have hxB : x ∈ zpowers x ⊔ zpowers z := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hBC : (zpowers x ⊔ zpowers z) ⊓ C = zpowers x :=
    sr630e_inf_eq_zpowers hp hBc hxB hxC hx1 hxp hzB hzC
  have hHN : C ⊔ zpowers z ≤ normalizer (C : Set G) := sup_le le_normalizer (zpowers_le.mpr hzN)
  have hBH : zpowers x ⊔ zpowers z ≤ C ⊔ zpowers z :=
    sup_le (zpowers_le.mpr (mem_sup_left hxC)) le_sup_right
  obtain ⟨W, hW, hBW⟩ := sr630e_exists_isSylowOf_le hBH hBp
  have hWp : IsPGroup p W := hW.isPGroup
  have hQ : IsSylowOf p (W ⊓ C) C := hW.inf_of_le_normalizer le_sup_left hHN
  have hxQ : x ∈ W ⊓ C := ⟨hBW hxB, hxC⟩
  have hWNQ : W ≤ normalizer ((W ⊓ C : Subgroup G) : Set G) := fun w hw =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hw, hHN (hW.le hw)⟩
  have hQne : W ⊓ C ≠ ⊥ := by
    intro h
    have hx : x ∈ (⊥ : Subgroup G) := h ▸ hxQ
    exact hx1 (Subgroup.mem_bot.mp hx)
  obtain ⟨a, haQ, ha1, hacomm⟩ := sr630a_exists_central hWp inf_le_left hWNQ hQne
  have hdvd : p ∣ Nat.card (zpowers a) := by
    obtain ⟨k, hk⟩ := (hWp.to_le (zpowers_le.mpr haQ.1)).exists_card_eq
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      apply ha1
      have h1 : zpowers a = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk, h0, pow_zero])
      have ha : a ∈ zpowers a := mem_zpowers a
      rw [h1] at ha
      exact Subgroup.mem_bot.mp ha
    · rw [hk]
      exact dvd_pow_self p hpos.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcp : orderOf (c : G) = p := by rw [Subgroup.orderOf_coe]; exact hc
  have hc1 : (c : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hcp
    exact hp.one_lt.ne hcp
  have hcpow : (c : G) ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp c.2
  have hcW : ∀ w ∈ W, w * (c : G) = (c : G) * w := by
    intro w hw
    rw [← hj]
    exact (Commute.zpow_right (hacomm w hw) j).eq
  have hcQ : (c : G) ∈ W ⊓ C := by rw [← hj]; exact zpow_mem haQ j
  have hcB : (c : G) ∈ zpowers x ⊔ zpowers z := hpl.mem_of_mem_centralizer _
    (mem_centralizer_iff.mpr fun b hb => hcW b (hBW hb)) hcpow
  have hcx : (c : G) ∈ zpowers x := by rw [← hBC]; exact ⟨hcB, hcQ.2⟩
  have hxc : x ∈ zpowers (c : G) := sr630e_mem_zpowers_of_mem hp hx1 hxp hcx hc1
  have hxW : ∀ w ∈ W, w * x = x * w := by
    intro w hw
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hxc
    rw [← hi]
    exact (Commute.zpow_right (hcW w hw) i).eq
  have hWCx : W ≤ centralizer ({x} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hxW w hw)
  have hPB : ∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ p = 1 →
      y ∈ zpowers x ⊔ zpowers z := by
    intro y hy hyp
    refine hpl.mem_of_mem_centralizer y (mem_centralizer_iff.mpr fun b hb => ?_) hyp
    have hBy : zpowers x ⊔ zpowers z ≤ centralizer ({y} : Set G) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hy.2).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc y hy.1).symm
    exact mem_centralizer_singleton_iff.mp (hBy hb)
  obtain ⟨S', hS', hWS'⟩ := sr630e_exists_isSylowOf_le hWCx hWp
  obtain ⟨k, -, hk⟩ := hPx.exists_mem_conj hS'
  have hconj : ∀ w ∈ W, w ^ p = 1 → k⁻¹ * w * k ∈ zpowers x ⊔ zpowers z := fun w hw hwp =>
    hPB _ ((hk w).mp (hWS' hw)) (by rw [sr630e_inv_conj_pow, hwp, mul_one, inv_mul_cancel])
  have hBk : (zpowers x ⊔ zpowers z).map (MulAut.conj k⁻¹).toMonoidHom =
      zpowers x ⊔ zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have h := hconj b (hBW hb) (hBe.2 b hb)
      simpa [MulAut.conj_apply] using h
    · exact (Subgroup.card_map_of_injective
        (fun a b h => (MulAut.conj k⁻¹).injective h)).ge
  have hWB : ∀ w ∈ W, w ^ p = 1 → w ∈ zpowers x ⊔ zpowers z := by
    intro w hw hwp
    have h1 := hconj w hw hwp
    rw [← hBk] at h1
    obtain ⟨b, hb, hbw⟩ := h1
    have hbw' : k⁻¹ * b * k = k⁻¹ * w * k := by simpa [MulAut.conj_apply] using hbw
    have hbw'' : b = w := mul_left_cancel (mul_right_cancel hbw')
    exact hbw'' ▸ hb
  obtain ⟨R, hWR⟩ := hWp.exists_le_sylow
  have hAR := sr630e_exists_rank_three_of_sylow P R hA3
  have key : ∀ n, ∀ q ∈ W ⊓ C, orderOf q = n → q ∈ zpowers x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hq hqn
      by_contra hqx
      have hq1 : q ≠ 1 := fun h => hqx (h ▸ one_mem _)
      obtain ⟨m, hm⟩ := hWp ⟨q, hq.1⟩
      have hqm : q ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
      obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hqm)
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hio
        exact hq1 (orderOf_eq_one_iff.mp hio)
      have hpdvd : p ∣ orderOf q := by rw [hio]; exact dvd_pow_self p hi0
      have hlt : orderOf (q ^ p) < n := by
        rw [orderOf_pow_of_dvd hp.ne_zero hpdvd, ← hqn]
        exact Nat.div_lt_self (orderOf_pos q) hp.one_lt
      have hqp : q ^ p ∈ zpowers x := ih _ hlt (q ^ p) (pow_mem hq p) rfl
      have hqp1 : q ^ p ≠ 1 := by
        intro h
        apply hqx
        rw [← hBC]
        exact ⟨hWB q hq.1 h, hq.2⟩
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (sr630e_mem_zpowers_of_mem hp hx1 hxp hqp hqp1)
      have hroot : (q ^ j) ^ p = x := by
        rw [← hj]
        calc (q ^ j) ^ p = (q ^ j) ^ (p : ℤ) := (zpow_natCast _ _).symm
          _ = q ^ (j * p) := (zpow_mul q j p).symm
          _ = q ^ ((p : ℤ) * j) := by rw [mul_comm]
          _ = (q ^ (p : ℤ)) ^ j := zpow_mul q p j
          _ = (q ^ p) ^ j := by rw [zpow_natCast]
      exact sr630b_not_pow_of_rank hp hp2 R.isPGroup' hxp (hWR (W.zpow_mem hq.1 j)) hroot hAR hCx
  have hQx : W ⊓ C = zpowers x :=
    le_antisymm (fun q hq => key _ q hq rfl) (zpowers_le.mpr hxQ)
  rw [← hQx]
  exact hQ

end CFSG.LocalAnalysis.RankThreeTheoremC
