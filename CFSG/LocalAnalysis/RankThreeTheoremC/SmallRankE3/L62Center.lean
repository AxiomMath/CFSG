module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {H : Type} [Group H] [Finite H]

theorem l62c_zpowers_comm {K : Subgroup H} {y : H} (hy : ∀ k ∈ K, k * y = y * k) :
    ∀ r ∈ Subgroup.zpowers y, ∀ k ∈ K, k * r = r * k := by
  intro r hr k hk
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  have hcy : Commute k y := hy k hk
  exact (Commute.zpow_right hcy j).eq

theorem l62c_normal_subgroupOf {K R : Subgroup H}
    (h : ∀ r ∈ R, ∀ k ∈ K, k * r = r * k) : (R.subgroupOf K).Normal := by
  refine ⟨fun n hn k => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (k : H) * (n : H) = (n : H) * (k : H) := h _ hn _ k.2
  have hconj : ((k * n * k⁻¹ : K) : H) = (n : H) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, mul_inv_cancel_right]
  rw [hconj]
  exact hn

theorem l62_center_isPGroup (hcore : primeComplementCore (G := H) 3 = ⊥) {C : Subgroup H}
    (hC : IsComponentOf C ⊤) : IsPGroup 3 ↥(center ↥C) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : CFSG.pPrimeCore 3 H = ⊥ := hcore
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨e, m, hm3, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hdvd : 3 ^ e ∣ orderOf g := ⟨m, hnm⟩
  have hyord : orderOf (g ^ 3 ^ e) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero e (by norm_num : (3 : ℕ) ≠ 0)) hdvd, hnm]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) e)
  have hinj : Function.Injective (C.subtype.comp (center ↥C).subtype) :=
    C.subtype_injective.comp (center ↥C).subtype_injective
  have hord : ∀ c : ↥(center ↥C),
      orderOf ((C.subtype.comp (center ↥C).subtype) c) = orderOf c :=
    fun c => orderOf_injective (C.subtype.comp (center ↥C).subtype) hinj c
  have hordy : orderOf ((C.subtype.comp (center ↥C).subtype) (g ^ 3 ^ e)) = m :=
    (hord (g ^ 3 ^ e)).trans hyord
  set y : H := (C.subtype.comp (center ↥C).subtype) (g ^ 3 ^ e) with hy_def
  have hyC : y ∈ C := ((g ^ 3 ^ e : ↥(center ↥C)) : ↥C).2
  have hycomm : ∀ k ∈ C, k * y = y * k := by
    intro k hk
    have h1 : (⟨k, hk⟩ : ↥C) * ((g ^ 3 ^ e : ↥(center ↥C)) : ↥C) =
        ((g ^ 3 ^ e : ↥(center ↥C)) : ↥C) * ⟨k, hk⟩ :=
      Subgroup.mem_center_iff.mp (g ^ 3 ^ e).2 ⟨k, hk⟩
    exact congrArg Subtype.val h1
  have hRle : Subgroup.zpowers y ≤ C := Subgroup.zpowers_le.mpr hyC
  have hRnorm : ((Subgroup.zpowers y).subgroupOf C).Normal :=
    l62c_normal_subgroupOf (l62c_zpowers_comm hycomm)
  have hsubRH : CFSG.Open.IsSubnormal (Subgroup.zpowers y) ⊤ :=
    CFSG.Open.IsSubnormal.step hRle hRnorm hC.2.1
  have hsubR : (Subgroup.zpowers y).IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hsubRH
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hordy]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  have hle : Subgroup.zpowers y ≤ CFSG.pPrimeCore 3 H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ths_le_pPrimeCore_of_isSubnormal hsubR hcop
  rw [hc] at hle
  have hy1 : y = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers y))
  have hm1 : m = 1 := by
    rw [← hordy, hy1, orderOf_one]
  exact ⟨e, by rw [hnm, hm1, mul_one]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
