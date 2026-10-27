module

public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Count
public import CFSG.CGT.PushingUpLit.CGT6X.End3L2Sec
public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_commV_of_section {S M : Type} [Group S] [Group M] {act : S → M → M}
    {Y : Subgroup (MulAut V)} {Z : Subgroup V} (hsec : IsNatSectionBy act Y (commV Y) Z) :
    Nat.card ↥(Z.subgroupOf (commV Y)) * Nat.card M = Nat.card ↥(commV Y) := by
  obtain ⟨-, θ, β, hβs, hβk, -⟩ := hsec
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rwa [hβk] at h1

theorem profile (hM2 : H1NaturalSL2) (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y)
    (hcls : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    (InClassX ↥(yuHol Y) ∧ ∃ Cc : ℕ, Nat.card ↥(commV Y) = Cc * 2 ^ (2 * f) ∧ Cc ≤ 2 ^ f ∧
        (∀ c ∈ Y, Odd (orderOf c) → 1 < orderOf c → 2 ^ (2 * f) ≤ Nat.card ↥(commSub c)) ∧
        (∀ c ∈ Y, Odd (orderOf c) → Nat.card ↥(commSub c) ≤ 2 ^ (2 * f))) ∨
    (Nat.card ↥(commV Y) = 2 ^ (2 * f) ∧
        (∀ c ∈ Y, Odd (orderOf c) → Nat.card ↥(commSub c) ≤ 2 ^ (2 * f))) := by
  classical
  have hcg : CommGen Y := commGen_of_perfect hperf
  have hleC : ∀ c ∈ Y, commSub c ≤ commV Y := fun c hc => by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨c, hc, v, rfl⟩
  rcases hcls with hX | ⟨n, hn, hΩ⟩
  · have hsq : SimpleQuot Y := simpleQuot_of_inClassX hV hperf hX
    rcases natSection_of_classX hV hperf hX hf hY with hnat | ⟨hf2, halt⟩
    · left
      refine ⟨hX, Nat.card ↥(commV Y ⊓ fixV Y), card_commV_of_natSection (by omega) hnat,
        card_fix_le_of_sl hM2 hV hcg hsq hf hnat, ?_, ?_⟩
      · intro c hc hodd hgt
        have := card_commSub_inf_ge_of_sl (by omega) hnat hc hodd hgt
        rwa [inf_eq_left.mpr (hleC c hc)] at this
      · intro c hc hodd
        have := card_commSub_le_of_section hV le_rfl hnat hc hodd
        rwa [card_sl_model (by omega)] at this
    · right
      subst hf2
      have hC := fix_eq_bot_of_alt hV hcg hsq halt
      have h16 : Nat.card ↥(G6.coreMod 5) = 16 := by
        rw [X1512.card_coreMod (Or.inr rfl)]
        norm_num
      have hU := card_commV_of_section halt
      rw [hC, Subgroup.bot_subgroupOf, Subgroup.card_bot, h16] at hU
      refine ⟨by rw [← hU]; norm_num, fun c hc hodd => ?_⟩
      have := card_commSub_le_of_section hV le_rfl halt hc hodd
      rw [h16] at this
      norm_num
      exact this
  · right
    have hf2 : f = 2 * n := not_natOmegaMinus_of_ysl (by omega) (by omega) hY hΩ
    subst hf2
    have hM : Nat.card (Multiplicative (hermSub n)) = 2 ^ (4 * n) :=
      card_multiplicative_hermSub (by omega)
    have hU := card_commV_of_section hΩ
    rw [Subgroup.bot_subgroupOf, Subgroup.card_bot, hM] at hU
    have h4 : 2 * (2 * n) = 4 * n := by ring
    refine ⟨by rw [← hU, h4]; ring, fun c hc hodd => ?_⟩
    have := card_commSub_le_of_section hV bot_le hΩ hc hodd
    rw [hM] at this
    rw [h4]
    exact this

end CFSG.CGT.PushingUpLit.CGT6X.End3
