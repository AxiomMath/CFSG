module

public import CFSG.LocalAnalysis.OddStandard.ONan76Main
public import CFSG.Goldschmidt.OddCore

public section

namespace CFSG.OddStandard.ONan76

open Subgroup

theorem false_of_alperinFrame_of_gold (hgold : CFSG.Goldschmidt.CoreStatement) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (P : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    {v₁ v₂ v₃ s t : G} (hF : AlperinFrame n v₁ v₂ v₃ s t)
    (hP : Subgroup.closure ({v₁, v₂, v₃, s, t} : Set G) = P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  set W := hF.W hn1 with hWdef
  have hWset : (W : Set G) = {w | w ∈ Subgroup.closure ({v₁, v₂, v₃} : Set G) ∧ w * w = 1} := by
    ext w
    exact hF.mem_W_iff hn1
  have hcl : CFSG.Open.fusionStronglyClosed (W : Set G) (P : Subgroup G) := by
    rw [hWset]
    exact stronglyClosed_of_alperinFrame P hn hF hP
  have hle : W ≤ (P : Subgroup G) := fun w hw => hP ▸ hF.V_le_P (hF.W_le_V hn1 hw)
  have hab : IsMulCommutative W := ⟨⟨fun a b => Subtype.ext
    (hF.V_comm hn1 (hF.W_le_V hn1 a.2) (hF.W_le_V hn1 b.2))⟩⟩
  set z := vec v₁ v₂ v₃ (((2 : ZMod (2 ^ n)) ^ (n - 1), 0, 0) : Vec n) with hz
  have hzW : z ∈ W := (hF.vec_mem_W_iff hn1).2 (by
    simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, and_true]
    exact two_pow_pred_add_self hn1)
  have hz1 : z ≠ 1 := fun h =>
    two_pow_pred_ne_zero hn1 (congrArg Prod.fst ((hF.vec_eq_one_iff hn1).1 h))
  have hW1 : W ≠ ⊥ := fun h => hz1 (by rw [h] at hzW; exact mem_bot.1 hzW)
  have hnc : normalClosure (W : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (W : Set G)) with h | h
    · exact absurd (eq_bot_iff.2 (h ▸ le_normalClosure)) hW1
    · exact h
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact ((hF.mem_W_iff hn1).1 hzW).2) hz1
  have heven : Even (Nat.card G) := even_iff_two_dvd.2 (hz2 ▸ orderOf_dvd_natCard z)
  have hna : ∃ a b : G, a * b ≠ b * a := by
    refine ⟨s, t, fun h => ?_⟩
    have hs : s * s ∈ hF.V := by
      have e : t⁻¹ * s * t = s := by rw [mul_assoc, h, inv_mul_cancel_left]
      rw [hF.t_s] at e
      rw [show s * s = s * s⁻¹ by rw [e], mul_inv_cancel]
      exact one_mem _
    have := (hF.nf_mem_V_iff hn2 0 (i := 2) (e := 0) (by norm_num) (by norm_num)).1
      (by rw [hF.vec_zero, one_mul, pow_zero, mul_one, pow_two]; exact hs)
    omega
  have hO : CFSG.Open.goldschmidtOddCore G = ⊥ := by
    rw [CFSG.Open.goldschmidtOddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · rw [h, Subgroup.card_top] at hodd
      exact absurd heven (Nat.not_even_iff_odd.mpr hodd)
  have hO2 : CFSG.Open.pCore 2 G = ⊥ := by
    rw [CFSG.pCore_eq_iSup, eq_bot_iff]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h.le
    · exfalso
      subst h
      have hX : IsPGroup 2 G := hp.of_equiv Subgroup.topEquiv
      obtain ⟨a, b, hab⟩ := hna
      have : Nontrivial G := ⟨⟨a * b, b * a, hab⟩⟩
      have hc := hX.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · rw [h] at hc
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hc rfl
      · exact hab ((Subgroup.mem_center_iff.1 (h ▸ mem_top b)) a)
  obtain ⟨h1, h2, -⟩ := hgold G P W hle hab hcl hnc hO
  rw [hO2, bot_sup_eq] at h1 h2
  rw [h1] at h2
  have ht : t ∈ W := by
    rw [h2]
    refine subset_closure ⟨mem_inf.2 ⟨hP ▸ hF.t_mem_P, mem_top t⟩, ?_⟩
    rw [pow_two]
    exact hF.t_sq
  have htV : t ∈ hF.V := hF.W_le_V hn1 ht
  have := (hF.nf_mem_V_iff hn2 0 (i := 0) (e := 1) (by norm_num) (by norm_num)).1
    (by rw [hF.vec_zero, one_mul, pow_zero, one_mul, pow_one]; exact htV)
  omega

end CFSG.OddStandard.ONan76
