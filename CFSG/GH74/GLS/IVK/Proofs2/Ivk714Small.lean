module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Comp
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Generic.S1.KL5Ord

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint CFSG.GH74.GLS.IVK

private theorem ivk714s_false_of_card {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) {N : ℕ} (hK : Nat.card K = N) (hN : ¬ 2520 ∣ N) : False := by
  apply hN
  rw [← hK]
  exact h.two_five_two_zero_dvd.trans (Subgroup.card_subgroup_dvd_card _)

theorem ivk714_l28 : Ivk714Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro K _ _ _ hK _ _ h
  exact ivk714s_false_of_card h (N := 504)
    ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hK).trans (by decide)) (by decide)

theorem ivk714_l216 : Ivk714Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro K _ _ _ hK _ _ h
  exact ivk714s_false_of_card h (N := 4080)
    ((CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hK).trans (by decide)) (by decide)

theorem ivk714_u34 : Ivk714Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro K _ _ _ hK _ _ h
  have hc := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psu_three
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hK)
  exact ivk714s_false_of_card h (N := 62400) (by norm_num at hc; exact hc) (by decide)

theorem ivk714_sz8 :
    Ivk714Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro K _ _ _ hK _ _ h
  exact ivk714s_false_of_card h (N := 29120)
    ((CFSG.GH74.card_of_lieModel_twistedB2 hK).trans (by decide)) (by decide)

end CFSG.GH74.GLS.IVK.Proofs2
