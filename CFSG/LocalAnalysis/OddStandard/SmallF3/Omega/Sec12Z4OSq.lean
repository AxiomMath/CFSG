module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem z4o_exists_sq [Finite G] {V B D : Subgroup G} (hV : IsZ4Pow4 V) (hBV : B ≤ V)
    (hB16 : Nat.card B = 2 ^ 4) (hB2 : ∀ b ∈ B, b * b = 1) (hDV : D ≤ V) :
    ∃ D2 : Subgroup G, D2 ≤ B ∧ (∀ x, x ∈ D2 ↔ ∃ v ∈ D, v * v = x) ∧
      Nat.card D = Nat.card ↥(D ⊓ B) * Nat.card D2 := by
  have hc := sec124_z4_comm hV
  let f : ↥D →* G := MonoidHom.mk' (fun v => (v : G) * v) (by
    intro a b
    have hab : (a : G) * b = b * a := hc a (hDV a.2) b (hDV b.2)
    show (a : G) * b * ((a : G) * b) = (a : G) * a * ((b : G) * b)
    calc (a : G) * b * ((a : G) * b) = a * ((b : G) * a) * b := by group
      _ = a * ((a : G) * b) * b := by rw [hab]
      _ = (a : G) * a * ((b : G) * b) := by group)
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact sec124_z4_sq_mem hV hBV hB16 hB2 v (hDV v.2)
  · intro x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, v.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  · have hker : f.ker = (D ⊓ B).subgroupOf D := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      change (v : G) * v = 1 ↔ _
      constructor
      · intro h
        exact ⟨v.2, sec124_z4_mem_of_sq hV hBV hB16 hB2 v (hDV v.2) h⟩
      · intro h
        exact hB2 v h.2
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    exact h.symm

theorem z4o_card_inf_le [Finite G] {B C D : Subgroup G} (hB16 : Nat.card B = 2 ^ 4)
    (hBC : ¬ B ≤ C) (hDC : D ≤ C) : Nat.card ↥(D ⊓ B) ≤ 2 ^ 3 := by
  have hdvd : Nat.card ↥(D ⊓ B) ∣ 2 ^ 4 := hB16 ▸ Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hmeq]
  by_cases h4 : m = 4
  · exfalso
    apply hBC
    have heq : D ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hmeq, h4, hB16])
    exact heq ▸ inf_le_left.trans hDC
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem z4o_card_sup_zpowers [Finite G] {H : Subgroup G} {x : G} (hx : orderOf x = 2)
    (hxH : x ∉ H) (hc : ∀ h ∈ H, h * x = x * h) :
    Nat.card ↥(H ⊔ zpowers x) = Nat.card H * 2 := by
  have hcomm : ∀ a ∈ H, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a x from hc a ha) i).eq
  have hbot : H ⊓ zpowers x = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro y ⟨hyH, hyx⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · rw [← zpow_mod_orderOf, hx]
      simp [h]
    · exfalso
      apply hxH
      have : x ^ i = x := by
        rw [← zpow_mod_orderOf, hx]
        simp [h]
      rwa [this] at hyH
  rw [sec124_card_sup hcomm hbot, Nat.card_zpowers, hx]

end CFSG.OddStandard.SmallF3.Omega
