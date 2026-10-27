module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BCw
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BS4

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {E E0 Y Y' V V' F F' P H : Subgroup G}

namespace Sec8T84G3BSide

theorem cent_U (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F'))
    {a b : G} (ha : a ∈ Y) (hb : b ∈ Y') (hy : a * b ∈ sec8t84g_Q E E0) {k : ℕ}
    (hyk : (a * b) ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E E0)) :
    (a ∈ oddCoreIn (normalizer (E : Set G)) →
      (V ⊔ F) ⊓ centralizer ({a * b} : Set G) = V ⊔ F) ∧
    (a ∉ oddCoreIn (normalizer (E : Set G)) →
      (V ⊔ F) ⊓ centralizer ({a * b} : Set G) = ⊥) := by
  have hkey : ∀ u ∈ V ⊔ F, ((a * b) * u * (a * b)⁻¹ = u ↔
      a * u * a⁻¹ * u⁻¹ ∈ oddCoreIn (normalizer (E : Set G))) := by
    intro u hu
    obtain ⟨n, hn, hne⟩ := S.conj_eq ha hb (S.U_le_Y hu)
    constructor
    · intro h
      have h1 : n * (a * u * a⁻¹ * u⁻¹) = 1 := by
        calc n * (a * u * a⁻¹ * u⁻¹) = (n * (a * u * a⁻¹)) * u⁻¹ := by group
          _ = ((a * b) * u * (a * b)⁻¹) * u⁻¹ := by rw [hne]
          _ = 1 := by rw [h, mul_inv_cancel]
      have h2 : a * u * a⁻¹ * u⁻¹ = n⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact (oddCoreIn (normalizer (E : Set G))).inv_mem hn
    · intro h
      have hc : ((a * b) * u * (a * b)⁻¹) * u⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
        have h1 : ((a * b) * u * (a * b)⁻¹) * u⁻¹ = n * (a * u * a⁻¹ * u⁻¹) := by
          rw [hne]; group
        rw [h1]
        exact (oddCoreIn (normalizer (E : Set G))).mul_mem hn h
      have hcU : ((a * b) * u * (a * b)⁻¹) * u⁻¹ ∈ E ⊔ E0 :=
        (E ⊔ E0).mul_mem (S.U_le_W (S.conj_U hW ha hb hy u hu))
          ((E ⊔ E0).inv_mem (S.U_le_W hu))
      have h2 : ((a * b) * u * (a * b)⁻¹) * u⁻¹ ∈
          (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨hcU, hc⟩
      rw [S.W_inf, Subgroup.mem_bot] at h2
      exact mul_inv_eq_one.mp h2
  refine ⟨fun haN => ?_, fun haN => ?_⟩
  · refine inf_eq_left.mpr (fun u hu => Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_))
    rw [Set.mem_singleton_iff.mp hz]
    have h1 : a * u * a⁻¹ * u⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
      have h2 : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
      rw [h2]
      exact (oddCoreIn (normalizer (E : Set G))).mul_mem haN
        (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (S.Y_le (S.U_le_Y hu))
          ((oddCoreIn (normalizer (E : Set G))).inv_mem haN))
    exact mul_inv_eq_iff_eq_mul.mp ((hkey u hu).mpr h1)
  · haveI hNn : ((oddCoreIn (normalizer (E : Set G))).subgroupOf Y).Normal := S.ydata.O_norm
    let π : ↥Y →* ↥Y ⧸ (oddCoreIn (normalizer (E : Set G))).subgroupOf Y := QuotientGroup.mk' _
    have hker : ∀ x : ↥Y, π x = 1 ↔ (x : G) ∈ oddCoreIn (normalizer (E : Set G)) :=
      fun x => QuotientGroup.eq_one_iff x
    have hS4c := sec8t84g3b_S4_ydata hP hS4 S.ydata S.P_syl S.F_le_P S.F_e16 S.F_ne
    have aux : ∀ p q : G, p * q⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) →
        p ∈ oddCoreIn (normalizer (E : Set G)) → q ∈ oddCoreIn (normalizer (E : Set G)) := by
      intro p q h1 hp
      have h3 := (oddCoreIn (normalizer (E : Set G))).mul_mem
        ((oddCoreIn (normalizer (E : Set G))).inv_mem h1) hp
      have h4 : (p * q⁻¹)⁻¹ * p = q := by group
      rwa [h4] at h3
    have hpow : a ^ (3 ^ k) ∈ oddCoreIn (normalizer (E : Set G)) := by
      have hyN : (a * b) ^ (3 ^ k) ∈ oddCoreIn (normalizer (E : Set G)) := by
        have h1 := hyk
        rw [S.O_eq] at h1
        exact h1.2
      have h1 := sec8t84g3b_pow_mod (X := normalizer (E : Set G))
        (fun x hx n hn => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hx hn)
        (S.Y_le ha) (S.Y'_le hb) (S.comm a ha b hb) (3 ^ k)
      have h2 : a ^ (3 ^ k) * b ^ (3 ^ k) ∈ oddCoreIn (normalizer (E : Set G)) :=
        aux _ _ h1 hyN
      have h5 : a ^ (3 ^ k) ∈ Y' := by
        have h6 := Y'.mul_mem (S.N_le' h2) (Y'.inv_mem (Y'.pow_mem hb (3 ^ k)))
        rwa [mul_inv_cancel_right] at h6
      exact S.inf ⟨Y.pow_mem ha _, h5⟩
    have hā1 : π ⟨a, ha⟩ ^ (3 ^ k) = 1 := by
      rw [← map_pow, hker, Subgroup.coe_pow]
      exact hpow
    have hnorm : π ⟨a, ha⟩ ∈ normalizer ((((V.subgroupOf Y).map π ⊔ (F.subgroupOf Y).map π :
        Subgroup _)) : Set _) := by
      refine sec8t84g3b_mem_normalizer_of_conj (fun x hx => ?_)
      rw [← Subgroup.map_sup] at hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← Subgroup.subgroupOf_sup S.ydata.V_le S.F_le_Y] at hw
      have hwU : (w : G) ∈ V ⊔ F := hw
      obtain ⟨n, hn, hne⟩ := S.conj_eq ha hb w.2
      have hyU : (a * b) * (w : G) * (a * b)⁻¹ ∈ V ⊔ F := S.conj_U hW ha hb hy w hwU
      have hY1 : a * (w : G) * a⁻¹ = n⁻¹ * ((a * b) * (w : G) * (a * b)⁻¹) := by
        rw [hne]; group
      have hY2 : π ⟨a, ha⟩ * π w * (π ⟨a, ha⟩)⁻¹ =
          π ⟨(a * b) * (w : G) * (a * b)⁻¹, S.U_le_Y hyU⟩ := by
        have h1 : (⟨a, ha⟩ * w * ⟨a, ha⟩⁻¹ : ↥Y) = ⟨n⁻¹, Y.inv_mem (S.N_le hn)⟩ *
            ⟨(a * b) * (w : G) * (a * b)⁻¹, S.U_le_Y hyU⟩ := Subtype.ext hY1
        have h2 : π (⟨n⁻¹, Y.inv_mem (S.N_le hn)⟩ : ↥Y) = 1 :=
          (hker _).mpr ((oddCoreIn (normalizer (E : Set G))).inv_mem hn)
        rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul, h2, one_mul]
      rw [hY2, ← Subgroup.map_sup]
      refine Subgroup.mem_map_of_mem π ?_
      rw [← Subgroup.subgroupOf_sup S.ydata.V_le S.F_le_Y]
      exact hyU
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hā1)
    have hM : π ⟨a, ha⟩ ∈ sec8t84g3b_M ((V.subgroupOf Y).map π) ((F.subgroupOf Y).map π) := by
      unfold sec8t84g3b_M twoRes
      exact Subgroup.subset_closure ⟨hnorm, Odd.of_dvd_nat (Odd.pow (by decide : Odd 3))
        (orderOf_dvd_of_pow_eq_one hā1)⟩
    have hne1 : π ⟨a, ha⟩ ≠ 1 := fun h => haN ((hker _).mp h)
    have hS42 := (hS4c.2.1 _ hM ⟨j, hj⟩ hne1).2
    refine eq_bot_iff.mpr (fun u hu => ?_)
    obtain ⟨huU, huc⟩ := hu
    have hcomm : (a * b) * u = u * (a * b) := Subgroup.mem_centralizer_iff.mp huc (a * b) rfl
    have h1 : (a * b) * u * (a * b)⁻¹ = u := by rw [hcomm, mul_inv_cancel_right]
    have h2 := (hkey u huU).mp h1
    have h3 : π ⟨a, ha⟩ * π ⟨u, S.U_le_Y huU⟩ = π ⟨u, S.U_le_Y huU⟩ * π ⟨a, ha⟩ := by
      have h4 : π (⟨a, ha⟩ * ⟨u, S.U_le_Y huU⟩ * ⟨a, ha⟩⁻¹ * ⟨u, S.U_le_Y huU⟩⁻¹) = 1 :=
        (hker _).mpr h2
      simp only [map_mul, map_inv] at h4
      have h5 : π ⟨a, ha⟩ * π ⟨u, S.U_le_Y huU⟩ * (π ⟨a, ha⟩)⁻¹ = π ⟨u, S.U_le_Y huU⟩ :=
        mul_inv_eq_one.mp h4
      calc π ⟨a, ha⟩ * π ⟨u, S.U_le_Y huU⟩
          = (π ⟨a, ha⟩ * π ⟨u, S.U_le_Y huU⟩ * (π ⟨a, ha⟩)⁻¹) * π ⟨a, ha⟩ := by group
        _ = π ⟨u, S.U_le_Y huU⟩ * π ⟨a, ha⟩ := by rw [h5]
    have huJ : π ⟨u, S.U_le_Y huU⟩ ∈
        (V.subgroupOf Y).map π ⊔ (F.subgroupOf Y).map π := by
      rw [← Subgroup.map_sup]
      refine Subgroup.mem_map_of_mem π ?_
      rw [← Subgroup.subgroupOf_sup S.ydata.V_le S.F_le_Y]
      exact huU
    have h6 := hS42 _ huJ h3
    have h7 : u ∈ oddCoreIn (normalizer (E : Set G)) := (hker ⟨u, S.U_le_Y huU⟩).mp h6
    have h8 : u ∈ (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨S.U_le_W huU, h7⟩
    rw [S.W_inf, Subgroup.mem_bot] at h8
    exact Subgroup.mem_bot.mpr h8

theorem conj_U_of_odd (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H)
    (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F')) {y : G} (hy : y ∈ sec8t84g_Q E E0)
    (hodd : Odd (orderOf y)) : ∀ u ∈ V ⊔ F, y * u * y⁻¹ ∈ V ⊔ F := by
  obtain ⟨a, ha, b, hb, rfl⟩ := S.odd_mem y (sec8t84g3b_Q_le_E hy) hodd
  exact S.conj_U hW ha hb hy

theorem cent_U_dich (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) (hW : E ⊔ E0 = (V ⊔ F) ⊔ (V' ⊔ F'))
    {y : G} (hy : y ∈ sec8t84g_Q E E0) {k : ℕ}
    (hyk : y ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E E0)) :
    (V ⊔ F) ⊓ centralizer ({y} : Set G) = ⊥ ∨ (V ⊔ F) ⊓ centralizer ({y} : Set G) = V ⊔ F := by
  have hodd : Odd (orderOf y) := sec8t84g3b_odd_of_pow (Odd.pow (by decide : Odd 3)) hyk
  obtain ⟨a, ha, b, hb, rfl⟩ := S.odd_mem y (sec8t84g3b_Q_le_E hy) hodd
  by_cases hN : a ∈ oddCoreIn (normalizer (E : Set G))
  · exact Or.inr ((S.cent_U hP hS4 hW ha hb hy hyk).1 hN)
  · exact Or.inl ((S.cent_U hP hS4 hW ha hb hy hyk).2 hN)

end Sec8T84G3BSide

end CFSG.OddStandard.SmallF3.Omega
