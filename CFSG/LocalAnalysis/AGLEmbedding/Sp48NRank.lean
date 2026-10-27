module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_pow_three_of_orderOf_eq_nine {u a : G} (hu : orderOf u = 9)
    (ha : a ∈ Subgroup.zpowers u) (ha3 : a ^ 3 = 1) : a ∈ Subgroup.zpowers (u ^ 3) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h1 : u ^ (k * 3) = 1 := by rw [zpow_mul]; exact_mod_cast ha3
  have h9 : ((9 : ℕ) : ℤ) ∣ k * 3 := hu ▸ orderOf_dvd_iff_zpow_eq_one.mpr h1
  obtain ⟨m, rfl⟩ : (3 : ℤ) ∣ k := by omega
  refine ⟨m, ?_⟩
  show (u ^ (3 : ℕ)) ^ m = u ^ (3 * m)
  rw [← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]

omit [Finite G] in
theorem zpowers_le_normalizer_zpowers_of_mul_comm {u v : G} (huv : u * v = v * u) :
    Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_le]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact ((Commute.zpow_left (Commute.eq huv).symm k).eq)

omit [Finite G] in
theorem card_zpowers_sup_zpowers_of_orderOf_eq_nine {u v : G} (hu : orderOf u = 9)
    (hv : orderOf v = 9) (huv : u * v = v * u)
    (hbot : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) :
    Nat.card (Subgroup.zpowers v ⊔ Subgroup.zpowers u : Subgroup G) = 81 := by
  have h := card_sup_mul_card_inf_eq_of_le_normalizer
    (zpowers_le_normalizer_zpowers_of_mul_comm huv)
  rw [inf_comm, hbot, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hu, hv] at h
  omega

theorem mem_zpowers_cube_sup_of_pow_three_eq_one {U : Subgroup G} {u v : G} (huU : u ∈ U)
    (hvU : v ∈ U) (hU : Nat.card U = 3 ^ 4) (hu : orderOf u = 9) (hv : orderOf v = 9)
    (huv : u * v = v * u) (hbot : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) {w : G}
    (hw : w ∈ U) (hw3 : w ^ 3 = 1) :
    w ∈ Subgroup.zpowers (u ^ 3) ⊔ Subgroup.zpowers (v ^ 3) := by
  have hle : Subgroup.zpowers v ⊔ Subgroup.zpowers u ≤ U :=
    sup_le (Subgroup.zpowers_le.mpr hvU) (Subgroup.zpowers_le.mpr huU)
  have heq : Subgroup.zpowers v ⊔ Subgroup.zpowers u = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [hU, card_zpowers_sup_zpowers_of_orderOf_eq_nine hu hv huv hbot]; norm_num)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers u)
    (Subgroup.zpowers v) (zpowers_le_normalizer_zpowers_of_mul_comm huv)
  rw [sup_comm, heq] at hset
  have hw' : w ∈ ((Subgroup.zpowers u : Set G) * (Subgroup.zpowers v : Set G)) := by
    rw [← hset]; exact hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have hab : Commute a b := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_zpow (huv : Commute u v) i j
  have h3 : a ^ 3 * b ^ 3 = 1 := by rw [← hab.mul_pow]; exact hw3
  have hmem : a ^ 3 ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
    refine ⟨Subgroup.pow_mem _ ha 3, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h3]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 3)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hb3 : b ^ 3 = 1 := by rw [hmem, one_mul] at h3; exact h3
  exact Subgroup.mul_mem_sup (mem_zpowers_pow_three_of_orderOf_eq_nine hu ha hmem)
    (mem_zpowers_pow_three_of_orderOf_eq_nine hv hb hb3)

theorem card_zpowers_cube_sup_le_nine {u v : G} (hu : orderOf u = 9) (hv : orderOf v = 9)
    (huv : u * v = v * u) :
    Nat.card (Subgroup.zpowers (u ^ 3) ⊔ Subgroup.zpowers (v ^ 3) : Subgroup G) ≤ 9 := by
  have huv3 : u ^ 3 * v ^ 3 = v ^ 3 * u ^ 3 :=
    (Commute.pow_pow (huv : Commute u v) 3 3).eq
  have h := card_sup_mul_card_inf_eq_of_le_normalizer
    (zpowers_le_normalizer_zpowers_of_mul_comm huv3.symm)
  have hu3 : orderOf (u ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hu]; norm_num), hu]
  have hv3 : orderOf (v ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hv]; norm_num), hv]
  rw [Nat.card_zpowers, Nat.card_zpowers, hu3, hv3] at h
  have hpos : 0 < Nat.card (Subgroup.zpowers (u ^ 3) ⊓ Subgroup.zpowers (v ^ 3) : Subgroup G) :=
    Nat.card_pos
  nlinarith

theorem pRank_le_three_of_homocyclic {R U : Subgroup G} (hR : Nat.card R = 3 ^ 5) (hUR : U ≤ R)
    (hU : Nat.card U = 3 ^ 4) {u v : G} (huU : u ∈ U) (hvU : v ∈ U) (hu : orderOf u = 9)
    (hv : orderOf v = 9) (huv : u * v = v * u)
    (hbot : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) : CFSG.Open.pRank 3 R ≤ 3 := by
  apply csSup_le'
  rintro k ⟨E, hER, hE, hk⟩
  have h9 : Nat.card (U ⊓ E : Subgroup G) ≤ 9 :=
    (Subgroup.card_le_of_le fun w (hw : w ∈ U ⊓ E) =>
      mem_zpowers_cube_sup_of_pow_three_eq_one huU hvU hU hu hv huv hbot
        (Subgroup.mem_inf.mp hw).1 (hE.2 w (Subgroup.mem_inf.mp hw).2)).trans
      (card_zpowers_cube_sup_le_nine hu hv huv)
  have hRU : U.relIndex R = 3 := by
    have h := Subgroup.card_mul_index (U.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv, hU, hR] at h
    rw [Subgroup.relIndex]
    omega
  have hEU : U.relIndex E ≤ 3 := hRU ▸ Subgroup.relIndex_le_of_le_right hER (by omega)
  have hcard : Nat.card E = Nat.card (U ⊓ E : Subgroup G) * U.relIndex E := by
    have h := Subgroup.card_mul_index (U.subgroupOf E)
    rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype]
      at h
    rw [Subgroup.relIndex, h]
  have hle : 3 ^ k ≤ 3 ^ 3 := by
    rw [← hk, hcard]
    calc Nat.card (U ⊓ E : Subgroup G) * U.relIndex E ≤ 9 * 3 := Nat.mul_le_mul h9 hEU
      _ = 3 ^ 3 := by norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem D1Sp48NData.pRank_le {P : Sylow 3 G} {M H R X U A V : Subgroup G}
    (hd : D1Sp48NData P M H R X U A V) : CFSG.Open.pRank 3 R ≤ 3 := by
  obtain ⟨u, v, huU, hvU, hu, hv, huv, hbot⟩ := hd.homocyclic
  exact pRank_le_three_of_homocyclic hd.card_R hd.U_le hd.card_U huU hvU hu hv huv hbot

theorem D1Sp48NData.exists_cube {P : Sylow 3 G} {M H R X U A V : Subgroup G}
    (hd : D1Sp48NData P M H R X U A V) {x : G} (hx : x ∈ X) : ∃ w ∈ R, w ^ 3 = x := by
  obtain ⟨u, v, huU, hvU, hu, hv, huv, hbot⟩ := hd.homocyclic
  have hcomm : Commute u v := huv
  have hle : X ≤ Subgroup.zpowers (u ^ 3) ⊔ Subgroup.zpowers (v ^ 3) := fun w hw =>
    mem_zpowers_cube_sup_of_pow_three_eq_one huU hvU hd.card_U hu hv huv hbot (hd.X_le_U hw)
      (hd.elem_X.2 w hw)
  have heq : X = Subgroup.zpowers (u ^ 3) ⊔ Subgroup.zpowers (v ^ 3) :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [hd.card_X]; exact card_zpowers_cube_sup_le_nine hu hv huv)
  rw [heq] at hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers (u ^ 3))
    (Subgroup.zpowers (v ^ 3)) (zpowers_le_normalizer_zpowers_of_mul_comm (hcomm.pow_pow 3 3).eq)
  have hx' : x ∈ ((Subgroup.zpowers (u ^ 3) : Set G) * (Subgroup.zpowers (v ^ 3) : Set G)) := by
    rw [← hset]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨u ^ i * v ^ j, hd.U_le (U.mul_mem (U.zpow_mem huU i) (U.zpow_mem hvU j)), ?_⟩
  rw [(hcomm.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
    ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm i, mul_comm j]

end CFSG.AGLEmbedding
