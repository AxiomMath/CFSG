module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoLiftSubgroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree

open Equiv Subgroup

theorem card_eq_two_mul_card_inf_centralizer {X : Type*} [Group X] {N : Subgroup X} {x x' : X}
    (hne : x' ≠ x) (h : ∀ b ∈ N, b * x * b⁻¹ = x ∨ b * x * b⁻¹ = x') {a : X} (ha : a ∈ N)
    (hax : a * x * a⁻¹ = x') :
    Nat.card N = 2 * Nat.card (N ⊓ centralizer ({x} : Set X) : Subgroup X) := by
  set C := N ⊓ centralizer ({x} : Set X)
  have hC : ∀ b : X, b ∈ C ↔ b ∈ N ∧ b * x * b⁻¹ = x := fun b => by
    rw [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ⟨fun hbx => by rw [hbx, mul_inv_cancel_right], fun hbx => ?_⟩
    calc b * x = b * x * b⁻¹ * b := by group
      _ = x * b := by rw [hbx]
  have hcancel : ∀ b : X, b * x' * b⁻¹ = b * x * b⁻¹ → False := fun b h' =>
    hne (by simpa using h')
  have hidx : (C.subgroupOf N).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨a, ha⟩, fun ⟨b, hb⟩ => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, hC, hC]
    show Xor (b * a ∈ N ∧ b * a * x * (b * a)⁻¹ = x) (b ∈ N ∧ b * x * b⁻¹ = x)
    have hba : b * a ∈ N := N.mul_mem hb ha
    have key : b * a * x * (b * a)⁻¹ = b * x' * b⁻¹ := by rw [← hax]; group
    rcases h b hb with hbx | hbx
    · refine Or.inr ⟨⟨hb, hbx⟩, fun ⟨_, h'⟩ => hcancel b ?_⟩
      rw [← key, h', hbx]
    · refine Or.inl ⟨⟨hba, ?_⟩, fun ⟨_, h'⟩ => hne (hbx.symm.trans h')⟩
      rcases h _ hba with h' | h'
      · exact h'
      · exact absurd (by rw [← key, h', hbx]) (hcancel b)
  have h1 := card_mul_index (C.subgroupOf N)
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [← h1]
  exact mul_comm _ _

theorem eq_or_eq_inv_of_mem_zpowers {X : Type*} [Group X] {s y : X} (hs : orderOf s = 3)
    (hy : y ∈ zpowers s) (hy1 : y ≠ 1) : y = s ∨ y = s⁻¹ := by
  classical
  have hfin : IsOfFinOrder s := orderOf_pos_iff.mp (by rw [hs]; norm_num)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hs, Finset.mem_image] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  rw [Finset.mem_range] at hk
  interval_cases k
  · exact absurd (pow_zero s) hy1
  · exact Or.inl (pow_one s)
  · exact Or.inr (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hs3]))

theorem exists_conj_mem_zpowers {X : Type*} [Group X] [Finite X] (K : Subgroup X) {m : ℕ}
    (hK : Nat.card K = m * 3 ^ 1) (hm : ¬ 3 ∣ m) {x s : X} (hx : x ∈ K) (hs : s ∈ K)
    (hox : orderOf x = 3) (hos : orderOf s = 3) : ∃ c ∈ K, c * x * c⁻¹ ∈ zpowers s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ y : K, orderOf (y : X) = 3 → ∃ P : Sylow 3 K, (P : Subgroup K) = zpowers y := by
    intro y hy
    have hy' : orderOf y = 3 := by rwa [Subgroup.orderOf_coe] at hy
    obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (p := 3) (P := zpowers y)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy', pow_one]))
    refine ⟨P, (eq_of_le_of_card_ge hP ?_).symm⟩
    rw [Nat.card_zpowers, hy', JankoPerm.card_sylow_eq P (k := 1) (m := m)
      (by rw [hK]; exact dvd_mul_left _ _) (by rw [hK]) hm, pow_one]
  obtain ⟨P₁, hP₁⟩ := hsyl ⟨x, hx⟩ hox
  obtain ⟨P₂, hP₂⟩ := hsyl ⟨s, hs⟩ hos
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P₁ P₂
  refine ⟨c, c.2, ?_⟩
  have hmem : c * ⟨x, hx⟩ * c⁻¹ ∈ (P₂ : Subgroup K) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul (⟨x, hx⟩ : K) (MulAut.conj c) (P₁ : Subgroup K)
      (by rw [hP₁]; exact mem_zpowers _)
    simpa only [MulAut.smul_def, MulAut.conj_apply] using this
  rw [hP₂] at hmem
  have := Subgroup.mem_map_of_mem K.subtype hmem
  rw [MonoidHom.map_zpowers] at this
  simpa using this

section TwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem ker_proj_le {X : Subgroup J} (hX : zbar J ∈ X) : (proj e).ker ≤ X := by
  rw [ker_proj]
  intro c hc
  rcases hJ.mem_center_iff.mp hc with rfl | rfl
  · exact X.one_mem
  · exact hX

theorem comap_map_proj {X : Subgroup J} (hX : zbar J ∈ X) : (X.map (proj e)).comap (proj e) = X :=
  comap_map_eq_self (ker_proj_le hJ e hX)

theorem card_eq_two_mul_card_map {X : Subgroup J} (hX : zbar J ∈ X) :
    Nat.card X = 2 * Nat.card (X.map (proj e)) := by
  conv_lhs => rw [← comap_map_proj hJ e hX]
  exact hJ.card_comap_proj e _

theorem comap_eq_liftOddSubgroup_sup {Y : Subgroup (alternatingGroup (Fin 9))}
    (hY : Odd (Nat.card Y)) : Y.comap (proj e) = liftOddSubgroup e Y ⊔ zpowers (zbar J) := by
  have hz : zbar J ∈ liftOddSubgroup e Y ⊔ zpowers (zbar J) :=
    (le_sup_right : zpowers (zbar J) ≤ _) (mem_zpowers _)
  rw [← comap_map_proj hJ e hz, Subgroup.map_sup, hJ.map_liftOddSubgroup e hY,
    MonoidHom.map_zpowers,
    hJ.proj_zbar e, zpowers_one_eq_bot, sup_bot_eq]

theorem liftOddSubgroup_inf_centralizer {Y : Subgroup (alternatingGroup (Fin 9))}
    (hY : Odd (Nat.card Y)) (u : J) : liftOddSubgroup e Y ⊓ centralizer {u} =
      liftOddSubgroup e (Y ⊓ centralizer {proj e u}) := by
  have hY' : Odd (Nat.card (Y ⊓ centralizer {proj e u} : Subgroup _)) :=
    hY.of_dvd_nat (card_dvd_of_le inf_le_left)
  ext x
  rw [mem_inf, hJ.mem_liftOddSubgroup_iff e hY, hJ.mem_liftOddSubgroup_iff e hY', mem_inf,
    mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hxY, hxo⟩, hxu⟩
    exact ⟨⟨hxY, by rw [← map_mul, hxu, map_mul]⟩, hxo⟩
  · rintro ⟨⟨hxY, hxu⟩, hxo⟩
    exact ⟨⟨hxY, hxo⟩, (hJ.commute_of_odd_orderOf e hxo hxu.symm).eq.symm⟩

theorem comap_le_centralizer {Y : Subgroup (alternatingGroup (Fin 9))} (hY : Odd (Nat.card Y))
    {b : J} (h : Y ≤ centralizer {proj e b}) : Y.comap (proj e) ≤ centralizer {b} := by
  rw [comap_eq_liftOddSubgroup_sup hJ e hY, sup_le_iff]
  constructor
  · intro x hx
    obtain ⟨hxY, hxo⟩ := (hJ.mem_liftOddSubgroup_iff e hY).mp hx
    rw [mem_centralizer_singleton_iff]
    exact (hJ.commute_of_odd_orderOf e hxo (mem_centralizer_singleton_iff.mp (h hxY)).symm).eq.symm
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    exact (hJ.commute_zbar b).eq.symm

end TwoANine

section Transport

variable {G : Type*} [Group G] {z : G}

theorem coe_zbar_eq (hz : orderOf z = 2) (hH : IsTwoANine (centralizer ({z} : Set G))) :
    (zbar (centralizer ({z} : Set G)) : G) = z := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine congrArg Subtype.val (hH.eq_zbar_of_mem_center (z := ⟨z, mem_centralizer_singleton_iff.mpr
    rfl⟩) ?_ fun h => hz1 (congrArg Subtype.val h)).symm
  exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)

theorem map_subtype_zpowers_zbar (hz : orderOf z = 2)
    (hH : IsTwoANine (centralizer ({z} : Set G))) :
    (zpowers (zbar (centralizer ({z} : Set G)))).map (centralizer ({z} : Set G)).subtype =
      zpowers z := by
  rw [MonoidHom.map_zpowers, coe_subtype, coe_zbar_eq hz hH]

end Transport

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree
