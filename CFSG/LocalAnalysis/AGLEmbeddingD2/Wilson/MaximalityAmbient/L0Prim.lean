module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77Bridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.OddLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77
public import Certificates.Certificate12634

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.L0Prim

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
  CFSG.AGLEmbeddingD2.Wilson.Coordinator
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] def letterPerm (k : ℕ) : Equiv.Perm (Fin 77) :=
  if k = 0 then sPerm 0 else if k = 1 then sPerm 0 ^ 2 else if k = 2 then sPerm 2
  else if k = 3 then sPerm 2 ^ 4 else 1

theorem encP_letterPerm (k : ℕ) : encP (letterPerm k) = lettersData.getD k idA := by
  have h0 : encP (sPerm 0) = dataS[0]! := (encP_sPerm 0).trans (by rfl)
  have h2 : encP (sPerm 2) = dataS[2]! := (encP_sPerm 2).trans (by rfl)
  unfold letterPerm
  split_ifs with a b c d
  · subst a; rw [h0]; rfl
  · subst b; rw [encP_pow, h0]; rfl
  · subst c; rw [h2]; rfl
  · subst d; rw [encP_pow, h2]; rfl
  · have hsz : lettersData.size = 4 := rfl
    rw [encP_one, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

section Facts

variable (hF : J4Facts)

theorem subgroupOf_inf_centralizer {G : Type*} [Group G] (z c : G)
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf
        (Subgroup.centralizer ({z} : Set G)) =
      Subgroup.centralizer ({(⟨c, hc⟩ : ↥(Subgroup.centralizer ({z} : Set G)))} :
        Set ↥(Subgroup.centralizer ({z} : Set G))) := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subtype.ext_iff, Subgroup.coe_mul]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨Subgroup.mem_centralizer_singleton_iff.1 m.2, h⟩

theorem L0_subgroupOf_eq :
    L0.subgroupOf M2 = Subgroup.centralizer ({(⟨cE, cE_mem_M2 hF.mat⟩ : ↥M2)} : Set ↥M2) :=
  subgroupOf_inf_centralizer z0 cE (cE_mem_M2 hF.mat)

theorem mem_map_L0_of_odd (g : ↥M2) (hg : Odd (orderOf (rho hF g))) :
    rho hF g ∈ (L0.subgroupOf M2).map (rho hF) := by
  rw [L0_subgroupOf_eq hF]
  refine mem_map_centralizer_of_odd (rho hF) (c := (⟨cE, cE_mem_M2 hF.mat⟩ : ↥M2)) (m := 2 ^ 13)
    (rho_cE hF) ?_ ?_ (by norm_num) g hg
  · rw [← Subgroup.orderOf_coe]
    exact orderOf_cE hF.mat
  · rw [(card_range_ker_rho hF).2]
    norm_num

theorem sPerm_mem_G (k : Fin 9) (hk : Odd (orderOf (sPerm k))) :
    sPerm k ∈ (L0.subgroupOf M2).map (rho hF) := by
  obtain ⟨g, hg⟩ := sigPerm_mem_range hF (nIdx_lt k)
  have : rho hF g = sPerm k := hg
  rw [← this]
  exact mem_map_L0_of_odd hF g (by rw [this]; exact hk)

theorem orders_sPerm :
    orderOf (sPerm 0) = 3 ∧ orderOf (sPerm 2) = 5 ∧ orderOf (sPerm 3) = 7 ∧
      orderOf (sPerm 4) = 11 := by
  obtain ⟨-, -, hO⟩ := primCheck_parts Certificates.certificate12634
  obtain ⟨o3, o5, o7, o11, -, -⟩ := chkOrders_parts hO
  have f3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have f5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have f7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have f11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact ⟨orderOf_eq_of_chkOrder ((encP_sPerm 0).trans (by rfl)) o3,
    orderOf_eq_of_chkOrder ((encP_sPerm 2).trans (by rfl)) o5,
    orderOf_eq_of_chkOrder ((encP_sPerm 3).trans (by rfl)) o7,
    orderOf_eq_of_chkOrder ((encP_sPerm 4).trans (by rfl)) o11⟩

theorem letterPerm_mem (k : ℕ) : letterPerm k ∈ (L0.subgroupOf M2).map (rho hF) := by
  obtain ⟨o3, o5, -, -⟩ := orders_sPerm
  have h0 := sPerm_mem_G hF 0 (by rw [o3]; decide)
  have h2 := sPerm_mem_G hF 2 (by rw [o5]; decide)
  unfold letterPerm
  split_ifs
  · exact h0
  · exact Subgroup.pow_mem _ h0 _
  · exact h2
  · exact Subgroup.pow_mem _ h2 _
  · exact Subgroup.one_mem _

theorem L0_rho_isPreprimitive :
    MulAction.IsPreprimitive ↥((L0.subgroupOf M2).map (rho hF)) (Fin 77) := by
  obtain ⟨hT, hS, -⟩ := primCheck_parts Certificates.certificate12634
  exact isPreprimitive_of_letters letterPerm encP_letterPerm _ (letterPerm_mem hF) hT hS

theorem le_card_of_orders {Γ : Type*} [Group Γ] [Finite Γ] (G : Subgroup Γ) {a b c d e : Γ}
    (ha : a ∈ G) (hb : b ∈ G) (hc : c ∈ G) (hd : d ∈ G) (he : e ∈ G)
    (oa : orderOf a = 8) (ob : orderOf b = 3) (oc : orderOf c = 5) (od : orderOf d = 7)
    (oe : orderOf e = 11) : 9240 ≤ Nat.card G := by
  have d8 : 8 ∣ Nat.card G := oa ▸ Subgroup.orderOf_dvd_natCard G ha
  have d3 : 3 ∣ Nat.card G := ob ▸ Subgroup.orderOf_dvd_natCard G hb
  have d5 : 5 ∣ Nat.card G := oc ▸ Subgroup.orderOf_dvd_natCard G hc
  have d7 : 7 ∣ Nat.card G := od ▸ Subgroup.orderOf_dvd_natCard G hd
  have d11 : 11 ∣ Nat.card G := oe ▸ Subgroup.orderOf_dvd_natCard G he
  have d24 : 24 ∣ Nat.card G := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d8 d3
  have d120 : 120 ∣ Nat.card G := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d24 d5
  have d840 : 840 ∣ Nat.card G := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d120 d7
  have d9240 : 9240 ∣ Nat.card G := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d840 d11
  exact Nat.le_of_dvd Nat.card_pos d9240

theorem four_thousand_six_hundred_twenty_lt_card_L0_rho :
    4620 < Nat.card ↥((L0.subgroupOf M2).map (rho hF)) := by
  obtain ⟨-, -, hO⟩ := primCheck_parts Certificates.certificate12634
  obtain ⟨-, -, -, -, h4, h8⟩ := chkOrders_parts hO
  obtain ⟨o3, o5, o7, o11⟩ := orders_sPerm
  have := le_card_of_orders ((L0.subgroupOf M2).map (rho hF))
    (evalPerm_mem letterPerm _ (letterPerm_mem hF) w8Word)
    (sPerm_mem_G hF 0 (by rw [o3]; decide)) (sPerm_mem_G hF 2 (by rw [o5]; decide))
    (sPerm_mem_G hF 3 (by rw [o7]; decide)) (sPerm_mem_G hF 4 (by rw [o11]; decide))
    (orderOf_word8 letterPerm encP_letterPerm h4 h8) o3 o5 o7 o11
  omega

end Facts

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.L0Prim
