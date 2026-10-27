module

public import CFSG.CGT.T75P.Comp81
public import CFSG.CGT.T75Q.KerZ
public import CFSG.CGT.T75P.Ident81

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem exists_mem_ne_of_two_lt_card {T : Subgroup G} (h : 2 < Nat.card T) (a b : G) :
    ∃ t ∈ T, t ≠ a ∧ t ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (T : Set G) ⊆ {a, b} := by
    intro t ht
    by_cases hta : t = a
    · simp [hta]
    · simp [hcon t ht hta]
  have h2 : (T : Set G).ncard ≤ 2 := by
    calc (T : Set G).ncard ≤ ({a, b} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          refine (Set.ncard_insert_le a ({b} : Set G)).trans ?_
          rw [Set.ncard_singleton]
  have h3 : (T : Set G).ncard = Nat.card T := (Nat.card_coe_set_eq _).symm
  omega

theorem Std81.card_H (s : Std81 T T₁) : Nat.card (hSub T (normIn T₁ T)) = 1344 := by
  obtain ⟨hTH, -, -⟩ := hSub_data T T₁
  obtain ⟨hN, e, φ, hcompat⟩ := s.hnat
  have hq : Nat.card (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_SL_three_two
  have hTs : Nat.card (T.subgroupOf (hSub T (normIn T₁ T))) = 8 := by
    rw [← s.card_T]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf (hSub T (normIn T₁ T))), hq,
    hTs]

theorem Std81.T_inf_center (s : Std81 T T₁) {Y : Subgroup G} (hHY : hSub T (normIn T₁ T) ≤ Y) :
    T.subgroupOf Y ⊓ Subgroup.center ↥Y = ⊥ := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  have htrans := natural_trans hHN s.hnat
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hy.1
  have hyG1 : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨t', ht', ht'y, ht'1⟩ := exists_mem_ne_of_two_lt_card (T := T)
    (by rw [s.card_T]; norm_num) (y : G) 1
  obtain ⟨h, hh, hhy⟩ := htrans (y : G) hyT hyG1 t' ht' ht'1
  have h1 := Subgroup.mem_center_iff.1 hy.2 ⟨h, hHY hh⟩
  have h2 : h * (y : G) = (y : G) * h := congrArg Subtype.val h1
  apply ht'y
  rw [← hhy]
  calc h * (y : G) * h⁻¹ = (y : G) * h * h⁻¹ := by rw [h2]
    _ = y := by group

theorem Std81.H_inf_center (s : Std81 T T₁) {Y : Subgroup G} (hHY : hSub T (normIn T₁ T) ≤ Y) :
    (hSub T (normIn T₁ T)).subgroupOf Y ⊓ Subgroup.center ↥Y = ⊥ := by
  obtain ⟨hTH, hHN, -⟩ := hSub_data T T₁
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hyH : (y : G) ∈ hSub T (normIn T₁ T) := Subgroup.mem_subgroupOf.1 hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := Subgroup.mem_center_iff.1 hy.2 ⟨t, hHY (hTH ht)⟩
    exact congrArg Subtype.val h1
  have hyT : (y : G) ∈ T := by
    have : (y : G) ∈ hSub T (normIn T₁ T) ⊓ Subgroup.centralizer (T : Set G) := ⟨hyH, hyC⟩
    rwa [s.hHC] at this
  have : y ∈ T.subgroupOf Y ⊓ Subgroup.center ↥Y := ⟨Subgroup.mem_subgroupOf.2 hyT, hy.2⟩
  rwa [s.T_inf_center hHY, Subgroup.mem_bot] at this

theorem Std81.hcl_of_gen (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G))) :
    Subgroup.normalClosure ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊤ :=
  s.normalClosure_top_of_gen (s.Uc_le_ugen.trans hUY) hgen

theorem Std81.ker_eq_center (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G))) :
    (jMap ↥Y).ker = Subgroup.center ↥Y := by
  have hfin : Finite G := s.finite
  have hcl := s.hcl_of_gen hUY hgen
  have hTY : T ≤ Y := T_le_ugen.trans hUY
  exact ker_jMap_eq_center (isWC_subgroupOf s.hc.hy.pair.wc Y hTY) hcl
    (s.T_inf_pCore (s.Uc_le_ugen.trans hUY) hcl)

theorem Std81.card_map_H (s : Std81 T T₁) {Y : Subgroup G} (hUY : ugen T ≤ Y)
    (hgen : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G))) :
    Nat.card (((hSub T (normIn T₁ T)).subgroupOf Y).map (jMap ↥Y)) = 1344 := by
  have hHY : hSub T (normIn T₁ T) ≤ Y := (hSub_le_ugen s.hc (by norm_num)).trans hUY
  rw [card_map_of_inf_ker_eq_bot _ _ (by rw [s.ker_eq_center hUY hgen]; exact s.H_inf_center hHY),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv]
  exact s.card_H

theorem Std81.exists_mem_T₁_not_normalizer (s : Std81 T T₁) :
    ∃ t₁ ∈ T₁, t₁ ∉ Subgroup.normalizer (T : Set G) := by
  have hfin : Finite G := s.finite
  by_contra hcon
  push Not at hcon
  have hle : T₁ ≤ normIn T₁ T := fun t ht => mem_normIn.2 ⟨ht, hcon t ht⟩
  have h1 : Nat.card T₁ ≤ Nat.card (normIn T₁ T) := Subgroup.card_le_of_le hle
  obtain ⟨x₀, -, hx₀⟩ := s.hc.sec3.conj
  have h2 : Nat.card T₁ = 8 := by rw [hx₀, card_conjSubgroup, s.card_T]
  have h3 : Nat.card (normIn T₁ T) = 4 := by
    rw [s.hc.card_normIn_swap, s.hc.card_normIn]
    norm_num
  omega

end CFSG.CGT.T75P
