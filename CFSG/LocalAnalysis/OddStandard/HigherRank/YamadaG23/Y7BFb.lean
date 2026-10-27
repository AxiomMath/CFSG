module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BFc
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Cyc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem y7b_card_le_two_mul {C Y : Subgroup G} (hYC : Y ≤ C)
    (h3 : ∀ x ∈ C, ∀ y ∈ C, x ∈ Y ∨ y ∈ Y ∨ x⁻¹ * y ∈ Y) :
    Nat.card ↥C ≤ 2 * Nat.card ↥Y := by
  classical
  by_cases hCY : C ≤ Y
  · have hEq : C = Y := le_antisymm hCY hYC
    subst hEq
    omega
  · obtain ⟨x₀, hx₀C, hx₀Y⟩ := Set.not_subset.1 hCY
    let f : ↥Y ⊕ ↥Y → ↥C := fun s =>
      match s with
      | Sum.inl y => ⟨y, hYC y.2⟩
      | Sum.inr y => ⟨x₀ * y, C.mul_mem hx₀C (hYC y.2)⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨c, hcC⟩
      by_cases hcY : c ∈ Y
      · refine ⟨Sum.inl ⟨c, hcY⟩, ?_⟩
        apply Subtype.ext
        rfl
      · have hmem : x₀⁻¹ * c ∈ Y := by
          rcases h3 x₀ hx₀C c hcC with h | h | h
          · exact absurd h hx₀Y
          · exact absurd h hcY
          · exact h
        refine ⟨Sum.inr ⟨x₀⁻¹ * c, hmem⟩, ?_⟩
        apply Subtype.ext
        change x₀ * (x₀⁻¹ * c) = c
        group
    have hle := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_sum] at hle
    omega

private theorem y7b_inf_zpowers_t_eq_bot (hH : F33Hyp s e) :
    s.fr.S ⊓ Subgroup.zpowers s.t = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxS, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
  rw [Subgroup.mem_bot]
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · have h2' : k % ((2 : ℕ) : ℤ) = 0 := h2
    rw [← zpow_mod_orderOf s.t k, s.t_order, h2']
    simp
  · exfalso
    have h2' : k % ((2 : ℕ) : ℤ) = 1 := h2
    have htk : s.t ^ k = s.t := by
      rw [← zpow_mod_orderOf s.t k, s.t_order, h2']
      simp
    rw [htk] at hxS
    exact s3_t_not_mem_L_of_odd s hH.hZ (s3_S_le_L s hxS)

private theorem y7b_mem_T_of_mem_M (hH : F33Hyp s e) {n : G}
    (hnN : n ∈ Subgroup.normalizer (s.fr.S : Set G))
    (hnM : n ∈ L ⊔ centIn s.H L) : n ∈ s.T := by
  rw [f3_centIn_H_L hH] at hnM
  obtain ⟨ℓ, hℓL, i, rfl⟩ := y5_mem_L_sup_t s hnM
  have ht_cent : s.t ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp s.t_mem x (s3_S_le_L s hx)
  have ht_norm : s.t ∈ Subgroup.normalizer (s.fr.S : Set G) :=
    Subgroup.centralizer_le_normalizer (s.fr.S : Set G) ht_cent
  have hti_norm : s.t ^ i ∈ Subgroup.normalizer (s.fr.S : Set G) :=
    Subgroup.zpow_mem _ ht_norm i
  have hℓN : ℓ ∈ Subgroup.normalizer (s.fr.S : Set G) := by
    have h : ℓ = (ℓ * s.t ^ i) * (s.t ^ i)⁻¹ := by group
    rw [h]
    exact Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ hti_norm)
  have hℓS : ℓ ∈ s.fr.S := by
    have h : ℓ ∈ normIn L s.fr.S := Subgroup.mem_inf.mpr ⟨hℓL, hℓN⟩
    rwa [y7b_NL_S hH] at h
  exact s.R_le_T (s.R.mul_mem (s.S_le_R hℓS) (s.R.zpow_mem (s3_t_mem_R s) i))

private theorem y7b_R_ne_T_of_not_mem_M (hH : F33Hyp s e) {n : G} (hnH : n ∈ s.H)
    (hnM : n ∉ L ⊔ centIn s.H L) : s.R ≠ s.T := by
  intro hRT
  have hMH : L ⊔ centIn s.H L ≤ s.H := s3_M_le_H s hH.hS
  have hMneH : L ⊔ centIn s.H L ≠ s.H := by
    intro h
    exact hnM (by rwa [h])
  have hle2 : Nat.card ↥s.H ≤ 2 * Nat.card ↥(L ⊔ centIn s.H L) :=
    y7b_card_le_two_mul hMH (y5_H_cosets hH)
  have hrelpos : 0 < (L ⊔ centIn s.H L).relIndex s.H :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card _ _) Nat.card_pos
  have hrel_le : (L ⊔ centIn s.H L).relIndex s.H ≤ 2 := by
    have hmul : (L ⊔ centIn s.H L).relIndex s.H * Nat.card ↥(L ⊔ centIn s.H L)
        ≤ 2 * Nat.card ↥(L ⊔ centIn s.H L) := by
      have h := Subgroup.relIndex_mul_card (H := L ⊔ centIn s.H L) (K := s.H)
      rw [inf_of_le_left hMH] at h
      rw [h]
      exact hle2
    exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos
  have hrel_ne1 : (L ⊔ centIn s.H L).relIndex s.H ≠ 1 := by
    intro h
    exact hMneH (le_antisymm (Subgroup.relIndex_eq_one.mp h) hMH).symm
  have hrel : (L ⊔ centIn s.H L).relIndex s.H = 2 := by omega
  have hcardH : Nat.card ↥s.H = 2 * Nat.card ↥(L ⊔ centIn s.H L) := by
    have h := Subgroup.relIndex_mul_card (H := L ⊔ centIn s.H L) (K := s.H)
    rw [inf_of_le_left hMH, hrel] at h
    exact h.symm
  have hTH : s.T ≤ s.H := s.sylow_T.1
  have hRM : s.R ≤ L ⊔ centIn s.H L := s.sylow_R.1
  have hHcard : Nat.card ↥s.H = s.T.relIndex s.H * Nat.card ↥s.T := by
    have h := Subgroup.relIndex_mul_card (H := s.T) (K := s.H)
    rw [inf_of_le_left hTH] at h
    exact h.symm
  have hMcard : Nat.card ↥(L ⊔ centIn s.H L)
      = s.R.relIndex (L ⊔ centIn s.H L) * Nat.card ↥s.R := by
    have h := Subgroup.relIndex_mul_card (H := s.R) (K := L ⊔ centIn s.H L)
    rw [inf_of_le_left hRM] at h
    exact h.symm
  have hmain : s.T.relIndex s.H * Nat.card ↥s.T
      = 2 * (s.R.relIndex (L ⊔ centIn s.H L) * Nat.card ↥s.R) := by
    calc s.T.relIndex s.H * Nat.card ↥s.T = Nat.card ↥s.H := hHcard.symm
      _ = 2 * Nat.card ↥(L ⊔ centIn s.H L) := hcardH
      _ = 2 * (s.R.relIndex (L ⊔ centIn s.H L) * Nat.card ↥s.R) := by rw [hMcard]
  have hcancel : s.T.relIndex s.H = 2 * s.R.relIndex (L ⊔ centIn s.H L) := by
    have h2 : s.T.relIndex s.H * Nat.card ↥s.T
        = (2 * s.R.relIndex (L ⊔ centIn s.H L)) * Nat.card ↥s.T := by
      rw [hmain, hRT]
      ring
    exact Nat.mul_right_cancel Nat.card_pos h2
  exact s.sylow_T.2.2 ⟨s.R.relIndex (L ⊔ centIn s.H L), hcancel⟩

theorem y7b_card_R (hH : F33Hyp s e) : Nat.card ↥s.R = 128 := by
  rw [y5_R_eq hH]
  have hcomm : ∀ x ∈ s.fr.S, ∀ y ∈ Subgroup.zpowers s.t, x * y = y * x := by
    have ht_cent : s.t ∈ Subgroup.centralizer (s.fr.S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp s.t_mem x (s3_S_le_L s hx)
    have hzple : Subgroup.zpowers s.t ≤ Subgroup.centralizer (s.fr.S : Set G) :=
      Subgroup.zpowers_le.mpr ht_cent
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hzple hy) x hx
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute s.fr.S
    (Subgroup.zpowers s.t) hcomm).1
  have hT2 : Nat.card ↥(Subgroup.zpowers s.t) = 2 := by
    rw [Nat.card_zpowers, s.t_order]
  rw [y7b_inf_zpowers_t_eq_bot hH, Subgroup.card_bot, hT2, y54_card_S hH, mul_one] at hcard
  norm_num at hcard
  exact hcard

theorem y7b_NH_S (hH : F33Hyp s e) : normIn s.H s.fr.S = s.T := by
  have hST : s.fr.S ≤ s.T := s3_S_le_T s
  have hTnorm : s.T ≤ Subgroup.normalizer (s.fr.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp (s3_S_normal_T s hH.hS)
  apply le_antisymm
  · intro n hn
    obtain ⟨hnH, hnN⟩ := Subgroup.mem_inf.mp hn
    by_cases hnM : n ∈ L ⊔ centIn s.H L
    · exact y7b_mem_T_of_mem_M hH hnN hnM
    · have hRT : s.R ≠ s.T := y7b_R_ne_T_of_not_mem_M hH hnH hnM
      obtain ⟨g, hgT, hgR⟩ := SetLike.exists_of_lt (lt_of_le_of_ne s.R_le_T hRT)
      have hgH : g ∈ s.H := s.sylow_T.1 hgT
      have hgM : g ∉ L ⊔ centIn s.H L := s3_not_mem_M s hH.hS hgT hgR
      have hgN : g ∈ Subgroup.normalizer (s.fr.S : Set G) := hTnorm hgT
      have hgnN : g⁻¹ * n ∈ Subgroup.normalizer (s.fr.S : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hnN
      have hgnT : g⁻¹ * n ∈ s.T := by
        rcases y5_H_cosets hH g hgH n hnH with h | h | h
        · exact absurd h hgM
        · exact absurd h hnM
        · exact y7b_mem_T_of_mem_M hH hgnN h
      have hgn : n = g * (g⁻¹ * n) := by group
      rw [hgn]
      exact s.T.mul_mem hgT hgnT
  · exact le_inf s.sylow_T.1 hTnorm

end CFSG.OddStandard.HigherRank.YamadaG23
