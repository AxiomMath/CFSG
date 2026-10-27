module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SProd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y6_le_normalizer_zpowers_t (s : Setting3 G L) {V : Subgroup G} (hV : V ≤ L) :
    V ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) := by
  have hcent : L ≤ Subgroup.centralizer ({s.t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp s.t_mem x hx
  calc V ≤ L := hV
    _ ≤ Subgroup.centralizer ({s.t} : Set G) := hcent
    _ = Subgroup.normalizer ({s.t} : Set G) := (Subgroup.normalizer_singleton s.t).symm
    _ ≤ Subgroup.normalizer (Subgroup.closure ({s.t} : Set G) : Set G) :=
        Subgroup.normalizer_le_normalizer_closure {s.t}
    _ = Subgroup.normalizer (Subgroup.zpowers s.t : Set G) := by
        rw [Subgroup.zpowers_eq_closure]

private theorem y6_inf_zpowers_t_eq_bot (s : Setting3 G L) (h31 : s.Fact31) {V : Subgroup G}
    (hV : V ≤ L) : V ⊓ Subgroup.zpowers s.t = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxV, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
  rw [Subgroup.mem_bot]
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · have h2' : k % ((2 : ℕ) : ℤ) = 0 := h2
    rw [← zpow_mod_orderOf s.t k, s.t_order, h2']; simp
  · exfalso
    have h2' : k % ((2 : ℕ) : ℤ) = 1 := h2
    have htk : s.t ^ k = s.t := by rw [← zpow_mod_orderOf s.t k, s.t_order, h2']; simp
    rw [htk] at hxV
    exact s3_t_not_mem_L s h31 (hV hxV)

theorem y6_card_NLA {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn L s.fr.A) = 576 := by
  obtain ⟨hn, hfrob⟩ := hH.hLF.fact18.1.2.1
  haveI := hn
  have hq : Nat.card (↥(normIn L s.fr.A) ⧸
      (zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.A)) = 18 := hfrob.1
  have hZ : zL L ⊔ s.fr.A = s.fr.A := by rw [f3_zL_eq_bot hH, bot_sup_eq]
  have hsub : Nat.card ↥((zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.A)) = 32 := by
    have hle : zL L ⊔ s.fr.A ≤ normIn L s.fr.A := by
      rw [hZ]
      exact le_inf (s3_A_le_L s) Subgroup.le_normalizer
    calc Nat.card ↥((zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.A))
        = Nat.card ↥(zL L ⊔ s.fr.A) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      _ = Nat.card ↥s.fr.A := by rw [hZ]
      _ = 32 := (lfactsA_of_setting hH.hS hH.hZ s).card_A
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((zL L ⊔ s.fr.A).subgroupOf (normIn L s.fr.A))
  rw [hq, hsub] at hcard
  norm_num at hcard
  exact hcard

theorem y6_card_NHA_inf_M {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn s.H s.fr.A ⊓ (L ⊔ centIn s.H L)) = 1152 := by
  rw [f3_centIn_H_L hH]
  have ht_cent : s.t ∈ Subgroup.centralizer (s.fr.A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact s3_comm_t_of_mem_A s ha
  have ht_norm : s.t ∈ Subgroup.normalizer (s.fr.A : Set G) :=
    Subgroup.centralizer_le_normalizer (s.fr.A : Set G) ht_cent
  have hEq : normIn s.H s.fr.A ⊓ (L ⊔ Subgroup.zpowers s.t) =
      normIn L s.fr.A ⊔ Subgroup.zpowers s.t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxNHA, hxLt⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨_, hxA⟩ := Subgroup.mem_inf.mp hxNHA
      obtain ⟨ℓ, hℓL, i, rfl⟩ := y5_mem_L_sup_t s hxLt
      have hti_norm : s.t ^ i ∈ Subgroup.normalizer (s.fr.A : Set G) :=
        Subgroup.centralizer_le_normalizer (s.fr.A : Set G)
          (Subgroup.zpow_mem (Subgroup.centralizer (s.fr.A : Set G)) ht_cent i)
      have hℓN : ℓ ∈ normIn L s.fr.A := by
        refine Subgroup.mem_inf.mpr ⟨hℓL, ?_⟩
        have hℓ_eq : ℓ = (ℓ * s.t ^ i) * (s.t ^ i)⁻¹ := by group
        rw [hℓ_eq]
        exact Subgroup.mul_mem _ hxA (Subgroup.inv_mem _ hti_norm)
      exact Subgroup.mul_mem_sup hℓN
        (Subgroup.zpow_mem (Subgroup.zpowers s.t) (Subgroup.mem_zpowers s.t) i)
    · apply sup_le
      · intro n hn
        have hnL : n ∈ L := (show normIn L s.fr.A ≤ L from inf_le_left) hn
        have hnN : n ∈ Subgroup.normalizer (s.fr.A : Set G) :=
          (show normIn L s.fr.A ≤ Subgroup.normalizer (s.fr.A : Set G) from inf_le_right) hn
        exact Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_inf.mpr ⟨s3_L_le_H s hH.hS hnL, hnN⟩,
            Subgroup.mem_sup_left hnL⟩
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ht_norm⟩,
            Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)⟩
  rw [hEq]
  have hHN : normIn L s.fr.A ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) :=
    y6_le_normalizer_zpowers_t s inf_le_left
  have hcard := y6_card_sup_mul_inf (H := normIn L s.fr.A)
    (N := Subgroup.zpowers s.t) hHN
  have hinf : normIn L s.fr.A ⊓ Subgroup.zpowers s.t = ⊥ :=
    y6_inf_zpowers_t_eq_bot s hH.h31 inf_le_left
  have hzp : Nat.card ↥(Subgroup.zpowers s.t) = 2 := by
    rw [Nat.card_zpowers, s.t_order]
  rw [hinf, Subgroup.card_bot, hzp, y6_card_NLA hH, mul_one] at hcard
  norm_num at hcard
  exact hcard

theorem y6_card_R {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥s.R = 128 := by
  rw [y5_R_eq hH]
  have hHN : s.fr.S ≤ Subgroup.normalizer (Subgroup.zpowers s.t : Set G) :=
    y6_le_normalizer_zpowers_t s (s3_S_le_L s)
  have hcard := y6_card_sup_mul_inf (H := s.fr.S) (N := Subgroup.zpowers s.t) hHN
  have hinf : s.fr.S ⊓ Subgroup.zpowers s.t = ⊥ :=
    y6_inf_zpowers_t_eq_bot s hH.h31 (s3_S_le_L s)
  have hzp : Nat.card ↥(Subgroup.zpowers s.t) = 2 := by
    rw [Nat.card_zpowers, s.t_order]
  rw [hinf, Subgroup.card_bot, hzp, y54_card_S hH, mul_one] at hcard
  norm_num at hcard
  exact hcard

end CFSG.OddStandard.HigherRank.YamadaG23
