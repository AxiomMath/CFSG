module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GCnt
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ExtremalTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_card_T2 (hH : F33Hyp s e) : Nat.card ↥s.T₂ = 4 * Nat.card ↥s.T := by
  have h := Subgroup.relIndex_mul_card (H := s.T) (K := s.T₂)
  rw [f3_T_relIndex_T₂ hH, inf_eq_left.mpr (y4_T_le_T2 s)] at h
  exact h.symm

private theorem y4_B_inf_zpowers_t (hH : F33Hyp s e) : s.fr.B ⊓ zpowers s.t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxB, hxt⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxt
  rw [← hn] at hxB ⊢
  rcases Int.emod_two_eq_zero_or_one n with h2 | h2
  · have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
    rw [show s.t ^ n = 1 by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp]
  · exfalso
    have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
    have htn : s.t ^ n = s.t := by rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp
    exact s3_t_not_mem_L s hH.h31 (htn ▸ f3_B_le_L s hxB)

theorem y4_card_P (hH : F33Hyp s e) : Nat.card ↥(f3P s) = 64 := by
  have hnorm : ∀ x ∈ s.fr.B, ∀ y ∈ zpowers s.t, x * y * x⁻¹ ∈ zpowers s.t := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    have hc : Commute x s.t := s3_comm_t_of_mem_L s (f3_B_le_L s hx)
    rw [(hc.zpow_right n).eq]
    group
  have hrel : s.fr.B.relIndex (s.fr.B ⊔ zpowers s.t) = 2 := by
    rw [relIndex_sup_of_normalizes hnorm, y4_B_inf_zpowers_t hH, Subgroup.relIndex_bot_left,
      Nat.card_zpowers, s.t_order]
  have hprod : s.fr.B.relIndex (s.fr.B ⊔ zpowers s.t) * Nat.card ↥s.fr.B =
      Nat.card ↥(s.fr.B ⊔ zpowers s.t) := by
    have h := Subgroup.relIndex_mul_card (H := s.fr.B) (K := s.fr.B ⊔ zpowers s.t)
    rwa [inf_eq_left.mpr le_sup_left] at h
  change Nat.card ↥(s.fr.B ⊔ zpowers s.t) = 64
  rw [← hprod, hrel, y54_card_B hH]

theorem y4_card_C2 (hH : F33Hyp s e) : Nat.card ↥s.C₂ = 256 := by
  have h := Subgroup.relIndex_mul_card (H := f3P s) (K := s.C₂)
  rw [f3_P_relIndex_C₂ hH, inf_eq_left.mpr (f3_P_le_C₂ hH), y4_card_P hH] at h
  norm_num at h
  exact h.symm

theorem y4_conj_t_mul_self {x : G} (hx : IsConj s.t x) : x * x = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  rw [← hg]
  have htt : s.t * s.t = 1 := by rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
  calc (g * s.t * g⁻¹) * (g * s.t * g⁻¹) = g * (s.t * s.t) * g⁻¹ := by group
    _ = 1 := by rw [htt, mul_one, mul_inv_cancel]

theorem y4_conj_t_not_mem_L (hH : F33Hyp s e) {x : G} (hx : IsConj s.t x) : x ∉ L := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  rw [← hg]
  exact hH.h31.2.2.1 g

theorem y4_cp (hH : F33Hyp s e) {x : G} (hx : IsExtremalConj s.T₂ s.t x) {N : Subgroup G}
    (hN : N ≤ s.T₂) : Nat.card ↥N ≤ 4 * Nat.card ↥(centEl N x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHT : s.H ⊓ s.T₂ = s.T := by
    symm
    exact sylowIn_eq_of_le s.sylow_T ((f3_c9 hH).2.1.to_le inf_le_right) inf_le_left
      (le_inf s.sylow_T.1 (y4_T_le_T2 s))
  have hcent_t : centEl s.T₂ s.t = s.T := by
    change s.T₂ ⊓ s.H = s.T
    rw [inf_comm, hHT]
  have hle : Nat.card ↥s.T ≤ Nat.card ↥(centEl s.T₂ x) := by
    rw [← hcent_t]
    exact hx.2.2 s.t (y4_t_mem_T2 s) (IsConj.refl s.t)
  have hcard : Nat.card ↥s.T₂ ≤ 4 * Nat.card ↥(centEl s.T₂ x) := by
    rw [y4_card_T2 hH]
    exact Nat.mul_le_mul_left 4 hle
  have hrel : (centEl s.T₂ x).relIndex s.T₂ ≤ 4 := by
    have hmul := Subgroup.relIndex_mul_card (H := centEl s.T₂ x) (K := s.T₂)
    rw [inf_eq_left.mpr (show centEl s.T₂ x ≤ s.T₂ from inf_le_left)] at hmul
    have hineq : (centEl s.T₂ x).relIndex s.T₂ * Nat.card ↥(centEl s.T₂ x) ≤
        4 * Nat.card ↥(centEl s.T₂ x) := by
      rw [hmul]
      exact hcard
    have hpos : 0 < Nat.card ↥(centEl s.T₂ x) := by
      haveI : Nonempty ↥(centEl s.T₂ x) := ⟨1⟩
      exact Nat.card_pos
    exact Nat.le_of_mul_le_mul_right hineq hpos
  have hinf : N ⊓ centEl s.T₂ x = centEl N x := by
    rw [centEl, centEl, ← inf_assoc, inf_eq_left.mpr hN]
  calc Nat.card ↥N
      ≤ (centEl s.T₂ x).relIndex s.T₂ * Nat.card ↥(N ⊓ centEl s.T₂ x) :=
        y4_card_le_relIndex_mul hN inf_le_left
    _ = (centEl s.T₂ x).relIndex s.T₂ * Nat.card ↥(centEl N x) := by rw [hinf]
    _ ≤ 4 * Nat.card ↥(centEl N x) := Nat.mul_le_mul_right _ hrel

end CFSG.OddStandard.HigherRank.YamadaG23
