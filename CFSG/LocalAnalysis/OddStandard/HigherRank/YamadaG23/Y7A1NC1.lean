module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1No10
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1NEq
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Psi16

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_card_X (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nat.card ↥(y7aX c) = 16 * Nat.card ↥(y7aY c) := by
  have h := c.y7acfg hH
  have hX1 : y7aX c ≤ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) := inf_le_left
  have hX2 : y7aX c ≤ normalizer (V1 c.e : Set G) := inf_le_right
  exact y7a_orbit16 h (y7a_Y_le_X c hH) hX1 hX2
    (fun x hx => (y7a_stab_iff h (hX1 hx)).symm) (y7a_all16 c hH hF)

private theorem y7a_NC1_cent_le_Y (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hx1 : x ∈ normalizer (C1 c.e : Set G)) (hxt : x ∈ centralizer ({c.s.t} : Set G)) :
    x ∈ y7aY c := by
  have hxt' : x * c.s.t * x⁻¹ = c.s.t := by
    have h := Subgroup.mem_centralizer_iff.mp hxt c.s.t (Set.mem_singleton _)
    calc x * c.s.t * x⁻¹ = (c.s.t * x) * x⁻¹ := by rw [h]
      _ = c.s.t := by group
  exact y6_mem_NAt_of_cent (c.y7acfg hH).cfg hx1 hxt'

theorem y7a_NC1_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    normalizer (C1 c.e : Set G) = y7aX c := by
  have h := c.y7acfg hH
  have hH0 : normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G) =
      normIn c.s.H c.s.fr.A := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hx1, hxt⟩ := Subgroup.mem_inf.mp hx
      have hxY := y7a_NC1_cent_le_Y c hH hx1 hxt
      exact Subgroup.mem_inf.mpr ⟨hxt, s5_Y_le_NA c.toCtx5 hH hxY⟩
    · intro x hx
      obtain ⟨hxH, hxA⟩ := Subgroup.mem_inf.mp hx
      have hxY : x ∈ y7aY c := s5_NHA_le_Y c.toCtx5 hH hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (y7a_Y_le_X c hH hxY)).1, hxH⟩
  have hY : Nat.card ↥(y7aY c) = 2 * Nat.card ↥(normIn c.s.H c.s.fr.A) := y6_card_Y c.toCtx5 hH
  have hX32 : Nat.card ↥(y7aX c) =
      32 * Nat.card ↥(normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G)) := by
    rw [hH0, y7a_card_X c hH hF, hY]
    ring
  refine (y7a_normal_eq (N := normalizer (C1 c.e : Set G)) (X := y7aX c)
    (H0 := normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G)) (t := c.s.t)
    (S := {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ∧ w ^ 2 = 1})
    inf_le_left ?_ rfl hX32 ?_ (y6_card_invol h.cfg)).symm
  · intro x hx
    obtain ⟨hx1, hxt⟩ := Subgroup.mem_inf.mp hx
    exact y7a_Y_le_X c hH (y7a_NC1_cent_le_Y c hH hx1 hxt)
  · intro n hn
    have htC1 : c.s.t ∈ c.s.fr.A ⊔ C0 c.e := Subgroup.mem_sup_right (y7a_t_mem_C0 h)
    refine ⟨(Subgroup.mem_normalizer_iff.mp hn c.s.t).mp htC1, ?_, ?_⟩
    · intro hA
      exact hH.h31.2.2.1 n ((s3_A_le_L c.s) hA)
    · have ht2 : c.s.t ^ 2 = 1 := by
        have h := pow_orderOf_eq_one c.s.t
        rwa [c.s.t_order] at h
      calc (n * c.s.t * n⁻¹) ^ 2 = n * c.s.t ^ 2 * n⁻¹ := conj_pow
        _ = 1 := by rw [ht2]; group

end CFSG.OddStandard.HigherRank.YamadaG23
