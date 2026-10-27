module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Dich
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1KY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Psi
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Count
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SOrd6

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_all16 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ w ∈ c.s.fr.A ⊔ C0 c.e, w ∉ c.s.fr.A ⊔ V1 c.e → w ∈ y7aO (y7aX c) (V1 c.e) c.s.t := by
  rcases y7a_dichotomy c hH hF with h16 | hUm
  · exact h16
  · exfalso
    have h := c.y7acfg hH
    have hUp : ∀ w ∈ y6Up c.s.fr.A (V1 c.e) c.s.t, w ∈ y7aO (y7aX c) (V1 c.e) c.s.t :=
      y7a_trans_Up c hH hF
    have hX1 : y7aX c ≤ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) := inf_le_left
    have hX2 : y7aX c ≤ normalizer (V1 c.e : Set G) := inf_le_right
    obtain ⟨ψ, hker⟩ := y7a_psi6 h hX1 hX2 hUp hUm
    have hker' : ψ.ker = (y7aK c).subgroupOf (y7aX c) := hker
    have hYX : y7aY c ≤ y7aX c := y7a_Y_le_X c hH
    have hXC : Nat.card ↥(y7aX c) = 10 * Nat.card ↥(y7aY c) :=
      y7a_orbit10 h hYX hX1 hX2 (fun x hx => (y7a_stab_iff h (hX1 hx)).symm) hUp hUm
    have hKY : y7aK c ⊓ y7aY c = C1 c.e := y7a_K_inf_Y c hH
    have hC1Y : C1 c.e ≤ y7aY c := y6_C1_le_NAt h.cfg
    have hKC : y7aK c ≤ y7aY c := (y7a_K_eq_C1 c hH).le.trans hC1Y
    have hC1K : C1 c.e ≤ y7aK c := y7a_C1_le_K h
    have hYm := y6_card_Y_m c.toCtx5 hH
    have hpos : 0 < Nat.card ↥(y7aY c) := Nat.card_pos
    by_cases hRT : c.s.R = c.s.T
    · obtain ⟨hCeq, -⟩ := y6_count (y7aX c) (y7aY c) (y7aY c) (y7aK c) (C1 c.e) ψ hker' hYX le_rfl
        hKC hC1K hC1Y hKY hXC (by omega) (m := 18) (Or.inl rfl) (hYm.1 hRT)
        (fun h => absurd h (by norm_num))
      omega
    · obtain ⟨y, hyY, hy6, hy2, hy3⟩ := y6_exists_order6 c.toCtx5 hH hRT
      have h6 : (36 : ℕ) = 36 → ∃ x : ↥(y7aX c), (x : G) ∈ y7aY c ∧ orderOf (ψ x) = 6 :=
        fun _ => y6_order_six ψ hker' hKY hYX hyY hy6 hy2 hy3
      obtain ⟨hCeq, -⟩ := y6_count (y7aX c) (y7aY c) (y7aY c) (y7aK c) (C1 c.e) ψ hker' hYX le_rfl
        hKC hC1K hC1Y hKY hXC (by omega) (m := 36) (Or.inr rfl) (hYm.2 hRT) h6
      omega

end CFSG.OddStandard.HigherRank.YamadaG23
