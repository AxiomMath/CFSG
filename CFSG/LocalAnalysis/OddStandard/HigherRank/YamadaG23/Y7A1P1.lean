module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Set
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1N0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1NZ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Rk

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_normC0_le (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ normalizer (C0 c.e : Set G), x ∈ y7aY c ∧ x ∈ normalizer (V1 c.e : Set G) := by
  intro x hx
  obtain ⟨hxz, hcase⟩ := y7a_norm_C0 (c.y7acfg hH) hx
  have hrank := y7a_rank_H c.toCtx5 hH
  have hbig : 32 < Nat.card ↥(M3 c.s) := by
    rw [y7a_card_M3 c hH]
    norm_num
  have hM := y7a_M3_elemAbelian c hH
  rcases hcase with ⟨hxt, hxV⟩ | hxt
  · exact ⟨y7a_NZ_le_Y c.toCtx5 hH hxz hxt, hxV⟩
  · exfalso
    rcases hxt with h | h
    · exact y7a_not_conj_of_rank hM (y7a_d_mem_M3 c) hbig hrank x h
    · refine y7a_not_conj_of_rank hM ?_ hbig hrank x h
      exact (M3 c.s).mul_mem (y7a_V1_le_M3 c (y7a_z_mem_V (c.y7acfg hH))) (y7a_d_mem_M3 c)

theorem y7a_normC0_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    normalizer (C0 c.e : Set G) = y7aY c :=
  le_antisymm (fun _ hx => (y7a_normC0_le c hH _ hx).1) (s5_Y_le_NC0 c.toCtx5 hH)

theorem y7a_fact71_1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    normalizer (C0 c.e : Set G) = normIn c.s.H c.s.fr.A ⊔ zpowers c.d ∧
      normalizer (C0 c.e : Set G) ≤ normalizer (V1 c.e : Set G) :=
  ⟨(y7a_normC0_eq c hH).trans (s5_Y_eq c.toCtx5 hH), fun x hx => (y7a_normC0_le c hH x hx).2⟩

theorem y7a_Y_le_X (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : y7aY c ≤ y7aX c := by
  intro x hx
  have hxC0 : x ∈ normalizer (C0 c.e : Set G) := s5_Y_le_NC0 c.toCtx5 hH hx
  exact Subgroup.mem_inf.mpr ⟨s5_Y_le_NC1 c.toCtx5 hH hx, (y7a_normC0_le c hH x hxC0).2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
