module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Main
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SNAV
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6P6b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec6S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_secprop_A6 {N K : Subgroup G} (ψ : ↥N →* Equiv.Perm (Fin 6))
    (hker : ψ.ker = K.subgroupOf N) (hA6 : alternatingGroup (Fin 6) ≤ ψ.range) :
    SecProp N K (fun Y _ _ _ =>
      ∃ X : Subgroup (MulAut (alternatingGroup (Fin 6))),
        (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ≤ X ∧
          Nonempty (Y ≃* ↥X)) := by
  have hn : (K.subgroupOf N).Normal := hker ▸ ψ.normal_ker
  refine ⟨hn, ?_⟩
  obtain ⟨X, hX, ⟨e⟩⟩ := y6_sub_to_autA6 hA6
  refine ⟨X, hX, ⟨?_⟩⟩
  haveI := hn
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans e

theorem y6_fact61 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) : c.Fact61 := by
  have cfg := c.y6cfg hH
  obtain ⟨ψ, hker, hK, hCY, hXC, hA6, -⟩ := y6_main c hH hF
  have hNC1 := y6_NC1_eq c hH hF
  have hNC0 := y6_NC0_eq c hH hF
  have hodd : c.s.oddH = ⊥ := f3_oddH_eq_bot hH.hS c.s
  refine ⟨?_, ?_, y6_NAV_le_NV cfg, ?_, ?_, ?_, ?_⟩
  · rw [hNC0, hNC1]
    exact inf_le_left
  · rw [hNC1]
    exact y6_X_le_NAV cfg
  · have hYN : y6Y c ≤ normalizer (C0 c.e : Set G) := s6_Y_le_NC0 c hH
    have h := Subgroup.relIndex_mul_card (H := y6Y c) (K := normalizer (C0 c.e : Set G))
    rw [inf_of_le_left hYN] at h
    have hcard : Nat.card ↥(normalizer (C0 c.e : Set G)) = 2 * Nat.card ↥(y6Y c) := by
      rw [hNC0]
      exact hCY
    have hpos : 0 < Nat.card ↥(y6Y c) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h.trans hcard)
  · rw [hodd, bot_sup_eq]
    exact hK
  · rw [hodd, bot_sup_eq, hNC1]
    rw [hK] at hker
    exact y6_secprop_A6 ψ hker hA6
  · rw [hNC1]
    have hle : c.s.T ⊔ M3 c.s ≤ y6X c := y6_TM3_le_X c hH hF
    refine ⟨hle, y6_TM3_pgroup c hH hF, ?_⟩
    have h := Subgroup.relIndex_mul_card (H := c.s.T ⊔ M3 c.s) (K := y6X c)
    rw [inf_of_le_left hle, y6_card_TM3 c hH hF, y6_card_X c hH hF] at h
    have hpos : 0 < Nat.card ↥c.s.T := Nat.card_pos
    have h1 : ((c.s.T ⊔ M3 c.s).relIndex (y6X c) * 8) * Nat.card ↥c.s.T =
        360 * Nat.card ↥c.s.T := by
      rw [mul_assoc]
      exact h
    have h2 : (c.s.T ⊔ M3 c.s).relIndex (y6X c) * 8 = 360 := Nat.eq_of_mul_eq_mul_right hpos h1
    have h3 : (c.s.T ⊔ M3 c.s).relIndex (y6X c) = 45 := by omega
    rw [h3]
    decide

end CFSG.OddStandard.HigherRank.YamadaG23
