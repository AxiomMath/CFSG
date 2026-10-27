module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2K

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_card_AB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(s.fr.A ⊓ s.fr.B) = 16 := by
  change Nat.card ↥((frameWith s 1).A ⊓ (frameWith s 1).B) = 16
  obtain ⟨eD⟩ := hH.hLF.fact14.2.2.2.1.2.1.2.2.2
  rw [Nat.card_congr eD.toEquiv, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, DihedralGroup.card]

theorem y7a_S_eq_sup {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.S = s.fr.A ⊔ s.fr.B := by
  have hA : Nat.card ↥s.fr.A = 32 := y56_card_A hH
  have hB : Nat.card ↥s.fr.B = 32 := y54_card_B hH
  have hS : Nat.card ↥s.fr.S = 64 := y54_card_S hH
  have hAB : Nat.card ↥(s.fr.A ⊓ s.fr.B) = 16 := y7a_card_AB hH
  have hle : s.fr.A ⊔ s.fr.B ≤ s.fr.S := sup_le (s3_A_le_S s) (s3_B_le_S s)
  have hdvdA : Nat.card ↥s.fr.A ∣ Nat.card ↥(s.fr.A ⊔ s.fr.B) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvdS : Nat.card ↥(s.fr.A ⊔ s.fr.B) ∣ Nat.card ↥s.fr.S := Subgroup.card_dvd_of_le hle
  rw [hA] at hdvdA
  rw [hS] at hdvdS
  have hpos : 0 < Nat.card ↥(s.fr.A ⊔ s.fr.B) := Nat.card_pos
  have hle64 : Nat.card ↥(s.fr.A ⊔ s.fr.B) ≤ 64 := Nat.le_of_dvd (by norm_num) hdvdS
  have h64 : Nat.card ↥(s.fr.A ⊔ s.fr.B) = 64 := by
    obtain ⟨n, hn⟩ := hdvdA
    have hn2 : n = 1 ∨ n = 2 := by omega
    rcases hn2 with rfl | rfl
    · exfalso
      have hAeq : s.fr.A = s.fr.A ⊔ s.fr.B :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      have hBA : s.fr.B ≤ s.fr.A := hAeq ▸ le_sup_right
      have hBeq : s.fr.B = s.fr.A := Subgroup.eq_of_le_of_card_ge hBA (by omega)
      rw [hBeq, inf_idem] at hAB
      omega
    · omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem y7a_V1_le_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    V1 c.e ≤ V2 c.e := by
  intro v hv
  refine Subgroup.mem_inf.mpr ⟨y7a_V1_le_M3 c hv, ?_⟩
  have hC0 : v ∈ C0 c.e := (Subgroup.mem_inf.mp hv).1
  have hC4 : v ∈ C4 c.s := hF.2.2.2.2.1.2.1 hC0
  refine Subgroup.mem_inf.mpr ⟨hC4, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (y7a_M3_elemAbelian c hH).comm (y7a_V1_le_M3 c hw) (y7a_V1_le_M3 c hv)

theorem y7a_S_V1_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ x ∈ c.s.fr.S, ∀ v ∈ V1 c.e, x * v = v * x := by
  have h := c.y7acfg hH
  have hA : c.s.fr.A ≤ centralizer ((V1 c.e : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)).symm
  have hB : c.s.fr.B ≤ centralizer ((V1 c.e : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (y7a_B_V2_comm c hH hF h71 b hb v (y7a_V1_le_V2 c hH hF hv)).symm
  intro x hx v hv
  rw [y7a_S_eq_sup hH] at hx
  exact (Subgroup.mem_centralizer_iff.mp (sup_le hA hB hx) v hv).symm

end CFSG.OddStandard.HigherRank.YamadaG23
