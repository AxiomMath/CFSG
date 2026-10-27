module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54P
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Aut1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y7b_card_E (hH : F33Hyp s e) : Nat.card ↥s.fr.E = 8 := by
  rw [(y56_E_isE3 hH).2]
  norm_num

theorem y7b_card_F (hH : F33Hyp s e) : Nat.card ↥s.fr.F = 8 := by
  rw [(y54_F_isE3 hH).2]
  norm_num

theorem y7b_card_V (hH : F33Hyp s e) : Nat.card ↥(cen s.fr.B) = 4 := by
  rw [(f3_V_isE2 hH).2]
  norm_num

theorem y7b_E_inf_F (hH : F33Hyp s e) : s.fr.E ⊓ s.fr.F = cen s.fr.B :=
  hH.hLF.fact14.2.2.2.1.2.2.2

theorem y7b_EF_eq (hH : F33Hyp s e) : s.fr.E ⊔ s.fr.F = s.fr.A ⊓ s.fr.B :=
  hH.hLF.fact14.2.2.2.1.1

theorem y7b_card_AB (hH : F33Hyp s e) : Nat.card ↥(s.fr.A ⊓ s.fr.B) = 16 := by
  change Nat.card ↥((frameWith s 1).A ⊓ (frameWith s 1).B) = 16
  obtain ⟨eD⟩ := hH.hLF.fact14.2.2.2.1.2.1.2.2.2
  rw [Nat.card_congr eD.toEquiv, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, DihedralGroup.card]

theorem y7b_mem_EF (hH : F33Hyp s e) {x : G} :
    x ∈ s.fr.A ⊓ s.fr.B ↔ ∃ u ∈ s.fr.E, ∃ v ∈ s.fr.F, x = u * v := by
  have hEF := y7b_EF_eq hH
  have hEAB : s.fr.E ≤ s.fr.A ⊓ s.fr.B := hEF ▸ le_sup_left
  have hFAB : s.fr.F ≤ s.fr.A ⊓ s.fr.B := hEF ▸ le_sup_right
  have hrel : s.fr.F.relIndex (s.fr.A ⊓ s.fr.B) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := s.fr.F) (K := s.fr.A ⊓ s.fr.B)
    rw [inf_of_le_left hFAB, y7b_card_F hH, y7b_card_AB hH] at h
    omega
  have hnorm : (s.fr.F.subgroupOf (s.fr.A ⊓ s.fr.B)).Normal :=
    Subgroup.normal_of_index_eq_two (by simpa only [Subgroup.relIndex] using hrel)
  have hNAB : s.fr.A ⊓ s.fr.B ≤ normalizer (s.fr.F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFAB).mp hnorm
  have hENF : s.fr.E ≤ normalizer (s.fr.F : Set G) := hEAB.trans hNAB
  rw [← hEF]
  exact mem_sup_iff_exists_mul_of_le_normalizer hENF

theorem y7b_mem_S (hH : F33Hyp s e) {x : G} :
    x ∈ s.fr.S ↔ ∃ a ∈ s.fr.A, ∃ b ∈ s.fr.B, x = a * b := by
  have hANB : s.fr.A ≤ normalizer (s.fr.B : Set G) :=
    (s3_A_le_S s).trans fun x hx => f3_B_char hH x (Subgroup.le_normalizer hx)
  have hcard := card_sup_mul_card_inf_of_le_normalizer (H := s.fr.A) (K := s.fr.B) hANB
  rw [y7b_card_AB hH, y56_card_A hH, y54_card_B hH] at hcard
  have h64 : Nat.card ↥(s.fr.A ⊔ s.fr.B) = 64 := by
    norm_num at hcard
    omega
  have hsup : s.fr.A ⊔ s.fr.B = s.fr.S := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le (s3_A_le_S s) (s3_B_le_S s)) ?_
    simp [h64, y54_card_S hH]
  rw [← hsup]
  exact mem_sup_iff_exists_mul_of_le_normalizer hANB

theorem y7b_S_le_normalizer_B (hH : F33Hyp s e) : s.fr.S ≤ normalizer (s.fr.B : Set G) :=
  fun x hx => f3_B_char hH x (Subgroup.le_normalizer hx)

theorem y7b_B_cent (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.S, (∀ v ∈ cen s.fr.B, x * v = v * x) → x ∈ s.fr.B := by
  intro x hxS hcomm
  have hw : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := (y56_v0 hH).1
  have hxw : x * (s.fr.b₁ * s.fr.b₂) = (s.fr.b₁ * s.fr.b₂) * x := hcomm _ hw
  refine Subgroup.mem_inf.mpr ⟨hxS, ?_⟩
  show x ∈ Subgroup.centralizer (Subgroup.closure {s.fr.b₁ * s.fr.b₂} : Set G)
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_singleton_iff]
  exact hxw

end CFSG.OddStandard.HigherRank.YamadaG23
