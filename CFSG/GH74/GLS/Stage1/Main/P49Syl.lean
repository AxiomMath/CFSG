module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem sylow_G_of_std6 (h : Std6 G z S) : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htc, htz⟩ := h.thm2
  obtain ⟨-, -, -, ⟨SG, hSG⟩, -⟩ := h.classical.2 t ht htc htz
  have hSGC : (SG : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (((hSG g).2 (Subgroup.mem_zpowers g)).2.1 s hs).symm
  have hSGcard : Nat.card (SG : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    Sylow.card_eq_multiplicity SG
  have hSc := h.sylow.card_eq
  have hdvd : 2 ^ (Nat.card G).factorization 2 ∣ Nat.card (centralizer ({z} : Set G)) := by
    rw [← hSGcard]
    exact Subgroup.card_dvd_of_le hSGC
  have hCG : Nat.card (centralizer ({z} : Set G)) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hCne : Nat.card (centralizer ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hle1 : (Nat.card G).factorization 2 ≤ (Nat.card (centralizer ({z} : Set G))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hCne).1 hdvd
  have hle2 : (Nat.card (centralizer ({z} : Set G))).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd hCne hGne).2 hCG 2
  have heq : (Nat.card (centralizer ({z} : Set G))).factorization 2 = (Nat.card G).factorization 2 :=
    le_antisymm hle2 hle1
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [hSc, heq]
  simp

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
