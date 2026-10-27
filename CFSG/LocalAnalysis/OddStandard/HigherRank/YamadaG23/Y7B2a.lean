module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1d

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M6_comm_sq (c : Ctx7 G L) (hb : B5Std c) :
    (∀ m ∈ M6 c.e, ∀ n ∈ M6 c.e, ⁅m, n⁆ ∈ V1 c.e) ∧ ∀ m ∈ M6 c.e, m ^ 2 ∈ V1 c.e := by
  refine ⟨?_, ?_⟩
  · intro m hm n hn
    have h : ⁅m, n⁆ ∈ ⁅M6 c.e, M6 c.e⁆ := Subgroup.commutator_mem_commutator hm hn
    rwa [hb.h72.2.2.1.1] at h
  · intro m hm
    obtain ⟨hN, hel⟩ := hb.h72.2.2.1.2
    let V' : Subgroup ↥(M6 c.e) := (V1 c.e).subgroupOf (M6 c.e)
    haveI : V'.Normal := hN
    have hsq : ((QuotientGroup.mk' V' ⟨m, hm⟩ : ↥(M6 c.e) ⧸ V')) ^ 2 = 1 :=
      hel.2 _ (Subgroup.mem_top _)
    have hmem : ((⟨m, hm⟩ : ↥(M6 c.e)) : G) ^ 2 ∈ V1 c.e := by
      have hmem' : (⟨m, hm⟩ : ↥(M6 c.e)) ^ 2 ∈ V' := by
        refine (QuotientGroup.eq_one_iff _).mp ?_
        change (QuotientGroup.mk' V' ((⟨m, hm⟩ : ↥(M6 c.e)) ^ 2)) = 1
        rw [map_pow]
        exact hsq
      simpa using Subgroup.mem_subgroupOf.mp hmem'
    simpa using hmem

theorem y7b_norm_of_V1_le (c : Ctx7 G L) (hb : B5Std c) {N : Subgroup G} (hN : V1 c.e ≤ N)
    (hNM : N ≤ M6 c.e) : ∀ m ∈ M6 c.e, ∀ x ∈ N, m * x * m⁻¹ ∈ N := by
  intro m hm x hx
  have hc : ⁅m, x⁆ ∈ V1 c.e := (y7b_M6_comm_sq c hb).1 m hm x (hNM hx)
  have he : m * x * m⁻¹ = ⁅m, x⁆ * x := by rw [commutatorElement_def]; group
  rw [he]
  exact N.mul_mem (hN hc) hx

theorem y7b_M5_le_M6 (c : Ctx7 G L) (hb : B5Std c) : M5 c.e ≤ M6 c.e := by
  unfold M5
  exact sup_le hb.h71.2.2.2.1 hb.h71.2.2.2.2

theorem y7b_V1_le_M5 (c : Ctx7 G L) (hb : B5Std c) : V1 c.e ≤ M5 c.e := by
  intro x hx
  change x ∈ M3 c.s ⊔ M4 c.e
  exact Subgroup.mem_sup_left
    ((Subgroup.mem_inf.mp (show x ∈ C0 c.e ⊓ M3 c.s from hx)).2)

theorem y7b_M6_norm_M3 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M6 c.e, ∀ x ∈ M3 c.s, m * x * m⁻¹ ∈ M3 c.s := by
  exact y7b_norm_of_V1_le c hb (N := M3 c.s) (show V1 c.e ≤ M3 c.s from inf_le_right)
    hb.h71.2.2.2.1

theorem y7b_M6_norm_M4 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M6 c.e, ∀ x ∈ M4 c.e, m * x * m⁻¹ ∈ M4 c.e := by
  exact y7b_norm_of_V1_le c hb (N := M4 c.e) (show V1 c.e ≤ M4 c.e from y7b_V1_le_M4 c hb)
    hb.h71.2.2.2.2

theorem y7b_M6_norm_V2 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M6 c.e, ∀ x ∈ V2 c.e, m * x * m⁻¹ ∈ V2 c.e := by
  refine y7b_norm_of_V1_le c hb (N := V2 c.e) (show V1 c.e ≤ V2 c.e from y7b_V1_le_V2 c hb) ?_
  intro x hx
  exact hb.h71.2.2.2.1
    ((Subgroup.mem_inf.mp (show x ∈ M3 c.s ⊓ M4 c.e from hx)).1)

theorem y7b_M6_norm_M5 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M6 c.e, ∀ x ∈ M5 c.e, m * x * m⁻¹ ∈ M5 c.e := by
  exact y7b_norm_of_V1_le c hb (N := M5 c.e) (show V1 c.e ≤ M5 c.e from y7b_V1_le_M5 c hb)
    (show M5 c.e ≤ M6 c.e from y7b_M5_le_M6 c hb)

theorem y7b_M5_comm_sq (c : Ctx7 G L) (hb : B5Std c) :
    (∀ m ∈ M5 c.e, ∀ n ∈ M5 c.e, ⁅m, n⁆ ∈ V1 c.e) ∧ ∀ m ∈ M5 c.e, m ^ 2 ∈ V1 c.e := by
  have h := y7b_M6_comm_sq c hb
  exact ⟨fun m hm n hn => h.1 m (y7b_M5_le_M6 c hb hm) n (y7b_M5_le_M6 c hb hn),
    fun m hm => h.2 m (y7b_M5_le_M6 c hb hm)⟩

theorem y7b_M5_mem (c : Ctx7 G L) (hb : B5Std c) {x : G} :
    x ∈ M5 c.e ↔ ∃ a ∈ M3 c.s, ∃ b ∈ M4 c.e, x = a * b := by
  have hM3norm : M3 c.s ≤ normalizer (M4 c.e : Set G) := by
    intro m hm
    exact Subgroup.mem_normalizer_fintype fun n hn =>
      y7b_M6_norm_M4 c hb m (hb.h71.2.2.2.1 hm) n hn
  change x ∈ M3 c.s ⊔ M4 c.e ↔ ∃ a ∈ M3 c.s, ∃ b ∈ M4 c.e, x = a * b
  exact mem_sup_iff_exists_mul_of_le_normalizer hM3norm

theorem y7b_card_M5 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(M5 c.e) = 2 ^ 8 := by
  have hM3norm : M3 c.s ≤ normalizer (M4 c.e : Set G) := by
    intro m hm
    exact Subgroup.mem_normalizer_fintype fun n hn =>
      y7b_M6_norm_M4 c hb m (hb.h71.2.2.2.1 hm) n hn
  have h2 : Nat.card ↥(V2 c.e) = 2 ^ 4 := hb.h72.1.2.2.2.1
  have h3 : Nat.card ↥(M3 c.s) = 2 ^ 6 := y7b_card_M3 c hb
  have h4 : Nat.card ↥(M4 c.e) = 2 ^ 6 := y7b_card_M4 c hb
  have hcard : Nat.card ↥(M5 c.e) * Nat.card ↥(V2 c.e) = 2 ^ 6 * 2 ^ 6 := by
    have h := card_sup_mul_card_inf_of_le_normalizer (H := M3 c.s) (K := M4 c.e) hM3norm
    rw [h3, h4] at h
    simpa [M5, V2] using h
  rw [h2] at hcard
  norm_num at hcard ⊢
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
