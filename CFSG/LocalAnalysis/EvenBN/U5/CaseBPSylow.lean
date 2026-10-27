module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

theorem sec52_sylow_le_normalizer_of_commute {A B : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : B ≤ normalizer (A : Set G) := by
  refine Subgroup.le_normalizer_iff.2 ?_
  intro b hb a ha
  have e : b * a = a * b := (hc a ha b hb).symm
  rw [e, mul_inv_cancel_right]
  exact ha

theorem sec52_sylow_centerIn_sup {A B : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    CFSG.centerIn (A ⊔ B) = CFSG.centerIn A ⊔ CFSG.centerIn B := by
  apply le_antisymm
  · intro z hz
    unfold CFSG.centerIn at hz
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hz
    obtain ⟨hzS, hzC⟩ := hz
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hzS
    have hA : a ∈ CFSG.centerIn A := by
      unfold CFSG.centerIn
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨ha, fun x hx => ?_⟩
      have hxA : x ∈ A := hx
      have h1 : x * (a * b) = a * b * x := hzC x (Subgroup.mem_sup_left (T := B) hxA)
      have h2 : x * b = b * x := hc x hxA b hb
      have h3 : x * a * b = a * x * b := by
        calc x * a * b = x * (a * b) := by rw [mul_assoc]
          _ = a * b * x := h1
          _ = a * (b * x) := by rw [mul_assoc]
          _ = a * (x * b) := by rw [h2]
          _ = a * x * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hB' : b ∈ CFSG.centerIn B := by
      unfold CFSG.centerIn
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      refine ⟨hb, fun y hy => ?_⟩
      have hyB : y ∈ B := hy
      have h1 : y * (a * b) = a * b * y := hzC y (Subgroup.mem_sup_right (S := A) hyB)
      have h2 : a * y = y * a := hc a ha y hyB
      have h3 : a * (y * b) = a * (b * y) := by
        calc a * (y * b) = a * y * b := by rw [mul_assoc]
          _ = y * a * b := by rw [h2]
          _ = y * (a * b) := by rw [mul_assoc]
          _ = a * b * y := h1
          _ = a * (b * y) := by rw [mul_assoc]
      exact mul_left_cancel h3
    exact Subgroup.mul_mem_sup hA hB'
  · refine sup_le ?_ ?_
    · intro x hx
      unfold CFSG.centerIn at hx ⊢
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      obtain ⟨hxA, hxC⟩ := hx
      refine ⟨Subgroup.mem_sup_left (T := B) hxA, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy
      calc a * b * x = a * (b * x) := by rw [mul_assoc]
        _ = a * (x * b) := by rw [← hc x hxA b hb]
        _ = a * x * b := by rw [mul_assoc]
        _ = x * a * b := by rw [hxC a ha]
        _ = x * (a * b) := by rw [mul_assoc]
    · intro x hx
      unfold CFSG.centerIn at hx ⊢
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      obtain ⟨hxB, hxC⟩ := hx
      refine ⟨Subgroup.mem_sup_right (S := A) hxB, fun y hy => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy
      calc a * b * x = a * (b * x) := by rw [mul_assoc]
        _ = a * (x * b) := by rw [hxC b hb]
        _ = a * x * b := by rw [mul_assoc]
        _ = x * a * b := by rw [hc a ha x hxB]
        _ = x * (a * b) := by rw [mul_assoc]

theorem sec52_sylow_Qc_le_Kc (c : d.CaseBData) : c.Qc ≤ c.Kc :=
  fun _ hx => (Subgroup.mem_inf.1 hx).2

theorem sec52_sylow_Qt_le_Kt (c : d.CaseBData) : c.Qt ≤ c.Kt :=
  Subgroup.map_mono (sec52_sylow_Qc_le_Kc c)


theorem sec52_sylow_comm_K (hB : d.CaseBHyp) (c : d.CaseBData) :
    ∀ x ∈ c.Kc, ∀ y ∈ c.Kt, x * y = y * x := fun x hx y hy =>
  Subgroup.mem_centralizer_iff.1 (c.Kt_le_centralizer_Kc hB hy) x hx

theorem sec52_sylow_comm (hB : d.CaseBHyp) (c : d.CaseBData) :
    ∀ x ∈ c.Qc, ∀ y ∈ c.Qt, x * y = y * x := fun x hx y hy =>
  sec52_sylow_comm_K hB c x (sec52_sylow_Qc_le_Kc c hx) y (sec52_sylow_Qt_le_Kt c hy)

theorem sec52_sylow_isSylowOf_Qc (hB : d.CaseBHyp) (c : d.CaseBData) :
    IsSylowOf 2 c.Qc c.Kc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (c.isSylowOf_S_L₁ hB).inf_of_le_normalizer c.Kc_le_L₁ c.L₁_le_normalizer_Kc

theorem sec52_sylow_isSylowOf_S_inf_Kt (hB : d.CaseBHyp) (c : d.CaseBData) :
    IsSylowOf 2 (c.S ⊓ c.Kt) c.Kt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (c.isSylowOf_S_L₁ hB).inf_of_le_normalizer (c.Kt_le_L₁ hB) (c.L₁_le_normalizer_Kt hB)

theorem sec52_sylow_Qt_eq (hB : d.CaseBHyp) (c : d.CaseBData) : c.Qt = c.S ⊓ c.Kt := by
  unfold CaseBData.Qt CaseBData.Qc CaseBData.Kt
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective,
    map_conj_eq_of_mem_normalizer (c.t_mem_normalizer_S hB)]

theorem sec52_sylow_Qt_le_S (hB : d.CaseBHyp) (c : d.CaseBData) : c.Qt ≤ c.S := by
  rw [sec52_sylow_Qt_eq hB c]
  exact inf_le_left

theorem sec52_sylow_S_eq (hB : d.CaseBHyp) (c : d.CaseBData) : c.S = c.Qc ⊔ c.Qt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := sec52_sylow_comm hB c
  have hQK := sec52_sylow_Qc_le_Kc c
  have hQtK := sec52_sylow_Qt_le_Kt c
  have hKKt : c.Kt ≤ normalizer (c.Kc : Set G) :=
    sec52_sylow_le_normalizer_of_commute (sec52_sylow_comm_K hB c)
  have hL : Nat.card d.L₁ = Nat.card c.Kc * Nat.card c.Kt := by
    have h := Common.card_sup_mul_card_inf_eq hKKt
    rwa [c.Kc_sup_Kt hB, c.Kc_inf_Kt hB, Subgroup.card_bot, mul_one] at h
  have hS := (c.isSylowOf_S_L₁ hB).card_eq
  have hQ := (sec52_sylow_isSylowOf_Qc hB c).card_eq
  have hQt : Nat.card c.Qt = 2 ^ (Nat.card c.Kt).factorization 2 := by
    rw [sec52_sylow_Qt_eq hB c]
    exact (sec52_sylow_isSylowOf_S_inf_Kt hB c).card_eq
  have hcard : Nat.card c.S = Nat.card c.Qc * Nat.card c.Qt := by
    rw [hS, hQ, hQt, hL, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, pow_add]
  have hinf : c.Qc ⊓ c.Qt = ⊥ := by
    rw [eq_bot_iff, ← c.Kc_inf_Kt hB]
    exact inf_le_inf hQK hQtK
  have hsup : Nat.card (c.Qc ⊔ c.Qt : Subgroup G) = Nat.card c.S := by
    have h := Common.card_sup_mul_card_inf_eq (A := c.Qc) (B := c.Qt)
      (sec52_sylow_le_normalizer_of_commute hc)
    rw [hinf, Subgroup.card_bot, mul_one] at h
    rw [h, hcard]
  exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (sec52_sylow_Qt_le_S hB c))
    hsup.ge).symm

theorem sec52_sylow_map_δ (hB : d.CaseBHyp) (c : d.CaseBData) :
    (c.Qc.subgroupOf c.Kc).map (c.δ hB) = d.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := sec52_sylow_S_eq hB c
  have hc := sec52_sylow_comm hB c
  have hPle : d.P ≤ (c.Qc.subgroupOf c.Kc).map (c.δ hB) := by
    intro p hp
    have hpS : p ∈ c.Qc ⊔ c.Qt := hS ▸ c.P_le_S hp
    have hpR : p ∈ (c.δ hB).range := by
      rw [c.range_δ hB]
      exact Subgroup.mem_inf.2 ⟨c.S_le_L₁ hB (c.P_le_S hp),
        hB.hyp.L_le_centralizer (d.P_le_L hp)⟩
    obtain ⟨x, rfl⟩ := hpR
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hc hpS
    have hxa : (x : G) = a := (eq_of_mul_eq_mul_of_inf_eq_bot (c.Kc_inf_Kt hB) x.2
      (sec52_sylow_Qc_le_Kc c ha) (c.conj_mem_Kt hB x.2) (sec52_sylow_Qt_le_Kt c hb)
      ((c.δ_apply hB x).symm.trans hab)).1
    refine Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    rw [hxa]
    exact ha
  have hle : (c.Qc.subgroupOf c.Kc).map (c.δ hB) ≤ d.L := by
    refine (Subgroup.map_le_range _ _).trans ?_
    rw [c.range_δ hB, hB.L₁_inf_centralizer_t]
    exact sup_le (d.pull_le_L _) (d.pull_le_L _)
  have hpg : IsPGroup 2 ((c.Qc.subgroupOf c.Kc).map (c.δ hB)) :=
    (sec52_sylow_isSylowOf_Qc hB c).isPGroup.comap_subtype.map (c.δ hB)
  exact d.isSylowOf_P.eq_of_le hPle hle hpg

theorem sec52_sylow_V_eq (hB : d.CaseBHyp) (c : d.CaseBData) :
    d.V = CFSG.centerIn c.Qc ⊔ CFSG.centerIn c.Qt := by
  rw [← (hB.sec3_9_two c.S c.S_syl c.P_le_S).1, sec52_sylow_S_eq hB c]
  exact sec52_sylow_centerIn_sup (sec52_sylow_comm hB c)

theorem sec52_sylow (hB : d.CaseBHyp) (c : d.CaseBData) : CaseBData.Sec52Sylow hB c :=
  ⟨sec52_sylow_S_eq hB c, sec52_sylow_map_δ hB c, sec52_sylow_V_eq hB c⟩

theorem sec52_card_Qc (hB : d.CaseBHyp) (c : d.CaseBData) :
    Nat.card c.Qc = (2 ^ f) ^ 10 := by
  have e1 : Nat.card c.Qc = Nat.card (c.Qc.subgroupOf c.Kc) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sec52_sylow_Qc_le_Kc c)).toEquiv).symm
  have e2 : Nat.card ((c.Qc.subgroupOf c.Kc).map (c.δ hB)) = Nat.card (c.Qc.subgroupOf c.Kc) :=
    Subgroup.card_map_of_injective (c.injective_δ hB)
  rw [e1, ← e2, (sec52_sylow hB c).map_δ, d.card_P]

end CaseBData

end Data

namespace CaseBParts

theorem sec52Sylow : Sec52SylowStatement :=
  fun _ _ _ _ _ _ _ _ hB c => Data.CaseBData.sec52_sylow hB c

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
