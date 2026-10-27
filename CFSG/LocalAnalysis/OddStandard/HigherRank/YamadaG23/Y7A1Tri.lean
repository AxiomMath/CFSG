module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem y7a_triple_sum {C V AV X : Subgroup G} (hVC : V ≤ C) (hAVC : AV ≤ C)
    (hidx : ∀ x ∈ C, ∀ y ∈ C, x ∉ AV → y ∉ AV → x * y ∈ AV)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ V) (hsq : ∀ x ∈ C, x * x ∈ V)
    (hX : ∀ x ∈ X, x ∈ normalizer (C : Set G) ∧ x ∈ normalizer (V : Set G))
    (p : Fin 3 → G) (hp : ∀ i, p i ∈ C ∧ p i ∉ AV)
    (hne : ∀ i j, i ≠ j → (p i)⁻¹ * p j ∉ V)
    (hinv : ∀ x ∈ X, ∀ i, ∃ j, (p j)⁻¹ * (x * p i * x⁻¹) ∈ V) :
    ∃ s ∈ C, s ∉ AV ∧ (∀ x ∈ X, s⁻¹ * (x * s * x⁻¹) ∈ V) ∧ ∀ i, (p i)⁻¹ * s ∉ V := by
  have hVn : (V.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVC]
    intro h k hh hk
    have hc : ⁅k, h⁆ ∈ V := hcomm k hk h (hVC hh)
    have heq : k * h * k⁻¹ = ⁅k, h⁆ * h := by rw [commutatorElement_def]; group
    rw [heq]
    exact V.mul_mem hc hh
  haveI : (V.subgroupOf C).Normal := hVn
  let q : C →* C ⧸ (V.subgroupOf C) := QuotientGroup.mk' (V.subgroupOf C)
  haveI : IsMulCommutative (C ⧸ (V.subgroupOf C)) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    change ⁅(⊤ : Subgroup C), ⊤⁆ ≤ V.subgroupOf C
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using
      hcomm (g₁ : G) g₁.2 (g₂ : G) g₂.2
  let s : G := p 0 * p 1 * p 2
  have hsc : s ∈ C := by
    dsimp only [s]; exact C.mul_mem (C.mul_mem (hp 0).1 (hp 1).1) (hp 2).1
  have hsa : s ∉ AV := by
    intro hsAV
    have h01 : p 0 * p 1 ∈ AV :=
      hidx (p 0) (hp 0).1 (p 1) (hp 1).1 (hp 0).2 (hp 1).2
    have h2 : p 2 ∈ AV := by
      have hmem : (p 0 * p 1)⁻¹ * s ∈ AV := AV.mul_mem (AV.inv_mem h01) hsAV
      have heq : (p 0 * p 1)⁻¹ * s = p 2 := by dsimp only [s]; group
      rwa [heq] at hmem
    exact (hp 2).2 h2
  have hsc_split : (⟨s, hsc⟩ : C) =
      (⟨p 0, (hp 0).1⟩ : C) * ⟨p 1, (hp 1).1⟩ * ⟨p 2, (hp 2).1⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    dsimp only [s]
  refine ⟨s, hsc, hsa, ?_, ?_⟩
  · intro x hx
    have hxC : x ∈ normalizer (C : Set G) := (hX x hx).1
    have hxV : x ∈ normalizer (V : Set G) := (hX x hx).2
    have hxi : ∀ i, x * p i * x⁻¹ ∈ C := fun i =>
      (Subgroup.mem_normalizer_iff.mp hxC (p i)).mp (hp i).1
    have hxs : x * s * x⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp hxC s).mp hsc
    let σ : Fin 3 → Fin 3 := fun i => Classical.choose (hinv x hx i)
    have hσmem : ∀ i, (p (σ i))⁻¹ * (x * p i * x⁻¹) ∈ V :=
      fun i => Classical.choose_spec (hinv x hx i)
    have hqσ : ∀ i, q ⟨x * p i * x⁻¹, hxi i⟩ = q ⟨p (σ i), (hp (σ i)).1⟩ := by
      intro i
      have hmem : ((⟨p (σ i), (hp (σ i)).1⟩ : C)⁻¹ * ⟨x * p i * x⁻¹, hxi i⟩) ∈
          V.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hσmem i
      have h1 : q ((⟨p (σ i), (hp (σ i)).1⟩ : C)⁻¹ * ⟨x * p i * x⁻¹, hxi i⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      calc q ⟨x * p i * x⁻¹, hxi i⟩
          = q (⟨p (σ i), (hp (σ i)).1⟩ *
              ((⟨p (σ i), (hp (σ i)).1⟩ : C)⁻¹ * ⟨x * p i * x⁻¹, hxi i⟩)) := by
              rw [mul_inv_cancel_left]
        _ = q ⟨p (σ i), (hp (σ i)).1⟩ *
              q ((⟨p (σ i), (hp (σ i)).1⟩ : C)⁻¹ * ⟨x * p i * x⁻¹, hxi i⟩) := by
              rw [map_mul]
        _ = q ⟨p (σ i), (hp (σ i)).1⟩ := by rw [h1, mul_one]
    have hσinj : Function.Injective σ := by
      intro i i' hii
      by_contra hne'
      have hWi : (p (σ i))⁻¹ * (x * p i * x⁻¹) ∈ V := hσmem i
      have hWi' : (p (σ i'))⁻¹ * (x * p i' * x⁻¹) ∈ V := hσmem i'
      rw [← hii] at hWi'
      have hw : x * ((p i)⁻¹ * p i') * x⁻¹ ∈ V := by
        have h0 : (x * p i * x⁻¹)⁻¹ * (x * p i' * x⁻¹) ∈ V := by
          have h1 := V.mul_mem (V.inv_mem hWi) hWi'
          have heq : ((p (σ i))⁻¹ * (x * p i * x⁻¹))⁻¹ *
              ((p (σ i))⁻¹ * (x * p i' * x⁻¹)) =
              (x * p i * x⁻¹)⁻¹ * (x * p i' * x⁻¹) := by group
          rwa [heq] at h1
        have heq : (x * p i * x⁻¹)⁻¹ * (x * p i' * x⁻¹) =
            x * ((p i)⁻¹ * p i') * x⁻¹ := by group
        rwa [heq] at h0
      have hpip : (p i)⁻¹ * p i' ∈ V := by
        have hxinvV : x⁻¹ ∈ normalizer (V : Set G) :=
          (Subgroup.normalizer (V : Set G)).inv_mem hxV
        have hconj :=
          (Subgroup.mem_normalizer_iff.mp hxinvV (x * ((p i)⁻¹ * p i') * x⁻¹)).mp hw
        have heq : x⁻¹ * (x * ((p i)⁻¹ * p i') * x⁻¹) * (x⁻¹)⁻¹ =
            (p i)⁻¹ * p i' := by group
        rwa [heq] at hconj
      exact hne i i' hne' hpip
    have hσbij : Function.Bijective σ := hσinj.bijective_of_finite
    have hx_split : (⟨x * s * x⁻¹, hxs⟩ : C) =
        (⟨x * p 0 * x⁻¹, hxi 0⟩ : C) * ⟨x * p 1 * x⁻¹, hxi 1⟩ *
          ⟨x * p 2 * x⁻¹, hxi 2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      dsimp only [s]
      group
    have hqsc : q ⟨x * s * x⁻¹, hxs⟩ = q ⟨s, hsc⟩ := by
      have hperm : q ⟨p (σ 0), (hp (σ 0)).1⟩ * q ⟨p (σ 1), (hp (σ 1)).1⟩ *
          q ⟨p (σ 2), (hp (σ 2)).1⟩ =
          q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩ := by
        rw [← Fin.prod_univ_three (fun i => q ⟨p (σ i), (hp (σ i)).1⟩),
            ← Fin.prod_univ_three (fun i => q ⟨p i, (hp i).1⟩)]
        exact hσbij.prod_comp (fun i => q ⟨p i, (hp i).1⟩)
      calc q ⟨x * s * x⁻¹, hxs⟩
          = q ((⟨x * p 0 * x⁻¹, hxi 0⟩ : C) * ⟨x * p 1 * x⁻¹, hxi 1⟩ *
              ⟨x * p 2 * x⁻¹, hxi 2⟩) := by rw [hx_split]
        _ = q ⟨x * p 0 * x⁻¹, hxi 0⟩ * q ⟨x * p 1 * x⁻¹, hxi 1⟩ *
              q ⟨x * p 2 * x⁻¹, hxi 2⟩ := by rw [map_mul, map_mul]
        _ = q ⟨p (σ 0), (hp (σ 0)).1⟩ * q ⟨p (σ 1), (hp (σ 1)).1⟩ *
              q ⟨p (σ 2), (hp (σ 2)).1⟩ := by rw [hqσ 0, hqσ 1, hqσ 2]
        _ = q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩ := hperm
        _ = q ⟨s, hsc⟩ := by rw [hsc_split, map_mul, map_mul]
    have hmemN : ((⟨s, hsc⟩ : C)⁻¹ * ⟨x * s * x⁻¹, hxs⟩) ∈ V.subgroupOf C := by
      rw [← QuotientGroup.eq_one_iff]
      change q ((⟨s, hsc⟩ : C)⁻¹ * ⟨x * s * x⁻¹, hxs⟩) = 1
      rw [map_mul, map_inv, hqsc, inv_mul_cancel]
    have hN := hmemN
    rw [Subgroup.mem_subgroupOf] at hN
    exact hN
  · intro i hi
    have hsq_q : ∀ i, q ⟨p i, (hp i).1⟩ * q ⟨p i, (hp i).1⟩ = 1 := by
      intro i
      have hmemN : ((⟨p i, (hp i).1⟩ : C) * ⟨p i, (hp i).1⟩) ∈ V.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hsq (p i) (hp i).1
      have h1 : q ((⟨p i, (hp i).1⟩ : C) * ⟨p i, (hp i).1⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmemN
      rwa [map_mul] at h1
    have hqs : q ⟨s, hsc⟩ = q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ *
        q ⟨p 2, (hp 2).1⟩ := by
      rw [hsc_split, map_mul, map_mul]
    have hiq : (q ⟨p i, (hp i).1⟩)⁻¹ * q ⟨s, hsc⟩ = 1 := by
      have hmemN : ((⟨p i, (hp i).1⟩ : C)⁻¹ * ⟨s, hsc⟩) ∈ V.subgroupOf C := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hi
      have h1 : q ((⟨p i, (hp i).1⟩ : C)⁻¹ * ⟨s, hsc⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmemN
      rwa [map_mul, map_inv] at h1
    rw [hqs] at hiq
    have hmem_of_eq : ∀ {j k : Fin 3},
        q ⟨p j, (hp j).1⟩ = q ⟨p k, (hp k).1⟩ → (p j)⁻¹ * p k ∈ V := by
      intro j k hjk
      have hmemN : ((⟨p j, (hp j).1⟩ : C)⁻¹ * ⟨p k, (hp k).1⟩) ∈ V.subgroupOf C := by
        rw [← QuotientGroup.eq_one_iff]
        change q ((⟨p j, (hp j).1⟩ : C)⁻¹ * ⟨p k, (hp k).1⟩) = 1
        rw [map_mul, map_inv, hjk, inv_mul_cancel]
      have hN := hmemN
      rw [Subgroup.mem_subgroupOf] at hN
      exact hN
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi_cases with rfl | rfl | rfl
    ·
      have h12 : q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩ = 1 := by
        have h := hiq
        rw [show (q ⟨p 0, (hp 0).1⟩)⁻¹ *
              (q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩) =
              q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩ by group] at h
        exact h
      have h22 := hsq_q 2
      have heq : q ⟨p 1, (hp 1).1⟩ = q ⟨p 2, (hp 2).1⟩ := by
        calc q ⟨p 1, (hp 1).1⟩
            = q ⟨p 1, (hp 1).1⟩ *
                (q ⟨p 2, (hp 2).1⟩ * q ⟨p 2, (hp 2).1⟩) := by rw [h22, mul_one]
          _ = (q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩) *
                q ⟨p 2, (hp 2).1⟩ := by rw [mul_assoc]
          _ = q ⟨p 2, (hp 2).1⟩ := by rw [h12, one_mul]
      exact hne 1 2 (by decide) (hmem_of_eq heq)
    ·
      have h02 : q ⟨p 0, (hp 0).1⟩ * q ⟨p 2, (hp 2).1⟩ = 1 := by
        have h := hiq
        rw [show (q ⟨p 1, (hp 1).1⟩)⁻¹ *
              (q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩) =
              q ⟨p 0, (hp 0).1⟩ * q ⟨p 2, (hp 2).1⟩ by
                rw [mul_comm (q ⟨p 0, (hp 0).1⟩) (q ⟨p 1, (hp 1).1⟩)]; group] at h
        exact h
      have h22 := hsq_q 2
      have heq : q ⟨p 0, (hp 0).1⟩ = q ⟨p 2, (hp 2).1⟩ := by
        calc q ⟨p 0, (hp 0).1⟩
            = q ⟨p 0, (hp 0).1⟩ *
                (q ⟨p 2, (hp 2).1⟩ * q ⟨p 2, (hp 2).1⟩) := by rw [h22, mul_one]
          _ = (q ⟨p 0, (hp 0).1⟩ * q ⟨p 2, (hp 2).1⟩) * q ⟨p 2, (hp 2).1⟩ := by
                rw [mul_assoc]
          _ = q ⟨p 2, (hp 2).1⟩ := by rw [h02, one_mul]
      exact hne 0 2 (by decide) (hmem_of_eq heq)
    ·
      have h01 : q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ = 1 := by
        have h := hiq
        rw [show (q ⟨p 2, (hp 2).1⟩)⁻¹ *
              (q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ * q ⟨p 2, (hp 2).1⟩) =
              q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩ by
                rw [mul_comm (q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩)
                  (q ⟨p 2, (hp 2).1⟩)]; group] at h
        exact h
      have h11 := hsq_q 1
      have heq : q ⟨p 0, (hp 0).1⟩ = q ⟨p 1, (hp 1).1⟩ := by
        calc q ⟨p 0, (hp 0).1⟩
            = q ⟨p 0, (hp 0).1⟩ *
                (q ⟨p 1, (hp 1).1⟩ * q ⟨p 1, (hp 1).1⟩) := by rw [h11, mul_one]
          _ = (q ⟨p 0, (hp 0).1⟩ * q ⟨p 1, (hp 1).1⟩) * q ⟨p 1, (hp 1).1⟩ := by
                rw [mul_assoc]
          _ = q ⟨p 1, (hp 1).1⟩ := by rw [h01, one_mul]
      exact hne 0 1 (by decide) (hmem_of_eq heq)

end CFSG.OddStandard.HigherRank.YamadaG23
