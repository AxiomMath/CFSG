module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem card_supp_eq_two_of_mem_cycleFactorsFinset {σ c : Perm α} (h2 : σ * σ = 1)
    (hc : c ∈ σ.cycleFactorsFinset) : c.support.card = 2 := by
  have hmem : c.support.card ∈ σ.cycleType := by
    rw [cycleType_def]
    exact Multiset.mem_map_of_mem (Finset.card ∘ support) hc
  rw [cycleType_eq_replicate_two h2] at hmem
  exact Multiset.eq_of_mem_replicate hmem

open Equiv.Perm.OnCycleFactors in
theorem card_centralizer_inf_mul_card_cycleType {σ τ : Perm α} (h2 : σ * σ = 1)
    (hτ : τ ∈ σ.cycleFactorsFinset) :
    Nat.card (centralizer ({σ} : Set (Perm α)) ⊓ centralizer ({τ} : Set (Perm α)) :
        Subgroup (Perm α)) * Multiset.card σ.cycleType =
      Nat.card (centralizer ({σ} : Set (Perm α))) := by
  classical
  set c₀ : σ.cycleFactorsFinset := ⟨τ, hτ⟩ with hc₀
  have htrans : ∀ c : σ.cycleFactorsFinset, ∃ k : centralizer ({σ} : Set (Perm α)),
      k • c₀ = c := by
    intro c
    have hmem : (Equiv.swap c₀ c) ∈ (toPermHom σ).range := by
      rw [mem_range_toPermHom_iff]
      intro d
      rw [card_supp_eq_two_of_mem_cycleFactorsFinset h2 (Equiv.swap c₀ c d).2,
        card_supp_eq_two_of_mem_cycleFactorsFinset h2 d.2]
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    rw [← toPermHom_apply, hk, Equiv.swap_apply_left]
  have hpre : MulAction.IsPretransitive (centralizer ({σ} : Set (Perm α))) σ.cycleFactorsFinset :=
    ⟨fun c c' => by
      obtain ⟨k₁, hk₁⟩ := htrans c
      obtain ⟨k₂, hk₂⟩ := htrans c'
      exact ⟨k₂ * k₁⁻¹, by rw [mul_smul, ← hk₁, inv_smul_smul, hk₂]⟩⟩
  have hstab : MulAction.stabilizer (centralizer ({σ} : Set (Perm α))) c₀ =
      (centralizer ({τ} : Set (Perm α))).subgroupOf (centralizer ({σ} : Set (Perm α))) := by
    ext k
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff,
      ← Subtype.coe_inj, val_centralizer_smul]
    simp only [hc₀, InvMemClass.coe_inv]
    constructor
    · intro hk
      calc (k : Perm α) * τ = (k * τ * (k : Perm α)⁻¹) * k := by group
        _ = τ * k := by rw [hk]
    · intro hk
      calc (k : Perm α) * τ * (k : Perm α)⁻¹ = τ * k * (k : Perm α)⁻¹ := by rw [hk]
        _ = τ := by group
  have hidx := MulAction.index_stabilizer_of_transitive (centralizer ({σ} : Set (Perm α))) c₀
  have hcardX : Nat.card σ.cycleFactorsFinset = Multiset.card σ.cycleType := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, cycleType_def, Multiset.card_map]
    rfl
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (centralizer ({σ} : Set (Perm α))) c₀)
  rw [hidx, hcardX, hstab, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
      centralizer ({τ} : Set (Perm α)) ⊓ centralizer ({σ} : Set (Perm α)) ≤ _)).toEquiv,
    inf_comm] at h1
  exact h1

end Perm

end CFSG.OddStandard.AltStdSec
