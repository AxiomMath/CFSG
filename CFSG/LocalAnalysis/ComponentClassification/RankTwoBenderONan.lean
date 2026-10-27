module

public import CFSG.Goldschmidt.Steps.GoldTypeBender
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {X : Type} [Group X] [Finite X]

theorem bender_sylow_facts (hX : fusionIsBenderGroup X) (U : Sylow 2 X) :
    fusionStronglyEmbedded (normalizer ((U : Subgroup X) : Set X)) ∧
      Nat.card (Sylow 2 X) = Nat.card (U : Subgroup X) + 1 ∧
      4 ≤ Nat.card (U : Subgroup X) := by
  obtain ⟨q, k, hq4, hB⟩ := (BenderExt.benderData_of_isBenderGroup hX).borel
  obtain ⟨hSE, -, hZcard, -⟩ := benderBorel_sylowCenter hB U
  refine ⟨hSE, Goldschmidt.GoldType.card_sylow_of_bender hX U, ?_⟩
  calc 4 ≤ q := hq4
    _ = Nat.card (sylowCenter (U : Subgroup X)) := hZcard.symm
    _ ≤ Nat.card (U : Subgroup X) := card_le_of_le (sylowCenter_le _)

theorem isSimpleGroup_of_bender (hX : fusionIsBenderGroup X) : IsSimpleGroup X :=
  (BenderExt.benderData_of_isBenderGroup hX).simple

theorem eq_of_mem_of_mem (hX : fusionIsBenderGroup X) {S U : Sylow 2 X} {x : X} (hx : x ≠ 1)
    (hxS : x ∈ (S : Subgroup X)) (hxU : x ∈ (U : Subgroup X)) : S = U := by
  by_contra hne
  exact hx (Omega.eq_one_of_mem_of_mem (bender_sylow_facts hX U).1 hne hxU hxS)

theorem mem_centralizer_of_involution (hX : fusionIsBenderGroup X) (U : Sylow 2 X) {x : X}
    (hxU : x ∈ (U : Subgroup X)) (hx : x ^ 2 = 1) :
    x ∈ centralizer ((U : Subgroup X) : Set X) := by
  obtain ⟨q, k, hq4, hB⟩ := (BenderExt.benderData_of_isBenderGroup hX).borel
  exact Asc76X.mem_centralizer_of_fusionBenderBorel hB (by omega) U hxU hx

theorem centralizer_le_normalizer_of_mem (hX : fusionIsBenderGroup X) (U : Sylow 2 X) {x : X}
    (hxU : x ∈ (U : Subgroup X)) (hx : x ≠ 1) :
    centralizer ({x} : Set X) ≤ normalizer ((U : Subgroup X) : Set X) := by
  intro c hc
  refine Sylow.smul_eq_iff_mem_normalizer.mp (eq_of_mem_of_mem hX hx ?_ hxU)
  rw [Omega.mem_conj_smul_iff]
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
  rw [show c⁻¹ * x * c = x by rw [mul_assoc, ← hcx, inv_mul_cancel_left]]
  exact hxU

theorem le_normalizer_or_eq_top (hX : fusionIsBenderGroup X) (U : Sylow 2 X) {H : Subgroup X}
    (hUH : (U : Subgroup X) ≤ H) : H ≤ normalizer ((U : Subgroup X) : Set X) ∨ H = ⊤ := by
  classical
  by_cases hle : H ≤ normalizer ((U : Subgroup X) : Set X)
  · exact Or.inl hle
  right
  obtain ⟨hSE, hcard, hU4⟩ := bender_sylow_facts hX U
  obtain ⟨h, hhH, hhN⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hne : h • U ≠ U := fun e => hhN (Sylow.smul_eq_iff_mem_normalizer.mp e)
  have hall : ∀ S : Sylow 2 X, (S : Subgroup X) ≤ H := by
    intro S
    by_cases hSU : S = U
    · rw [hSU]
      exact hUH
    obtain ⟨r, hr, hrS⟩ := Omega.exists_smul_eq hSE hcard hne hSU
    intro x hx
    rw [← hrS, ← mul_smul, Omega.mem_conj_smul_iff] at hx
    have hrh : r * h ∈ H := H.mul_mem (hUH hr) hhH
    have := H.mul_mem (H.mul_mem hrh (hUH hx)) (H.inv_mem hrh)
    rwa [show r * h * ((r * h)⁻¹ * x * (r * h)) * (r * h)⁻¹ = x by group] at this
  have hncl : normalClosure ((U : Subgroup X) : Set X) ≤ H := by
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    refine hall (c • U) ?_
    rw [Omega.mem_conj_smul_iff, show c⁻¹ * (c * a * c⁻¹) * c = a by group]
    exact ha
  have : IsSimpleGroup X := isSimpleGroup_of_bender hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure ((U : Subgroup X) : Set X)) with
    hbot | htop
  · exfalso
    have hUbot : (U : Subgroup X) = ⊥ :=
      le_bot_iff.mp fun x hx => hbot ▸ subset_normalClosure hx
    rw [hUbot, card_bot] at hU4
    omega
  · exact eq_top_iff.mpr (htop ▸ hncl)

end CFSG.ComponentClassification.RankTwoBender
