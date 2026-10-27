module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaSiegPerfect
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def SpTwoLagDerivedClosureAt (N j : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (H : Type) [Group H] (Φ₁ Φ₂ : StatedSp N K →* H), Function.Injective Φ₁ →
      Function.Injective Φ₂ → Φ₁ (spARep N j) = Φ₂ (spARep N j) →
      (⁅centralizer ({spARep N j} : Set (StatedSp N K)),
          centralizer ({spARep N j} : Set (StatedSp N K))⁆).map Φ₁ =
        (⁅centralizer ({spARep N j} : Set (StatedSp N K)),
          centralizer ({spARep N j} : Set (StatedSp N K))⁆).map Φ₂ →
      ∃ c d : StatedSp N K,
        (∃ y ∈ ⁅centralizer ({spARep N j} : Set (StatedSp N K)),
            centralizer ({spARep N j} : Set (StatedSp N K))⁆,
          c * y * c⁻¹ ∉ ⁅centralizer ({spARep N j} : Set (StatedSp N K)),
            centralizer ({spARep N j} : Set (StatedSp N K))⁆) ∧
        Φ₁ (spARep N j) * Φ₂ (c * spARep N j * c⁻¹) = Φ₁ (d * spARep N 1 * d⁻¹)

theorem spTwoLagDerivedClosureAt_of_closure (h : SpTwoLagClosureInput) {N j : ℕ} (hj : 3 ≤ j)
    (hjN : 2 * j = N) : SpTwoLagDerivedClosureAt N j := by
  intro K _ _ _ hK H _ Φ₁ Φ₂ h₁ h₂ ha hC
  have hP := spTwoLagPerfectInput_holds N j K hK hj hjN
  rw [hP] at hC
  simp only [hP]
  exact h N j K hK hj hjN H Φ₁ Φ₂ h₁ h₂ ha hC

section Commutator

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commutator_le_commutator_inf_centralizer_two (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) {N : ℕ} (hN : 3 ≤ N) (e : L ≃* StatedSp N K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {x : G} (htx : t * x = x * t) {P : Subgroup G} (hPt : P ≤ centralizer ({t} : Set G))
    (hPx : P ≤ centralizer ({x} : Set G)) :
    ⁅P, P⁆ ≤ ⁅L ⊓ centralizer ({x} : Set G), L ⊓ centralizer ({x} : Set G)⁆ := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hM : ∀ r ∈ P, ∃ r' ∈ L ⊓ centralizer ({x} : Set G), r = r' ∨ r = t * r' := by
    intro r hr
    have hrx : r * x = x * r := mem_centralizer_singleton_iff.1 (hPx hr)
    rcases mem_or_mul_mem_of_mem_centralizer_two hset hK hN e ht hKt (hPt hr) with h | h
    · exact ⟨r, ⟨h, mem_centralizer_singleton_iff.2 hrx⟩, Or.inl rfl⟩
    · refine ⟨t * r, ⟨h, mem_centralizer_singleton_iff.2 ?_⟩, Or.inr ?_⟩
      · calc t * r * x = t * (x * r) := by rw [mul_assoc, hrx]
          _ = (t * x) * r := by group
          _ = (x * t) * r := by rw [htx]
          _ = x * (t * r) := by group
      · rw [← mul_assoc, htt, one_mul]
  rw [Subgroup.commutator_le]
  intro p hp q hq
  obtain ⟨p', hp', hpp'⟩ := hM p hp
  obtain ⟨q', hq', hqq'⟩ := hM q hq
  have hcp : Commute t p' := (mem_centralizer_iff.1 htC p' hp'.1).symm
  have hcq : Commute t q' := (mem_centralizer_iff.1 htC q' hq'.1).symm
  have key : ⁅p, q⁆ = ⁅p', q'⁆ := by
    rcases hpp' with rfl | rfl <;> rcases hqq' with rfl | rfl
    · rfl
    · exact (commutatorElement_mul_central_eq hcp hcq).2
    · exact (commutatorElement_mul_central_eq hcp hcq).1
    · rw [(commutatorElement_mul_central_eq hcp ((Commute.refl t).mul_right hcq)).1,
        (commutatorElement_mul_central_eq hcp hcq).2]
  rw [key]
  exact Subgroup.commutator_mem_commutator hp' hq'

end Commutator

end CFSG.SeitzReduction.SymplecticPilot
