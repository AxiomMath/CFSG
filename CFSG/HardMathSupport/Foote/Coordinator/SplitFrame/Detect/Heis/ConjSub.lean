module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

theorem conjSub_eq_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : conjSub g A = A := by
  ext x
  rw [mem_conjSub_iff]
  have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).symm
  simpa using h

theorem conjSub_le_of_mem {G : Type*} [Group G] {A : Subgroup G} {n : G} (hn : n ∈ A) :
    conjSub n A ≤ A := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hn hx) (inv_mem hn)

theorem conjSub_le_of_mem_of_le {G : Type*} [Group G] {A H : Subgroup G} {n : G} (hn : n ∈ H)
    (hA : A ≤ H) : conjSub n A ≤ H :=
  (conjSub_mono n hA).trans (conjSub_le_of_mem hn)

theorem conjSub_inv_conjSub {G : Type*} [Group G] (g : G) (A : Subgroup G) :
    conjSub g⁻¹ (conjSub g A) = A := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]


variable (τ : Tag) (K : Type) [Field K]

theorem Qθ_le_Pθ : Qθ τ K ≤ Pθ τ K :=
  (parabolic_root_radical_Levi_factors τ K (Jθ τ)).1

theorem Lθ_le_Pθ : Lθ τ K ≤ Pθ τ K :=
  parabolicLevi_le_parabolicSubgroup (Jθ τ)

theorem Pθ_le_adjointGroup : Pθ τ K ≤ adjointGroup τ K :=
  parabolicSubgroup_le_adjointGroup τ K (Jθ τ)

theorem Qθ_le_adjointGroup : Qθ τ K ≤ adjointGroup τ K :=
  (Qθ_le_Pθ τ K).trans (Pθ_le_adjointGroup τ K)

theorem Pθ_le_normalizer_Qθ : Pθ τ K ≤ Subgroup.normalizer (Qθ τ K : Set (ModGL τ K)) :=
  parabolicSubgroup_le_normalizer_parabolicRadical (Jθ τ)

theorem exists_factor_Pθ {p : ModGL τ K} (hp : p ∈ Pθ τ K) :
    ∃ q ∈ Qθ τ K, ∃ l ∈ Lθ τ K, p = q * l := by
  obtain ⟨-, -, -, -, -, -, hfac, -⟩ := parabolic_root_radical_Levi_factors τ K (Jθ τ)
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hp'⟩, -⟩ := hfac p hp
  exact ⟨q, hq, l, hl, hp'⟩

theorem exists_conjSub_Pθ_Uneg {p : ModGL τ K} (hp : p ∈ Pθ τ K) :
    ∃ q ∈ Qθ τ K, conjSub p (Uneg τ K) = conjSub q (Uneg τ K) := by
  obtain ⟨q, hq, l, hl, rfl⟩ := exists_factor_Pθ τ K hp
  refine ⟨q, hq, ?_⟩
  rw [conjSub_mul, conjSub_eq_of_mem_normalizer (Lθ_le_normalizer_Uneg τ K hl)]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
