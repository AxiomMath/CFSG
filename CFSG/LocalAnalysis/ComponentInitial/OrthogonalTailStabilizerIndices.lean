module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailFlagTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCountComparison

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

section Scalars

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def elemScalars : Subgroup (orthElementaryGroup Q) where
  carrier := {g | ∃ c : K, ∀ v, (g : V ≃ₗ[K] V) v = c • v}
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, fun v => by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hd, map_smul, hc, smul_smul, mul_comm]⟩
  one_mem' := ⟨1, fun v => by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun v => ?_⟩
    by_cases hc0 : c = 0
    · have hv : ∀ w : V, w = 0 := fun w => (g : V ≃ₗ[K] V).injective (by
        rw [hc, hc0, zero_smul, map_zero])
      rw [hv v, map_zero, smul_zero]
    · have h1 : (g : V ≃ₗ[K] V) (c⁻¹ • v) = v := by
        rw [hc, smul_smul, mul_inv_cancel₀ hc0, one_smul]
      calc ((g⁻¹ : orthElementaryGroup Q) : V ≃ₗ[K] V) v =
          ((g⁻¹ : orthElementaryGroup Q) : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) (c⁻¹ • v)) := by rw [h1]
        _ = ((g⁻¹ * g : orthElementaryGroup Q) : V ≃ₗ[K] V) (c⁻¹ • v) := rfl
        _ = c⁻¹ • v := by rw [inv_mul_cancel]; rfl

instance elemScalars_normal : (elemScalars Q).Normal where
  conj_mem := by
    rintro n ⟨c, hc⟩ g
    refine ⟨c, fun v => ?_⟩
    change (g : V ≃ₗ[K] V) ((n : V ≃ₗ[K] V) (((g⁻¹ : orthElementaryGroup Q) : V ≃ₗ[K] V) v)) = _
    rw [hc, map_smul]
    congr 1
    change ((g * g⁻¹ : orthElementaryGroup Q) : V ≃ₗ[K] V) v = v
    rw [mul_inv_cancel]
    rfl

variable {Q}

theorem mem_stabilizer_iff_map {W : Submodule K V} {g : orthElementaryGroup Q} :
    g ∈ MulAction.stabilizer (orthElementaryGroup Q) W ↔
      W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = W :=
  Iff.rfl

theorem elemScalars_le_stabilizer (W : Submodule K V) :
    elemScalars Q ≤ MulAction.stabilizer (orthElementaryGroup Q) W := by
  rintro g ⟨c, hc⟩
  refine mem_stabilizer_iff_map.2 (le_antisymm ?_ fun w hw => ?_)
  · rintro _ ⟨w, hw, rfl⟩
    change (g : V ≃ₗ[K] V) w ∈ W
    rw [hc]
    exact W.smul_mem c hw
  · by_cases hc0 : c = 0
    · have hv : w = 0 := (g : V ≃ₗ[K] V).injective (by rw [hc, hc0, zero_smul, map_zero])
      rw [hv]
      exact Submodule.zero_mem _
    · refine ⟨c⁻¹ • w, W.smul_mem _ hw, ?_⟩
      change (g : V ≃ₗ[K] V) (c⁻¹ • w) = w
      rw [hc, smul_smul, mul_inv_cancel₀ hc0, one_smul]

variable (Q) in
@[expose] noncomputable def stabP (W : Submodule K V) :
    Subgroup (orthElementaryGroup Q ⧸ elemScalars Q) :=
  (MulAction.stabilizer (orthElementaryGroup Q) W).map (QuotientGroup.mk' (elemScalars Q))

theorem mem_stabP_iff {W : Submodule K V} {x : orthElementaryGroup Q ⧸ elemScalars Q} :
    x ∈ stabP Q W ↔ ∀ g : orthElementaryGroup Q, (g : orthElementaryGroup Q ⧸ elemScalars Q) = x →
      (W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V)) = W := by
  constructor
  · rintro ⟨h, hh, rfl⟩ g hg
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hg
    have hz := elemScalars_le_stabilizer W hg
    have hg' : g = h * (g⁻¹ * h)⁻¹ := by group
    have hgs : g ∈ MulAction.stabilizer (orthElementaryGroup Q) W := by
      rw [hg']
      exact mul_mem hh (inv_mem hz)
    exact mem_stabilizer_iff_map.1 hgs
  · intro h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, mem_stabilizer_iff_map.2 (h g rfl), rfl⟩

theorem index_stabP (W : Submodule K V) :
    (stabP Q W).index = (MulAction.stabilizer (orthElementaryGroup Q) W).index := by
  refine Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  exact elemScalars_le_stabilizer W

end Scalars

section Tail

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem index_stabilizer_eq_card [FiniteDimensional K A] (hani : qA.Anisotropic)
    (hA : ∃ a : A, a ≠ 0) {k : ℕ} (hk : k ≤ r) {W : Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ∈ singularSubspaces (quadTail r qA) k) :
    (MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) W).index =
      Nat.card (singularSubspaces (quadTail r qA) k) := by
  rw [MulAction.index_stabilizer]
  have horb : MulAction.orbit (orthElementaryGroup (quadTail r qA)) W =
      singularSubspaces (quadTail r qA) k := by
    ext X
    constructor
    · rintro ⟨g, rfl⟩
      change W.map (((g : orthElementaryGroup (quadTail r qA)) :
        ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
          ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ∈ _
      refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hW.1, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [LinearEquiv.coe_coe, map_of_mem (orthElementaryGroup_le _ g.2)]
      exact hW.2 w hw
    · intro hX
      obtain ⟨g, hg, hgX⟩ :=
        (orthogonal_geometry_tail_singular_flag_transitivity hani hA).2 k hk W hW X hX
      exact ⟨⟨g, hg⟩, hgX⟩
  rw [horb]
  exact (Nat.card_coe_set_eq _).symm

end Tail


theorem orthogonal_geometry_tail_geometric_stabilizer_indices {K : Type*} [Field K] [Finite K]
    {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} (hr : 1 ≤ r)
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hA : ∃ a : A, a ≠ 0) :
    (∀ k, 1 ≤ k → k ≤ r → ∀ W ∈ singularSubspaces (quadTail r qA) k,
      ((stabP (quadTail r qA) W).index : ℚ) =
        (∏ j ∈ Finset.range k, (((Nat.card K : ℚ) ^ (r - j) - 1) *
          ((Nat.card K : ℚ) ^ (r + finrank K A - j - 1) + 1))) /
          ∏ i ∈ Finset.Icc 1 k, ((Nat.card K : ℚ) ^ i - 1)) ∧
    (3 ≤ r → ∀ k, 2 ≤ k → k ≤ r → ∀ W ∈ singularSubspaces (quadTail r qA) k,
      ∀ L ∈ singularSubspaces (quadTail r qA) 1,
        (stabP (quadTail r qA) L).index < (stabP (quadTail r qA) W).index) := by
  have hidx : ∀ k, k ≤ r → ∀ W ∈ singularSubspaces (quadTail r qA) k,
      ((stabP (quadTail r qA) W).index : ℚ) = tailCount (Nat.card K) r (finrank K A) k := by
    intro k hk W hW
    rw [index_stabP, index_stabilizer_eq_card hani hA hk hW,
      card_singularSubspaces_tail hani hreg hk, tailCount]
  refine ⟨fun k _ hk W hW => hidx k hk W hW, fun hr3 k hk2 hkr W hW L hL => ?_⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ finrank K A := by
    obtain ⟨a, ha⟩ := hA
    have : Nontrivial A := ⟨⟨a, 0, ha⟩⟩
    exact Module.finrank_pos
  have hlt := (orthogonal_geometry_tail_count_comparison hq hr3 hm).2 k hk2 hkr
  rw [← hidx 1 hr L hL, ← hidx k hkr W hW] at hlt
  exact_mod_cast hlt

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
