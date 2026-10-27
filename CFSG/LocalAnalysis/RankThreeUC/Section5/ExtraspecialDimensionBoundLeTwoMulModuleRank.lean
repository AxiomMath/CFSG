module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialDimensionBounds.InvolutionFixedSpaceBounds
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ModuleMMinimizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace ExtraspecialDimensionBounds

theorem commRank_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (t : G) :
    commRank ρ t = Module.finrank (ZMod 2) ↥(BinaryRepresentations.commSpace ρ (Subgroup.zpowers t)) := by
  have hrange : LinearMap.range (ρ t - 1) = BinaryRepresentations.commSpace ρ (Subgroup.zpowers t) := by
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      exact Submodule.subset_span ⟨t, Subgroup.mem_zpowers t, v, by simp⟩
    · apply Submodule.span_le.mpr
      rintro w ⟨x, hx, v, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      show ρ (t ^ k) v - v ∈ LinearMap.range (ρ t - 1)
      clear hx
      induction k using Int.induction_on generalizing v with
      | zero => simp
      | succ k ih =>
        have h1 := ih v
        have h2 : ρ (t ^ ((k : ℤ) + 1)) v - v =
            (ρ t - 1) (ρ (t ^ (k : ℤ)) v) + (ρ (t ^ (k : ℤ)) v - v) := by
          rw [add_comm (k : ℤ) 1, zpow_one_add, map_mul]; simp
        rw [h2]
        exact add_mem ⟨_, rfl⟩ h1
      | pred k ih =>
        have h1 := ih v
        have h2 : ρ (t ^ (-(k : ℤ) - 1)) v - v =
            -(ρ t - 1) (ρ (t ^ (-(k : ℤ) - 1)) v) + (ρ (t ^ (-(k : ℤ))) v - v) := by
          have : ρ (t ^ (-(k : ℤ))) v = ρ t (ρ (t ^ (-(k : ℤ) - 1)) v) := by
            rw [← Module.End.mul_apply, ← map_mul]
            congr 2
            rw [← zpow_one_add]; congr 1; ring
          rw [this]; simp
        rw [h2]
        exact add_mem (neg_mem ⟨_, rfl⟩) h1
  unfold commRank
  rw [hrange]

end ExtraspecialDimensionBounds
theorem extraspecial_dimension_bound_le_two_mul_moduleRank {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (n : ℕ) (hn : Nat.card ↥P = p ^ (1 + 2 * n)) :
    p ^ (n - 1) * (p - 1) * binaryMultiplicativeOrder p ≤ 2 * moduleM ρ := by
  have hS := h.oddPrimeClassTwoAction.setting
  have hp := hS.prime
  have hp2 : p ≠ 2 := by have := hS.odd; rintro rfl; exact absurd this (by decide)
  have hdO : binaryMultiplicativeOrder p = WeakClosure.dOfPrime p := by unfold binaryMultiplicativeOrder; exact (WeakClosure.dOfPrime_eq_orderOf hp hp2).symm
  rw [hdO]
  haveI : Module.Finite (ZMod 2) V :=
    haveI := ExtraspecialDimensionBounds.finiteDimensional_of_irreducible' ρ
      h.faithfulBinaryIrreducibleAction.irreducible
    inferInstance
  have hρ := h.faithfulBinaryIrreducibleAction.faithful
  have hexp := hS.exponent
  have hPn := h.faithfulBinaryIrreducibleAction.normal
  have hH := h.extraspecial
  have key : ∀ X : Subgroup G, X ≤ P → Nat.card ↥X = p → X ≠ centerP P →
      let U := BinaryRepresentations.commSpace ρ (BinaryRepresentations.centerIn P)
      let m := Module.finrank (ZMod 2) ↥(U ⊓ BinaryRepresentations.fixedSpace ρ X)
      p ^ (n - 1) * WeakClosure.dOfPrime p ≤ m ∧ m * p ≤ Module.finrank (ZMod 2) V ∧
        (∀ t : G, orderOf t = 2 → (∀ x ∈ X, t * x * t⁻¹ = x⁻¹) →
          m * (p - 1) ≤ 2 * Module.finrank (ZMod 2) ↥(BinaryRepresentations.commSpace ρ (Subgroup.zpowers t))) := by
    intro X hXP hXp hXZ U m
    obtain ⟨-, h2, -, h4, h5⟩ := BinaryRepresentations.extraspecial_center_commutator_decomposition_and_dimension_bounds ρ hρ hp hp2 P hH hexp hn X hXP hXp hXZ
    refine ⟨?_, ?_, h4⟩
    · have hm : 0 < m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        have h2' : Module.finrank (ZMod 2) U = m * p := h2
        have hU : Module.finrank (ZMod 2) U = 0 := by rw [h2', hm0]; simp
        have hbot : U = ⊥ := Submodule.finrank_eq_zero.mp hU
        have hcZ : Nat.card ↥(BinaryRepresentations.centerIn P) = p := by
          unfold BinaryRepresentations.centerIn
          rw [Subgroup.card_map_of_injective P.subtype_injective]
          exact hH.2.2.2
        have : BinaryRepresentations.centerIn P = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro z hz
          apply hρ
          rw [map_one]
          ext v
          have hmem : ρ z v - v ∈ U := Submodule.subset_span ⟨z, hz, v, rfl⟩
          rw [hbot] at hmem
          have := (Submodule.mem_bot _).mp hmem
          simpa [sub_eq_zero] using this
        rw [this, Subgroup.card_bot] at hcZ
        exact hp.one_lt.ne hcZ
      exact Nat.le_of_dvd hm h5
    · rw [← h2]; exact Submodule.finrank_le U
  by_cases hev : Even (Nat.card G)
  · obtain ⟨t, htT, ht2, htm⟩ := exists_involution_in_sylow_attaining_moduleM ρ T h.faithfulBinaryIrreducibleAction.sylow hev
    rw [← htm, ExtraspecialDimensionBounds.commRank_eq]
    have htN : t ∈ Subgroup.normalizer (P : Set G) := hS.normT htT
    by_cases hPt : ⁅P, Subgroup.zpowers t⁆ = ⊥
    · have := ExtraspecialDimensionBounds.central_case hp hp2 hH hexp hn hPn ρ hρ h.faithfulBinaryIrreducibleAction.irreducible ht2 ?_
      · calc _ = p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) := by ring
          _ ≤ _ := this
      · have hc : ⁅P, Subgroup.zpowers t⁆ ≤ ⊥ := hPt.le
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hPt
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (Subgroup.mem_centralizer_iff.1 (hPt hg) t (Subgroup.mem_zpowers t)).symm
    · obtain ⟨X, hXP, hXp, hXZ, hinv⟩ :=
        ExtraspecialDimensionBounds.exists_inverted hp hp2 hH hexp hn ht2 htN hPt
      obtain ⟨k1, -, k3⟩ := key X hXP hXp hXZ
      have := k3 t ht2 hinv
      calc _ = p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ k1
        _ ≤ _ := this
  · obtain ⟨X, hXP, hXp, hXZ⟩ :=
      NoncentralOrderP.exists_subgroup hp hH hexp
    obtain ⟨k1, k2, -⟩ := key X hXP hXp hXZ
    have hM : moduleM ρ = Module.finrank (ZMod 2) V := by
      unfold moduleM; rw [if_neg hev]
    rw [hM]
    set m := Module.finrank (ZMod 2) ↥(BinaryRepresentations.commSpace ρ (BinaryRepresentations.centerIn P) ⊓ BinaryRepresentations.fixedSpace ρ X)
    calc p ^ (n - 1) * (p - 1) * WeakClosure.dOfPrime p = p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) := by ring
      _ ≤ m * (p - 1) := Nat.mul_le_mul_right _ k1
      _ ≤ m * p := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ Module.finrank (ZMod 2) V := k2
      _ ≤ 2 * Module.finrank (ZMod 2) V := by omega

end Section5
end CFSG.LocalAnalysis.RankThreeUC
