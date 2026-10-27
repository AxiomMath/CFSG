module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type} [Field F]

@[expose] def slCast {m n : ℕ} (h : m = n) :
    SpecialLinearGroup (Fin m) F ≃* SpecialLinearGroup (Fin n) F := by
  subst h
  exact MulEquiv.refl _

@[expose] def quaternionSL (r : ℕ) {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 →* SpecialLinearGroup (Fin (2 + r)) F :=
  (blockSL F 2 r).comp (QuaternionMatrices.quatHom h)

theorem quaternionSL_not_mem_center (hF : ringChar F ≠ 2) {r : ℕ} (hr : 1 ≤ r) {a b : F}
    (h : a ^ 2 + b ^ 2 = -1) :
    quaternionSL r h (QuaternionGroup.a 2) ∉ center (SpecialLinearGroup (Fin (2 + r)) F) := by
  rw [← scalars_eq_center]
  intro hmem
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hmem
  have hX : SpecialLinearGroup.toGL (QuaternionMatrices.quatHom h (QuaternionGroup.a 2)) ≠ 1 := by
    intro h1
    apply QuaternionMatrices.neg_one_ne_one_matrix hF
    rw [← QuaternionMatrices.quatHom_a_two h]
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
    simpa using this
  exact blockGL_ne_scalar_of_ne_one hr hX c hc

variable [Finite F]

theorem not_small_source_of_sl_cover {L : Type} [Group L] {n l e : ℕ} (hn : 3 ≤ n)
    (hl : l.Prime) (hl2 : l ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = l ^ e)
    (σ : SpecialLinearGroup (Fin n) F →* L)
    (hσ : σ.ker ≤ center (SpecialLinearGroup (Fin n) F)) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  have : CharP F l := finite_field_prime_power_characteristic hl he hF
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F l]
    exact hl2
  have hn' : n = 2 + (n - 2) := by omega
  set e₀ := slCast (F := F) hn'.symm with he₀
  set σ' := σ.comp e₀.toMonoidHom with hσ'
  have : Group.IsPerfect (SpecialLinearGroup (Fin (2 + (n - 2))) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  have hσ'c : σ'.ker ≤ center (SpecialLinearGroup (Fin (2 + (n - 2))) F) := by
    intro x hx
    have hx' : e₀ x ∈ σ.ker := hx
    have hc := hσ hx'
    rw [mem_center_iff] at hc ⊢
    intro g
    apply e₀.injective
    rw [map_mul, map_mul]
    exact hc (e₀ g)
  obtain ⟨⟨a, b, hab⟩, -⟩ :=
    QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices (K := F) hF2
  have hU : l ^ 3 ∣ Nat.card (unitriangular (2 + (n - 2)) F) := by
    rw [card_unitriangular, hF, ← pow_mul]
    refine pow_dvd_pow l ?_
    have h3 : 3 ≤ (2 + (n - 2)) * (2 + (n - 2) - 1) / 2 := by
      have h6 : 6 ≤ (2 + (n - 2)) * (2 + (n - 2) - 1) :=
        Nat.mul_le_mul (show 3 ≤ 2 + (n - 2) by omega) (show 2 ≤ 2 + (n - 2) - 1 by omega)
      omega
    exact h3.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hUZ : unitriangular (2 + (n - 2)) F ⊓ center _ = ⊥ := by
    rw [← scalars_eq_center]
    exact unitriangular_inf_scalars _
  exact not_small_source_of_cover_quaternion σ' hσ'c (quaternionSL (n - 2) hab)
    (quaternionSL_not_mem_center hF2 (by omega) hab) hl hl2 _ hU hUZ

end CFSG.ComponentClassification.OddSelector
