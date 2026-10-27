module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilCount
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilEigen

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilCount

open Module Polynomial

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U] {Γ : Type} [Group Γ]
  [Fintype Γ] {D : WeilData K U Γ}

omit [Fintype Γ] in
theorem WeilTwist.mem_F_iff_comm (Tw : WeilTwist D) (a : Module.End K U) :
    a ∈ Tw.F ↔ (Tw.T : Module.End K U) * a = a * (Tw.T : Module.End K U) := by
  rw [Tw.mem_F, Tw.AdT_apply]
  constructor
  · intro h
    have h1 := congrArg (fun x => x * (Tw.T : Module.End K U)) h
    simpa [mul_assoc, ← Units.val_mul] using h1.symm.symm
  · intro h
    rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem WeilTwist.weil_bound [FiniteDimensional K U] (Tw : WeilTwist D)
    (hΓ : (Fintype.card Γ : K) ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ 5)
    (σb : MulAut (Γ ⧸ Subgroup.center Γ))
    (hσb : ∀ g : Γ, σb (QuotientGroup.mk g) = QuotientGroup.mk (Tw.σ g)) (h5 : σb ^ 5 = 1)
    (hT5 : (Tw.T : Module.End K U) ^ 5 = 1) :
    ∃ e : ℕ, (finrank K U) ^ 2 = Nat.card (Γ ⧸ Subgroup.center Γ) * e ∧
      (5 * (finrank K (Module.End.eigenspace (Tw.T : Module.End K U) 1) : ℤ) - finrank K U) ^ 2 ≤
        20 * e * Nat.card (MonoidHom.eqLocus
          (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) := by
  classical
  set T : Module.End K U := (Tw.T : Module.End K U) with hT
  set R := nthRootsFinset 5 (1 : K) with hR
  set M := Nat.card (Γ ⧸ Subgroup.center Γ) with hM
  set C := Nat.card (MonoidHom.eqLocus
    (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) with hC
  set e := finrank K D.W1 with he
  set S := finrank K U with hS
  have h4 : S ^ 2 = M * e := by
    rw [hM, Nat.card_eq_fintype_card]
    exact D.finrank_end hΓ
  refine ⟨e, h4, ?_⟩
  have h1 : S ≤ ∑ ξ ∈ R, finrank K (Module.End.eigenspace T ξ) :=
    WeilEigen.finrank_le_sum_finrank_eigenspace T ζ hζ hT5
  have h2 : ∑ ξ ∈ R, (finrank K (Module.End.eigenspace T ξ)) ^ 2 ≤ finrank K Tw.F :=
    WeilEigen.sum_sq_finrank_eigenspace_le T ζ hζ hT5 Tw.F Tw.mem_F_iff_comm
  have h3 : 5 * finrank K Tw.F ≤ (M + 4 * C) * e :=
    Tw.five_finrank_F_le hΓ σb hσb h5
  have hcard : R.card = 5 := hζ.card_nthRootsFinset
  have hone : (1 : K) ∈ R := (mem_nthRootsFinset (by norm_num) 1).mpr (one_pow _)
  set a : K → ℕ := fun ξ => finrank K (Module.End.eigenspace T ξ) with ha
  have hsum : ∑ ξ ∈ R, ((5 : ℤ) * a ξ - S) ^ 2 =
      25 * ∑ ξ ∈ R, ((a ξ : ℤ)) ^ 2 - 10 * S * ∑ ξ ∈ R, (a ξ : ℤ) + 5 * (S : ℤ) ^ 2 := by
    have : ∀ ξ ∈ R, ((5 : ℤ) * a ξ - S) ^ 2 =
        25 * ((a ξ : ℤ)) ^ 2 - 10 * S * (a ξ : ℤ) + (S : ℤ) ^ 2 := fun ξ _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    ring
  have hle : ((5 : ℤ) * a 1 - S) ^ 2 ≤ ∑ ξ ∈ R, ((5 : ℤ) * a ξ - S) ^ 2 :=
    Finset.single_le_sum (f := fun ξ => ((5 : ℤ) * a ξ - S) ^ 2) (fun ξ _ => sq_nonneg _) hone
  have h1' : (S : ℤ) ≤ ∑ ξ ∈ R, (a ξ : ℤ) := by exact_mod_cast h1
  have h2' : ∑ ξ ∈ R, ((a ξ : ℤ)) ^ 2 ≤ (finrank K Tw.F : ℤ) := by exact_mod_cast h2
  have h3' : 5 * (finrank K Tw.F : ℤ) ≤ ((M : ℤ) + 4 * C) * e := by exact_mod_cast h3
  have h4' : (S : ℤ) ^ 2 = (M : ℤ) * e := by exact_mod_cast h4
  have hSB : (S : ℤ) * S ≤ S * ∑ ξ ∈ R, (a ξ : ℤ) :=
    mul_le_mul_of_nonneg_left h1' (Int.natCast_nonneg _)
  show ((5 : ℤ) * a 1 - S) ^ 2 ≤ 20 * e * C
  nlinarith [hle, hsum, h2', h3', h4', hSB]

end CFSG.CGT.PushingUpLit.CGT6.WeilCount
