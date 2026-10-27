module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.FixedVector

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.OddFixed

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem natCard_submodule {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [Finite V] (W : Submodule K V) : Nat.card W = Nat.card K ^ Module.finrank K W :=
  Module.natCard_eq_pow_finrank

theorem exists_fixed_vector_of_odd {r : ℕ} {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {i : ℕ} (hi : i ∈ I) (hodd : Odd i) {v : StatedSp r (ZMod 2)} (hv3 : v ^ 3 = 1)
    (hvJ : v ∈ SymplecticHigher.flagStabilizer r (ZMod 2) I) :
    ∃ a ∈ SymplecticFlag.flag r (ZMod 2) i, a ≠ 0 ∧ spMat v *ᵥ a = a := by
  classical
  set F := SymplecticFlag.flag r (ZMod 2) i with hF
  have hmem : ∀ x : F, spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2) ∈ F := fun x =>
    spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.1 hvJ i hi) x.2
  let f : Function.End F := fun x => ⟨spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2), hmem x⟩
  have hv3' : spMat v ^ 3 = 1 := by rw [← spMat_pow, hv3]; rfl
  have hf3 : f ^ 3 = 1 := by
    funext x
    apply Subtype.ext
    have h3 : spMat v *ᵥ (spMat v *ᵥ (spMat v *ᵥ (x : Fin r ⊕ Fin r → ZMod 2))) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        show spMat v * spMat v * spMat v = spMat v ^ 3 by simp [pow_succ, mul_assoc], hv3',
        Matrix.one_mulVec]
    exact h3
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fintype F := Fintype.ofFinite F
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) (by simpa using hf3)
  have hcard : Fintype.card F = 2 ^ i := by
    have hfr : Module.finrank (ZMod 2) F = i :=
      SymplecticHigher.finrank_flag (r := r) (K := ZMod 2) (by have := (hI i hi).2; omega)
    rw [Fintype.card_eq_nat_card, natCard_submodule F, hfr]
    simp
  rw [hcard] at hmod
  obtain ⟨k, hk⟩ := hodd
  have h2 : 2 ^ i % 3 = 2 := by
    subst hk
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h0 : (0 : F) ∈ f.fixedPoints := by
    show f 0 = 0
    apply Subtype.ext
    simp [f]
  have hpos : 0 < Fintype.card f.fixedPoints := Fintype.card_pos_iff.2 ⟨⟨0, h0⟩⟩
  have hgt : 1 < Fintype.card f.fixedPoints := by
    by_contra hle
    have h1 : Fintype.card f.fixedPoints = 1 := by omega
    rw [h1] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨0, h0⟩
  refine ⟨(y : Fin r ⊕ Fin r → ZMod 2), y.2, ?_, congrArg Subtype.val hy⟩
  intro hy0
  apply hne
  apply Subtype.ext
  exact Subtype.ext hy0

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.OddFixed
