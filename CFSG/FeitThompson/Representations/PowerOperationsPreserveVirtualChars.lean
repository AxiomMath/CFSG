module

public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
public import CFSG.FeitThompson.Representations.ExteriorPowerCharacteristicCoefficients
public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Pointwise

section Mul

variable {G : Type*} [Monoid G] {M : Type*}

@[simp]
theorem powOp_const (n : ℕ) (m : M) :
    powOp n (Function.const G m) = Function.const G m := by
  ext g; simp [Function.const]

@[simp]
theorem powOp_one_fun [One M] (n : ℕ) : powOp n (1 : G → M) = 1 := powOp_const n 1

@[simp]
theorem powOp_mul [Mul M] (n : ℕ) (f h : G → M) :
    powOp n (f * h) = powOp n f * powOp n h := by
  ext g; simp

end Mul

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] {g : G}

theorem powOp_mem_classFun (n : ℕ) {f : G → ℂ} (hf : f ∈ classFun G) :
    powOp n f ∈ classFun G := by
  rw [mem_classFun]
  intro x y h
  simpa using classFun.apply_eq_of_isConj hf (h.pow n)

theorem Representation.character_mem_span_Irr [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : ρ.character ∈ Submodule.span ℤ (Irr G) := by
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul ρ
  rw [hm]
  refine Submodule.sum_mem _ fun χ _ => ?_
  have h : ((m χ : ℂ) • (χ : G → ℂ)) = (m χ) • (χ : G → ℂ) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [h]
  exact nsmul_mem (Submodule.subset_span (mem_irrFinset.1 χ.2)) _

theorem FDRep.character_mem_span_Irr [Finite G] (Z : FDRep ℂ G) :
    (FDRep.character Z : G → ℂ) ∈ Submodule.span ℤ (Irr G) := by
  rw [fdRepCharacter_eq]
  exact Representation.character_mem_span_Irr Z.ρ

theorem exteriorChar_mem_span_Irr [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (j : ℕ) :
    Representation.exteriorChar ρ j ∈ Submodule.span ℤ (Irr G) := by
  rw [Representation.exteriorChar_eq_character]
  exact Representation.character_mem_span_Irr _

theorem mul_mem_span_Irr [Finite G] {f h : G → ℂ} (hf : f ∈ Submodule.span ℤ (Irr G))
    (hh : h ∈ Submodule.span ℤ (Irr G)) : f * h ∈ Submodule.span ℤ (Irr G) := by
  have key : Irr G * Irr G ⊆ (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := by
    intro x hx
    obtain ⟨χ, hχ, ψ, hψ, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨Z, -, rfl⟩ := mem_Irr.1 hχ
    obtain ⟨Z', -, rfl⟩ := mem_Irr.1 hψ
    rw [← FDRep.char_tensor]
    exact FDRep.character_mem_span_Irr _
  have hmem := Submodule.mul_mem_mul hf hh
  rw [Submodule.span_mul_span] at hmem
  exact Submodule.span_le.2 key hmem

private theorem sum_pow_eq_newton {ι : Type*} [Fintype ι] (α : ι → ℂ) {m : ℕ} (hm : 0 < m) :
    ∑ i, α i ^ m
      = (-1) ^ (m + 1) * (m : ℂ) * (Finset.univ.val.map α).esymm m
        + ∑ j ∈ Finset.Ico 1 m,
            (-1 : ℂ) ^ (j + 1) * (Finset.univ.val.map α).esymm j * ∑ i, α i ^ (m - j) := by
  classical
  have hps : ∀ k : ℕ, MvPolynomial.aeval α (MvPolynomial.psum ι ℂ k) = ∑ i, α i ^ k := by
    intro k
    rw [MvPolynomial.psum, map_sum]
    simp
  have h := congrArg (MvPolynomial.aeval α) (MvPolynomial.psum_eq_mul_esymm_sub_sum ι ℂ m hm)
  rw [map_sub, map_sum, hps, map_mul, map_mul, MvPolynomial.aeval_esymm_eq_multiset_esymm,
    map_pow, map_neg, map_one, map_natCast] at h
  have h2 : ∀ a : ℕ × ℕ, MvPolynomial.aeval α
      ((-1) ^ a.1 * MvPolynomial.esymm ι ℂ a.1 * MvPolynomial.psum ι ℂ a.2)
      = (-1 : ℂ) ^ a.1 * (Finset.univ.val.map α).esymm a.1 * ∑ i, α i ^ a.2 := by
    intro a
    rw [map_mul, map_mul, MvPolynomial.aeval_esymm_eq_multiset_esymm, hps, map_pow, map_neg,
      map_one]
  rw [Finset.sum_congr rfl fun a _ => h2 a] at h
  rw [h, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun j _ => ?_
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ico]
    omega
  · rw [pow_succ]
    ring

theorem Representation.character_pow_eq_sum_exteriorChar [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hg : IsOfFinOrder g) {m : ℕ} (hm : 0 < m) :
    ρ.character (g ^ m)
      = (-1) ^ (m + 1) * (m : ℂ) * Representation.exteriorChar ρ m g
        + ∑ j ∈ Finset.Ico 1 m,
            (-1 : ℂ) ^ (j + 1) * Representation.exteriorChar ρ j g *
              ρ.character (g ^ (m - j)) := by
  obtain ⟨b, α, hα, -⟩ := Representation.exists_basis_eigenvector ρ hg
  have hpow : ∀ (k : ℕ) (i), ρ (g ^ k) (b i) = α i ^ k • b i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      rw [pow_succ, map_mul, Module.End.mul_apply, hα i, map_smul, ih i, smul_smul, pow_succ]
      ring_nf
  have hs : ∀ k : ℕ, ρ.character (g ^ k) = ∑ i, α i ^ k := fun k =>
    Representation.character_eq_sum_of_eigenbasis (g := g ^ k) ρ b _ (hpow k)
  have he : ∀ j : ℕ, Representation.exteriorChar ρ j g = (Finset.univ.val.map α).esymm j :=
    fun j => Representation.exteriorChar_eq_esymm_of_eigenbasis ρ j b α hα
  rw [hs, he, sum_pow_eq_newton α hm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [he, hs]

theorem Representation.powOp_character_mem_span_Irr [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : ∀ {n : ℕ}, 1 ≤ n →
      powOp n ρ.character ∈ Submodule.span ℤ (Irr G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have key : powOp n ρ.character
        = ((-1) ^ (n + 1) * (n : ℤ)) • Representation.exteriorChar ρ n
          + ∑ j ∈ Finset.Ico 1 n,
              ((-1 : ℤ) ^ (j + 1)) •
                (Representation.exteriorChar ρ j * powOp (n - j) ρ.character) := by
      funext x
      rw [powOp_apply,
        Representation.character_pow_eq_sum_exteriorChar ρ (isOfFinOrder_of_finite x) hn]
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.mul_apply, powOp_apply]
      push_cast [zsmul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [key]
    refine Submodule.add_mem _ (zsmul_mem (exteriorChar_mem_span_Irr ρ n) _)
      (Submodule.sum_mem _ fun j hj => zsmul_mem ?_ _)
    simp only [Finset.mem_Ico] at hj
    exact mul_mem_span_Irr (exteriorChar_mem_span_Irr ρ j) (ih (n - j) (by omega) (by omega))

theorem powOp_mem_span_Irr [Finite G] {n : ℕ} (hn : 1 ≤ n) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : powOp n f ∈ Submodule.span ℤ (Irr G) := by
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
    obtain ⟨Z, -, rfl⟩ := mem_Irr.1 hχ
    rw [fdRepCharacter_eq]
    exact Representation.powOp_character_mem_span_Irr Z.ρ hn
  | zero =>
    have hzero : powOp n (0 : G → ℂ) = 0 := by ext x; simp
    rw [hzero]
    exact Submodule.zero_mem _
  | add f h _ _ hf hh =>
    have hadd : powOp n (f + h) = powOp n f + powOp n h := by ext x; simp
    rw [hadd]
    exact Submodule.add_mem _ hf hh
  | smul c f _ hf =>
    have hsmul : powOp n (c • f) = c • powOp n f := by ext x; simp
    rw [hsmul]
    exact Submodule.smul_mem _ c hf

theorem powOp_mem_virtualChars [Finite G] {n : ℕ} (hn : 1 ≤ n) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : powOp n f ∈ virtualChars G :=
  span_Irr_le_virtualChars (powOp_mem_span_Irr hn hf)

end CFSG.FeitThompson
