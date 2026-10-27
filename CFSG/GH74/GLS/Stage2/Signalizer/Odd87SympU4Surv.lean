module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympKill
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympU4Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4ThreeIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4Cases

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K]

theorem genericKill_of_symp_bar (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {A : GL (HypIndex 2 0) K} {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = (-1 : K) • 1) :
    GenericKill (hypPSU h 2 0) (semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) := by
  have := h.finite
  obtain ⟨ψ, hψc, hψs⟩ := exists_sp4_comm_of_bar h hp hA hAA
  have hfix := fixed_of_comm_bar h (by norm_num) (by norm_num) hσ hx ψ hψc
  exact genericKill_of_sp4_hom _ h.prime h.one_le hp h.card_fixedField ((hypProj h 2 0).comp ψ)
    (fun x => hfix _ ⟨x, rfl⟩) (fun x hx1 => hψs x hx1)

theorem eq_one_or_neg_one_of_bar (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {c : K} (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = c • 1) : c = 1 ∨ c = -1 := by
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex 2 0 → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (conjOp h (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) v) =
        ((Units.mk0 c hc : Kˣ) : K) • v := conjOp_conjOp hAA
  obtain ⟨hμ1, -⟩ := odd_unitary_conjugate_semilinear_involution_descent h hodd hn1
    (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective hc hAA) (hypForm_conjOp hA)
    (Units.mk0 c hc) hμ
  rcases hμ1 with h1 | h1
  · left
    simpa using congrArg Units.val h1
  · right
    simpa using congrArg Units.val h1

@[expose] def SurvU4Orth (h : UnitaryFieldData p f K) (α : MulAut (hypPSU h 2 0)) : Prop :=
  (∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = 1 ∧
      finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) = 2 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) ∨
    (∃ (A : GL (HypIndex 2 0) K) (l : K)
      (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ l ≠ 0 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧ h.norm l = -1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) ∨
    (∃ (A : GL (HypIndex 2 0) K) (σ : K ≃+* K)
      (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0),
      A ∈ hypUnitary h 2 0 ∧ (∀ c, σ c = h.bar c) ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = 1 ∧
      α = semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩)

theorem genericKill_or_survU4Orth_of_hyp (hMin : MinIndexU33) (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (α : MulAut (hypPSU h 2 0)) (hα : α ^ 2 = 1) :
    GenericKill (hypPSU h 2 0) α ∨ SurvU4Orth h α := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rcases unitary4_involution_cases h hp2 α hα with ⟨ψ, hψ, hfix⟩ | hS
  · exact Or.inl (genericKill_of_su3_block_odd hMin h.one_le hK hp2 α ((hypProj h 2 0).comp ψ) hψ
      (fun g => hfix _ ⟨g, rfl⟩))
  · rcases hS with hS | hS | ⟨A, σ, hx, hA, hσ, c, hc, hAA, hα'⟩
    · exact Or.inr (Or.inl hS)
    · exact Or.inr (Or.inr (Or.inl hS))
    · rcases eq_one_or_neg_one_of_bar h hp2 hA hc hAA with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨A, σ, hx, hA, hσ, by rw [hAA, one_smul], hα'⟩))
      · subst hα'
        exact Or.inl (genericKill_of_symp_bar h hp2 hσ hx hA hAA)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
