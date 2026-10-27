module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

open Matrix

theorem braid_of_rel {R : Type*} [Ring R] (a b : R) (ha2 : a + a = 0) (hb2 : b + b = 0)
    (haa : a * a = 0) (hbb : b * b = 0) (hab : a * b * a = a) (hba : b * a * b = b) :
    (1 + a) * (1 + b) * (1 + a) = (1 + b) * (1 + a) * (1 + b) := by
  have e1 : (1 + a) * (1 + b) * (1 + a) =
      1 + (a + a) + b + a * b + b * a + a * a + a * b * a := by noncomm_ring
  have e2 : (1 + b) * (1 + a) * (1 + b) =
      1 + (b + b) + a + a * b + b * a + b * b + b * a * b := by noncomm_ring
  rw [e1, e2, ha2, hb2, haa, hbb, hab, hba]
  abel

section Support

variable {n : ℕ} {R : Type*} [Ring R]

@[expose] def SuppIn (S : Set (Fin n)) (N : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ a b, N a b ≠ 0 → a ∈ S ∧ b ∈ S

theorem SuppIn.add {S : Set (Fin n)} {N M : Matrix (Fin n) (Fin n) R} (hN : SuppIn S N)
    (hM : SuppIn S M) : SuppIn S (N + M) := by
  intro a b hab
  by_cases h : N a b = 0
  · have : M a b ≠ 0 := fun h' => hab (by simp [h, h'])
    exact hM a b this
  · exact hN a b h

theorem SuppIn.neg {S : Set (Fin n)} {N : Matrix (Fin n) (Fin n) R} (hN : SuppIn S N) :
    SuppIn S (-N) := fun a b hab => hN a b (fun h => hab (by simp [h]))

theorem SuppIn.sub {S : Set (Fin n)} {N M : Matrix (Fin n) (Fin n) R} (hN : SuppIn S N)
    (hM : SuppIn S M) : SuppIn S (N - M) := by
  rw [sub_eq_add_neg]
  exact hN.add hM.neg

theorem suppIn_single [DecidableEq (Fin n)] {S : Set (Fin n)} {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (x : R) : SuppIn S (single a b x) := by
  intro c d hcd
  by_cases h : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨ha, hb⟩
  · exact absurd (by simp [h]) hcd

theorem SuppIn.mul_eq_zero {S T : Set (Fin n)} (hST : Disjoint S T)
    {N M : Matrix (Fin n) (Fin n) R} (hN : SuppIn S N) (hM : SuppIn T M) : N * M = 0 := by
  ext a b
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : N a c = 0
  · rw [h, zero_mul]
  · by_cases h' : M c b = 0
    · rw [h', mul_zero]
    · exact absurd (hN a c h).2 (Set.disjoint_left.1 hST.symm (hM c b h').1)

theorem commute_one_add_of_disjoint {S T : Set (Fin n)} (hST : Disjoint S T)
    {N M : Matrix (Fin n) (Fin n) R} (hN : SuppIn S N) (hM : SuppIn T M) :
    Commute (1 + N) (1 + M) := by
  have h1 := hN.mul_eq_zero hST hM
  have h2 := hM.mul_eq_zero hST.symm hN
  change (1 + N) * (1 + M) = (1 + M) * (1 + N)
  have e1 : (1 + N) * (1 + M) = 1 + N + M + N * M := by noncomm_ring
  have e2 : (1 + M) * (1 + N) = 1 + M + N + M * N := by noncomm_ring
  rw [e1, e2, h1, h2]
  abel

end Support

end CFSG.HardMathSupport.Lang.AlphaThree
