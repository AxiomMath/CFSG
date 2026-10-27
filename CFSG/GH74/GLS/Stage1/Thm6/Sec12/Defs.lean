module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IsElemAb2 (E : Subgroup G) : Prop :=
  ∀ a ∈ E, a * a = 1 ∧ ∀ b ∈ E, a * b = b * a

@[expose] def IsFour (V : Subgroup G) : Prop :=
  IsElemAb2 V ∧ Nat.card V = 4

@[expose] def Rank2Le (H : Subgroup G) (n : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ H → IsElemAb2 E → Nat.card E ≤ 2 ^ n

@[expose] def omega1 (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {u : G | u ∈ H ∧ u * u = 1}

@[expose] def phi2 (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {s : G | ∃ d ∈ H, s = d * d}

@[expose] def centIn (T A : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (A : Set G)

@[expose] def NormalIn (N T : Subgroup G) : Prop :=
  N ≤ T ∧ ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N

@[expose] def omegaZ (T : Subgroup G) : Subgroup G where
  carrier := {u | u ∈ T ∧ u * u = 1 ∧ ∀ t ∈ T, u * t = t * u}
  mul_mem' := by
    rintro a b ⟨ha, ha2, hac⟩ ⟨hb, hb2, hbc⟩
    refine ⟨T.mul_mem ha hb, ?_, ?_⟩
    · have hba : b * a = a * b := (hac b hb).symm
      calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by simp only [mul_assoc]
        _ = 1 := by rw [ha2, hb2, mul_one]
    · intro t ht
      calc a * b * t = a * (b * t) := by simp only [mul_assoc]
        _ = a * (t * b) := by rw [hbc t ht]
        _ = (a * t) * b := by simp only [mul_assoc]
        _ = (t * a) * b := by rw [hac t ht]
        _ = t * (a * b) := by simp only [mul_assoc]
  one_mem' := ⟨T.one_mem, by simp, fun t _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha2, hac⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hinv]
    exact ⟨ha, ha2, hac⟩

@[expose] def Hconj (g : G) (H : Subgroup G) : Subgroup G :=
  H.comap (MulAut.conj g).toMonoidHom

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
