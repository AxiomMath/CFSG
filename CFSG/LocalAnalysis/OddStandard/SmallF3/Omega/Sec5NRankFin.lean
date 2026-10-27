module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def nrZ : SL2F3 × SL2F3 := (sl2f3NegOne, 1)

@[expose] def nrK : SL2F3 × SL2F3 := (sl2f3NegOne, sl2f3NegOne)

@[expose] def nrU : Fin 3 → SL2F3
  | 0 => ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩
  | 1 => ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩
  | 2 => ⟨!![1, -1; -1, -1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def nrCls : Bool × Fin 3 → SL2F3 × SL2F3
  | (false, i) => (nrU i, 1)
  | (true, i) => (1, nrU i)

@[expose] def nrGen : Fin 4 → Bool × Fin 3
  | 0 => (false, 0)
  | 1 => (false, 1)
  | 2 => (true, 0)
  | 3 => (true, 1)

@[expose] def IsQ8P (p : SL2F3 × SL2F3) : Prop := p.1 ^ 4 = 1 ∧ p.2 ^ 4 = 1

instance (p : SL2F3 × SL2F3) : Decidable (IsQ8P p) := by unfold IsQ8P; infer_instance

@[expose] def NrEq (p q : SL2F3 × SL2F3) : Prop := p = q ∨ p = q * nrK

instance (p q : SL2F3 × SL2F3) : Decidable (NrEq p q) := by unfold NrEq; infer_instance

@[expose] def NrR (s t : Bool × Fin 3) : Prop := s.1 = t.1 ∧ s ≠ t

instance (s t : Bool × Fin 3) : Decidable (NrR s t) := by unfold NrR; infer_instance

theorem isQ8P_nrZ : IsQ8P nrZ := by decide +kernel

theorem isQ8P_nrCls (s : Bool × Fin 3) : IsQ8P (nrCls s) := by
  revert s
  decide +kernel

theorem nrK_mul_comm (p : SL2F3 × SL2F3) : nrK * p = p * nrK := by
  revert p
  decide +kernel

theorem nrZ_mul_comm (p : SL2F3 × SL2F3) : nrZ * p = p * nrZ := by
  revert p
  decide +kernel

theorem nrZ_mul_self : nrZ * nrZ = 1 := by decide +kernel

theorem nrZ_ne_one : nrZ ≠ 1 := by decide +kernel

theorem nrZ_ne_nrK : nrZ ≠ nrK := by decide +kernel

theorem nrZ'_eq : ((1 : SL2F3), sl2f3NegOne) = nrZ * nrK := by decide +kernel

theorem sec5nr_comm_cls : ∀ s t : Bool × Fin 3,
    NrEq (nrCls s * nrCls t * (nrCls s)⁻¹ * (nrCls t)⁻¹) (if NrR s t then nrZ else 1) := by
  decide +kernel

theorem sec5nr_sq_cls : ∀ s : Bool × Fin 3, NrEq (nrCls s * nrCls s) nrZ := by
  decide +kernel

theorem sec5nr_classify : ∀ p : SL2F3 × SL2F3, IsQ8P p → NrEq (p * p) nrZ →
    ∃ s : Bool × Fin 3, NrEq p (nrCls s) ∨ NrEq p (nrCls s * nrZ) := by
  decide +kernel

theorem sec5nr_distinct : ∀ (s t : Bool × Fin 3) (a b : Bool),
    NrEq (nrCls s * (if a then nrZ else 1)) (nrCls t * (if b then nrZ else 1)) → s = t := by
  decide +kernel

theorem sec5nr_center : ∀ p : SL2F3 × SL2F3,
    (∀ p' : SL2F3 × SL2F3, IsQ8P p' → NrEq (p * p' * p⁻¹ * p'⁻¹) 1) →
      NrEq p 1 ∨ NrEq p nrZ ∨ NrEq p (1, sl2f3NegOne) := by
  decide +kernel

theorem sec5nr_realize : ∀ ε : Fin 4 → Bool, ∃ p : SL2F3 × SL2F3, IsQ8P p ∧ ∀ g : Fin 4,
    NrEq (p * nrCls (nrGen g) * p⁻¹) (nrCls (nrGen g) * (if ε g then nrZ else 1)) := by
  decide +kernel

theorem sec5nr_gen_word : ∀ p : SL2F3 × SL2F3, IsQ8P p →
    ∃ (a : Fin 4) (b : Fin 2) (c : Fin 4) (d : Fin 2),
      p = nrCls (nrGen 0) ^ (a : ℕ) * nrCls (nrGen 1) ^ (b : ℕ) * nrCls (nrGen 2) ^ (c : ℕ) *
        nrCls (nrGen 3) ^ (d : ℕ) := by
  decide +kernel

theorem sec5nr_inner : ∀ p : SL2F3 × SL2F3, IsQ8P p → ∀ s : Bool × Fin 3,
    NrEq (p * nrCls s * p⁻¹) (nrCls s) ∨ NrEq (p * nrCls s * p⁻¹) (nrCls s * nrZ) := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
