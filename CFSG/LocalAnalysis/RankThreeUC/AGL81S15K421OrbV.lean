module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Mono

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OrbProof

open K421MonoProof

@[expose] def act (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (x : V3) : V3 :=
  fun b => (if ε (π.symm b) then -1 else 1) * x (π.symm b)

@[expose] def nz (x : V3) : ℕ := (Finset.univ.filter fun b => x b ≠ 0).card

@[expose] def rep : Fin 3 → V3
  | 0 => ![1, 0, 0]
  | 1 => ![1, 1, 0]
  | 2 => ![1, 1, 1]

@[expose] def Indep (u v : V3) : Prop := ∀ a b : ZMod 3, a • u + b • v = 0 → a = 0 ∧ b = 0

instance (u v : V3) : Decidable (Indep u v) := by unfold Indep; infer_instance

theorem nz_eq_zero_iff : ∀ x : V3, nz x = 0 ↔ x = 0 := by
  unfold nz
  decide +kernel

theorem exists_act_rep : ∀ x : V3, x ≠ 0 →
    ∃ (t : Fin 3) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
      nz x = t.val + 1 ∧ act π ε x = rep t := by
  unfold nz act rep
  decide +kernel

theorem indep_of : ∀ u v : V3, u ≠ 0 → v ≠ 0 → v ≠ u → v ≠ -u → Indep u v := by
  unfold Indep
  decide +kernel

theorem exists_odd_weight : ∀ u v : V3, Indep u v →
    ∃ a b : ZMod 3, nz (a • u + b • v) = 1 ∨ nz (a • u + b • v) = 3 := by
  unfold Indep nz
  decide +kernel

theorem exists_two_weights : ∀ u v : V3, Indep u v →
    ∃ a b a' b' : ZMod 3, a • u + b • v ≠ 0 ∧ a' • u + b' • v ≠ 0 ∧
      nz (a • u + b • v) ≠ nz (a' • u + b' • v) := by
  unfold Indep nz
  decide +kernel

end K421OrbProof

end CFSG.LocalAnalysis.RankThreeUC.S15
