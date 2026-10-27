module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1420Model {Q : Type} [Group Q] [Finite Q] (p : ℕ) (K I₀ D : Subgroup Q) : Prop :=
  IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧ D ≤ Subgroup.normalizer (K : Set Q) ∧
    CFSG.Open.IsQuasisimple (PQuot p K) ∧ IsCatalogGroup (PSimple p K) ∧
    GLAPComponent p (K ⊓ Subgroup.centralizer (D : Set Q)) I₀ ∧ ¬ K ≤ I₀ ⊔ GLAPPrimeCoreOf p K ∧
    ∃ a ∈ D, a ≠ 1 ∧ K ≤ Subgroup.centralizer ({a} : Set Q)

@[expose] def I1420Ly : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.sporIs .McL) 3 → catalogIs (PSimple 3 K) (S8.sporIs .Ly)

@[expose] def I1420Co1 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.sporIs .Suz) 3 → catalogIs (PSimple 3 K) (S8.sporIs .Co1)

@[expose] def I1420Suz : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.isU4of 3) 3 →
      catalogIs (PSimple 3 K) (S8.sporIs .Suz) ∨ S8.IsTypeWithCenter 3 K (S8.sporIs .Fi22) 3

@[expose] def I1420Suzh : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.isU4of 3) 9 →
      catalogIs (PSimple 3 K) (S8.sporIs .Suz) ∨ catalogIs (PSimple 3 K) (S8.sporIs .Co1)

@[expose] def I1420M3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.sporIs .Fi24Prime) 3 → catalogIs (PSimple 3 K) (S8.sporIs .M)

@[expose] def I1420M5 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420Model 5 K I₀ D →
    S8.IsTypeWithCenter 5 I₀ (S8.sporIs .HN) 1 → catalogIs (PSimple 5 K) (S8.sporIs .M)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
