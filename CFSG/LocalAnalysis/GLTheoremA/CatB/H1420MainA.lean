module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1420LyA : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.sporIs .McL) 3 → catalogIs (PSimple 3 K) (S8.sporIs .Ly)

@[expose] def I1420Co1A : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.sporIs .Suz) 3 → catalogIs (PSimple 3 K) (S8.sporIs .Co1)

@[expose] def I1420SuzA : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.isU4of 3) 3 →
      catalogIs (PSimple 3 K) (S8.sporIs .Suz) ∨ S8.IsTypeWithCenter 3 K (S8.sporIs .Fi22) 3

@[expose] def I1420SuzhA : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ D : Subgroup Q), I1420ModelA 3 K I₀ D →
    S8.IsTypeWithCenter 3 I₀ (S8.isU4of 3) 9 →
      catalogIs (PSimple 3 K) (S8.sporIs .Suz) ∨ catalogIs (PSimple 3 K) (S8.sporIs .Co1)

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
