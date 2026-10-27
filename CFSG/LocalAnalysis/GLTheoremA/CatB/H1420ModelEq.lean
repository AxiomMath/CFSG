module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420MainA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

theorem i1420ModelA_of_i1420Model {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    {K I₀ D : Subgroup Q} (h : I1420Model p K I₀ D) : I1420ModelA p K I₀ D :=
  ⟨h, h.2.2.2.2.2.2.2⟩

theorem i1420M3_of_i1420M3A (h : I1420M3A) : I1420M3 :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

theorem i1420M5_of_i1420M5A (h : I1420M5A) : I1420M5 :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

theorem i1420Ly_of_i1420LyA (h : I1420LyA) : I1420Ly :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

theorem i1420Co1_of_i1420Co1A (h : I1420Co1A) : I1420Co1 :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

theorem i1420Suz_of_i1420SuzA (h : I1420SuzA) : I1420Suz :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

theorem i1420Suzh_of_i1420SuzhA (h : I1420SuzhA) : I1420Suzh :=
  fun Q _ _ K I₀ D hM hT => h Q K I₀ D (i1420ModelA_of_i1420Model hM) hT

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
