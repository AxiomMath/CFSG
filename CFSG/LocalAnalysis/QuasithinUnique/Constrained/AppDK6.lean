module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDC56
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDC61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDK4

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open CFSG.QuasithinUnique.AppC (C61A3Double C56DoubleA3)

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem exists_gcfg (h : A3A3 T M H S L s) : Nonempty (GCfg T M H S L) := by
  obtain ⟨sp⟩ := A3x.exists_spec h
  exact ⟨{ hcs := h.cs
           U := blockU L ⊔ blockU2 L s
           hUdef := (A3x.hUeq h).symm
           P := A3x.piS sp
           hB := A3x.piS_im_B sp
           hS := A3x.piS_im_S sp
           hUQ := A3x.U_le_Q (h := h)
           hQ := A3x.hQ_cent h
           hUD := A3x.U_inf_D h
           hQeq := A3x.Q_eq sp
           hU1 := le_sup_left }⟩

theorem c61A3Double : C61A3Double := by
  intro G _ _ T M H S L hcs h3 hne
  obtain ⟨s, h⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨C⟩ := exists_gcfg h
  exact c61_gen C (A3x.hU0 h) (fun hj _ => hne hj) (Or.inr ⟨h3, hne⟩) (fun _ hj => hne hj)

theorem c56DoubleA3 : C56DoubleA3 := by
  intro G _ _ T M H S L hcs h3 hne M₀ hSM hMT h2
  obtain ⟨s, h⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨C⟩ := exists_gcfg h
  exact c56_gen_double C (A3x.hU0 h) hne hSM hMT h2

end CFSG.QuasithinUnique.AppD
