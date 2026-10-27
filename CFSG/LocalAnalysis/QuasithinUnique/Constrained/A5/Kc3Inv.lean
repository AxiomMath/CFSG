module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem chevalleyExceptionalModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {p f : ℕ} (h : ChevalleyExceptionalModel G t p f) :
    ChevalleyExceptionalModel G' t p f := by
  obtain ⟨hadm, h⟩ := h
  refine ⟨hadm, ?_⟩
  cases t <;> first
    | exact h
    | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)
    | (obtain ⟨K, hK, hKf, hcard, σ, hσ, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, σ, hσ, ⟨e.symm.trans e'⟩⟩)

theorem reeTitsModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {p f : ℕ} (h : ReeTitsModel G t p f) : ReeTitsModel G' t p f := by
  obtain ⟨hadm, a, ha, h⟩ := h
  refine ⟨hadm, a, ha, ?_⟩
  cases t <;> first
    | exact h
    | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
       exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)

theorem isoInv_psl3 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3PSL3 X) : Kc3PSL3 Y :=
  let ⟨f, hf, hm⟩ := h
  ⟨f, hf, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm⟩

theorem isoInv_psp4 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3PSp4 X) : Kc3PSp4 Y :=
  let ⟨f, hf, hm⟩ := h
  ⟨f, hf, CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hm⟩

theorem isoInv_g2 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3G2 X) : Kc3G2 Y :=
  let ⟨f, hf, hm⟩ := h
  ⟨f, hf, chevalleyExceptionalModel_of_mulEquiv e hm⟩

theorem isoInv_d4 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3D4 X) : Kc3D4 Y :=
  let ⟨f, hf, hm⟩ := h
  ⟨f, hf, chevalleyExceptionalModel_of_mulEquiv e hm⟩

theorem isoInv_f4 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3F4 X) : Kc3F4 Y :=
  let ⟨f, hodd, hf, hm⟩ := h
  ⟨f, hodd, hf, reeTitsModel_of_mulEquiv e hm⟩

theorem isoInv_tits (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3Tits X) : Kc3Tits Y :=
  reeTitsModel_of_mulEquiv e h

theorem isoInv_l4 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3L4 X) : Kc3L4 Y :=
  CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h

theorem isoInv_l5 (X Y : Type) [Group X] [Group Y] (e : X ≃* Y) (h : Kc3L5 X) : Kc3L5 Y :=
  CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e h

theorem isoInv_spor (s : TauCeti.SporadicName) (X Y : Type) [Group X] [Group Y] (e : X ≃* Y)
    (h : Kc3Spor s X) : Kc3Spor s Y :=
  let ⟨e'⟩ := h
  ⟨e.symm.trans e'⟩

end CFSG.QuasithinUnique.A5
