module

public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D13
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1531Stage1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Blocks

@[expose] def Stage15325_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def Stage15325One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 1 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def StageComponentCase_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) → ¬ CharTwo I → False

theorem stage15325_of_blocks_F4 (h113 : StageLemma14113) (h13 : Stage15313_F4) (h1 : Stage15325One_F4) :
    Stage15325_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h I hI
  have hle := h.pRank_Yp_le_two h113
  have hge := h.one_le_pRank_Yp h113 hI
  rcases (by omega : CFSG.Open.pRank 3 Yp = 1 ∨ CFSG.Open.pRank 3 Yp = 2) with h1' | h2'
  · exact h1 G T Mc M V₁ V₂ Yp t h h1' I hI
  · exact h13 G T Mc M V₁ V₂ Yp t h h2' I hI

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem stage15344_of_blocks_F4 (h25 : Stage15325_F4) (hc : StageComponentCase_F4) : Stage15344_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp t h
  by_contra hnu
  obtain ⟨I, hI⟩ := exists_isHPlus_of_not_isUniqueM h hnu
  obtain ⟨J, ⟨hJ, hJI⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {K : Subgroup G | IsHPlus Yp (Sgp153 T V₁) M K ∧ K ≤ I} ⟨I, hI, le_rfl⟩
  refine hc G T Mc M V₁ V₂ Yp t h J hJ (fun K hK hKJ => ?_) (h25 G T Mc M V₁ V₂ Yp t h J hJ)
  by_contra hne
  exact hmin K ⟨hK, hKJ.trans hJI⟩ (lt_of_le_of_ne hKJ hne)

end Blocks

end CFSG.Quasithin
