module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

noncomputable def pSimpleEquiv {p : ℕ} {X : Subgroup G} {Y : Subgroup G'}
    (e : PQuot p X ≃* PQuot p Y) : PSimple p X ≃* PSimple p Y :=
  QuotientGroup.congr (Subgroup.center (PQuot p X)) (Subgroup.center (PQuot p Y)) e
    (Subgroup.map_center_eq e)

theorem pSimpleIsLie_of_mulEquiv {p : ℕ} {X : Subgroup G} {Y : Subgroup G'}
    (e : PQuot p X ≃* PQuot p Y) (d : TauCeti.LieTypeIndex) (h : pSimpleIsLie p Y d) :
    pSimpleIsLie p X d := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := h
  exact ⟨i, hi, ⟨(pSimpleEquiv e).trans φ⟩⟩

theorem isSL3Type_of_mulEquiv {p q : ℕ} {X : Subgroup G} {Y : Subgroup G'}
    (e : PQuot p X ≃* PQuot p Y) (h : IsSL3Type p q Y) : IsSL3Type p q X := by
  obtain ⟨Q, hQ, hL, hc⟩ := h
  refine ⟨Q, hQ, ?_, fun h3 => ?_⟩
  · rcases hL with hL | hL
    · exact Or.inl (pSimpleIsLie_of_mulEquiv e _ hL)
    · exact Or.inr (pSimpleIsLie_of_mulEquiv e _ hL)
  · intro hbot
    apply hc h3
    rw [← Subgroup.map_center_eq e, hbot, Subgroup.map_bot]

theorem isOmegaType_of_mulEquiv {p q : ℕ} {X : Subgroup G} {Y : Subgroup G'}
    (e : PQuot p X ≃* PQuot p Y) (h : IsOmegaType p q Y) : IsOmegaType p q X := by
  obtain ⟨Q, hQ, hL⟩ := h
  refine ⟨Q, hQ, ?_⟩
  rcases hL with hL | hL | hL
  · exact Or.inl (pSimpleIsLie_of_mulEquiv e _ hL)
  · exact Or.inr (Or.inl (pSimpleIsLie_of_mulEquiv e _ hL))
  · exact Or.inr (Or.inr (pSimpleIsLie_of_mulEquiv e _ hL))

end CFSG.LocalAnalysis.GLTheoremA.H81
