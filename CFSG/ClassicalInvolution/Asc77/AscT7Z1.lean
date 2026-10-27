module

public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exactLayer_eq_omegaGen (Ω : Set (Subgroup G)) (c : G) :
    exactLayer Ω c = omegaGen (exactFamily Ω c) :=
  exactLayer_eq_iSup Ω c

omit [Finite G]
  in
theorem exists_omegaLie_of_sectionLieType {Φ : Set (Subgroup G)}
    (hO : classicalInvolutionOddCore ↥(omegaGen Φ) = ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h : SectionLieType p f Φ (omegaGen Φ) t n) :
    ∃ D : OmegaLie p f Φ, D.card = 1 ∧ ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  set Y := omegaGen Φ with hY
  obtain ⟨D, hcard, i₀, hi₀, hr₀⟩ := h
  let ε : (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  let g : (↥Y ⧸ classicalInvolutionOddCore ↥Y) →* G := Y.subtype.comp ε.toMonoidHom
  have hginj : Function.Injective g := Y.subtype_injective.comp ε.injective
  have hgmk : ∀ L ∈ Φ, ((L.subgroupOf Y).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))).map g = L := by
    intro L hL
    rw [Subgroup.map_map]
    have : g.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) = Y.subtype := by
      ext y
      rfl
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le (le_omegaGen hL)
  have hrange : g.range = Y := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact (ε q).2
    · intro hx
      obtain ⟨q, hq⟩ := ε.surjective ⟨x, hx⟩
      exact ⟨q, by simp [g, hq]⟩
  have hfund : ∀ L' ∈ oddQuotientFamily (restrictFamily Φ Y), ∃ L ∈ Φ, L'.map g = L := by
    rintro _ ⟨_, ⟨L, hL, -, rfl⟩, rfl⟩
    exact ⟨L, hL, hgmk L hL⟩
  refine ⟨{ card := D.card
            tag := D.tag
            rank := D.rank
            exp := D.exp
            hom := fun i => g.comp (D.hom i)
            isFundTag := D.isFundTag
            admissible := D.admissible
            exp_eq := D.exp_eq
            ker_le_center := ?_
            commute := ?_
            generate := ?_
            fundamental := ?_
            meets := ?_ }, hcard, i₀, hi₀, hr₀⟩
  · intro i x hx
    have : D.hom i x = 1 := hginj (by simpa using hx)
    exact D.ker_le_center i this
  · intro i j hij x y
    simp only [MonoidHom.comp_apply, ← map_mul]
    rw [D.commute i j hij x y]
  · simp only [MonoidHom.range_comp]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top, hrange]
  · intro L hL
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental _ ⟨_, ⟨L, hL, le_omegaGen hL, rfl⟩, rfl⟩
    refine ⟨i, R, hR, ?_⟩
    rw [← Subgroup.map_map, ← hLR]
    exact (hgmk L hL).symm
  · intro i
    obtain ⟨R, hR, hmem⟩ := D.meets i
    obtain ⟨L, hL, hLR⟩ := hfund _ hmem
    refine ⟨R, hR, ?_⟩
    rw [Subgroup.map_map] at hLR
    simpa [Subgroup.map_map, hLR] using hL

theorem exists_omegaLie_of_layerOrth {Ω : Set (Subgroup G)} {c : G} {d : ℕ} {ε : Bool}
    (hO : classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥) (h : LayerOrthType p f Ω c d ε) :
    ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsOrthTag d ε t n ∧
      ∃ D : OmegaLie p f (exactFamily Ω c), D.card = 1 ∧
        ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  obtain ⟨t, n, ht, hS⟩ := h
  refine ⟨t, n, ht, ?_⟩
  rw [exactLayer_eq_omegaGen] at hO hS
  exact exists_omegaLie_of_sectionLieType hO hS

end T7Z

end CFSG.ClassicalInvolution.Asc77
