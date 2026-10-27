module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ
public import CFSG.ClassicalInvolution.Q3.Q3T7SectB

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Disc3

section Gen

theorem omegaGen_oddQuotientFamily3 {Y : Type} [Group Y] {Λ : Set (Subgroup Y)}
    (hgen : omegaGen Λ = ⊤) : omegaGen (oddQuotientFamily Λ) = ⊤ :=
  CFSG.ClassicalInvolution.Asc77.omegaGen_oddQuotientFamily hgen

end Gen

section Convert


variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

noncomputable def toLieSystemDataU {ι : Type} (D : OmegaLieU p f Φ) (hgen : omegaGen Φ = ⊤)
    (e : ι ≃ Fin D.card) : LieSystemDataU p f ι X Φ where
  kind j := D.kind (e j)
  valid j := D.valid (e j)
  hom j := D.hom (e j)
  ker_le_center j := D.ker_le_center (e j)
  commute i j hij x y := D.commute (e i) (e j) (e.injective.ne hij) x y
  generate := (Equiv.iSup_comp (g := fun i => (D.hom i).range) e).trans (D.generate.trans hgen)
  fundamental L hL := by
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, R, hR, hLR⟩
  meets j := D.meets (e j)
  card_eq h := D.card_eq h

end Convert

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {c : G}

theorem omegaGen_layerFam3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) : omegaGen (layerFam3 Ω c) = ⊤ :=
  omegaGen_oddQuotientFamily3 (Λ := exactPair3 Ω c)
    (inClass3_exactPair3 (inClass3_of_stand3 hs) hc2 hne).generated

theorem layerTransSect3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty)
    (htrans : ∀ A ∈ layerFam3 Ω c, ∀ B ∈ layerFam3 Ω c,
      ∃ g : layerQuot3 Ω c, conjSub g A = B) : TransSect3 (layerFam3 Ω c) :=
  ⟨hypOmegaModU_layerFam3 hs hc2 hne, layerQuot3_oddCore_eq_bot, omegaGen_layerFam3 hs hc2 hne,
    htrans, aEmpty_layerFam3 hs hc2 hne⟩

theorem layerLieType3_of_hasLieTypeU (hgen : omegaGen (layerFam3 Ω c) = ⊤)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (h : HasLieTypeU 3 1 (layerFam3 Ω c) t n) : LayerLieType3 Ω c t n := by
  rw [layerLieType3_iff]
  obtain ⟨D, hcard, i, hi⟩ := h
  have : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  refine ⟨toLieSystemDataU D hgen (finCongr hcard.symm), ?_⟩
  have e : finCongr hcard.symm (0 : Fin 1) = i := Subsingleton.elim _ _
  show CompIs 3 1 (D.kind (finCongr hcard.symm (0 : Fin 1))) t n
  rw [e]
  exact hi

theorem layerOrthType3_of_twin (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) (hne : (tqMembers3 Ω c).Nonempty)
    (htrans : ∀ A ∈ layerFam3 Ω c, ∀ B ∈ layerFam3 Ω c,
      ∃ g : layerQuot3 Ω c, conjSub g A = B)
    {A : Subgroup (layerQuot3 Ω c)} (hA : A ∈ layerFam3 Ω c)
    (htwin : ∃ A' ∈ twinSet (layerFam3 Ω c) A, A' ≠ A) :
    ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ LayerOrthType3 Ω c d ε := by
  have hT := layerTransSect3 hs hc2 hne htrans
  obtain ⟨d, ε, hd, t, n, htag, hLie⟩ := thm7SectBelowU_of hs.below (layerQuot3 Ω c)
    (card_layerQuot3_lt hnc) (layerFam3 Ω c) hT A hA htwin
  exact ⟨d, ε, hd, t, n, htag, layerLieType3_of_hasLieTypeU (omegaGen_layerFam3 hs hc2 hne) hLie⟩

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T7
