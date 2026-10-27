module

public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8B01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Section


theorem e2_proved : SectionLeaf := by
  intro G _ _ _ Ω K J S R T W z t h
  have hs : Std8 Ω K J S R T W z t := h.bad.std
  have hXne : omegaNbrGen Ω K ≠ ⊤ := h.proper
  have hE : MuIsoE4 Ω W := h.mu
  unfold SectionE4
  have hΩU : HypOmegaModU (.sl2 3 1) Ω := hs.stand.modU
  have hA : ∀ L ∈ Ω, AEmpty Ω L := hs.stand.aEmpty
  have hn : CITBelowT (.sl2 3 1) (Nat.card G) := hs.stand.below
  have hih : IH8T 3 1 (Nat.card G) := hs.stand.ih
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hXp : X ≠ ⊤ := hXne
  obtain ⟨W', hW', hZ2⟩ := T8W.s26XMuZ2_E4_of_data hs hE hXne
  have hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω X)) := by
    have hGen0 := Sect.s26_genSection_omegaNbrGen (K := K) hΩU hA
    exact s26_dEdgeless_of_muIsoZ2 l7_5_2_proved hGen0.modU
      ⟨hGen0.hyp, hGen0.cls, hGen0.aEmpty⟩ hW' hZ2
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := s26_top_notMem_of_c26_1H c26_1H_proved hs
  have hcardX : Nat.card ↥X < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group X)
      (fun h => hXp (Subgroup.eq_top_of_card_eq X h))
  have hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < Nat.card G :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective) hcardX
  have hGen := Sect.s26_genSection_omegaNbrGen (K := K) hΩU hA
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hΦne : (oddQuotientFamily (restrictFamily Ω X)).Nonempty :=
    ⟨_, ⟨J.subgroupOf X, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩⟩
  have hne : (restrictFamily Ω X).Nonempty := ⟨J.subgroupOf X, J, hs.hJ.1, hJX, rfl⟩
  have hL : layerHull Ω X = X := s26_layerHull_omegaNbrGen Ω K
  have hcls : InClassU (.sl2 3 1) (restrictFamily Ω X) := inClassU_restrict_hull hΩU hL hne
  have hΛU : HypOmegaModU (.sl2 3 1) (restrictFamily Ω X) := Q3T6.hypOmegaModU_restrict hΩU X
  have hΛg : HypOmegaGen (restrictFamily Ω X) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛU
  have hconj : ConjInvariant (oddQuotientFamily (restrictFamily Ω X)) :=
    conjInvariant_oddQuotientFamily hΛU.conjInvariant
  have hno : ∀ A ∈ oddQuotientFamily (restrictFamily Ω X),
      ∀ B ∈ oddQuotientFamily (restrictFamily Ω X), ¬ Commutes A B := by
    intro A hA' B hB' hAB
    by_cases hEq : A = B
    · subst hEq
      obtain ⟨K₁, hK₁, rfl⟩ := hA'
      obtain ⟨x, hx, y, hy, hxy⟩ := Q3T6.exists_noncomm_map_of_mem hΛg hK₁
      exact hxy (hAB _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
    · exact hDE A hA' B hB' (dAdj_of_commutes hB' hEq hAB)
  obtain ⟨ι, -, ⟨D₀⟩⟩ := (hn ↥X hcardX _ hcls).toLieSystemU
  have : Subsingleton ι := Q3T6.subsingleton_of_noCommute D₀ hno
  obtain ⟨L₀, hL₀⟩ := hΦne
  obtain ⟨i₀, -⟩ := D₀.fundamental L₀ hL₀
  have : Unique ι := uniqueOfSubsingleton i₀
  let D := D₀.reindex (Equiv.ofUnique (Fin 1) ι)
  have hΦne' : (oddQuotientFamily (restrictFamily Ω X)).Nonempty := ⟨L₀, hL₀⟩
  have hnt : Nontrivial (↥X ⧸ classicalInvolutionOddCore ↥X) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hno L₀ hL₀ L₀ hL₀ (fun a _ b _ => Subsingleton.elim _ _)
  have hexcl : ∀ (t' : StatedLieTag) (k : ℕ), S1911.IsT6Tag t' k → ¬ (t' = .PSL ∧ k = 3) →
      CompIs 3 1 (D.kind 0) t' k → False := by
    intro t' k htag hnot hc
    obtain ⟨e, he, hft, hadm, hc'⟩ := hc
    have hsimple : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X) :=
      Q3T6.isSimpleGroup_of_systemU (by norm_num) D 0 hconj htag hft hadm he hc' hGen.oddCore
    have htrans : ∀ K' ∈ oddQuotientFamily (restrictFamily Ω X),
        ∀ L' ∈ oddQuotientFamily (restrictFamily Ω X),
          ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g K' = L' := by
      rcases dConnected_or_transitive3 hih.thm4 hlt hGen.modU hGen.oddCore hGen.aEmpty with
        hc3 | ht
      · exfalso
        apply htop
        have hall : omegaGen (oddQuotientFamily (restrictFamily Ω X)) = L₀ := by
          refine le_antisymm (iSup₂_le fun L hL' => ?_) (le_omegaGen hL₀)
          rw [eq_of_dConnected_of_dEdgeless3 hc3 hDE hL' hL₀]
        rw [← hGen.gen, hall]
        exact hL₀
      · exact ht
    have hrows := hih.muTable (by norm_num) (by norm_num) (↥X ⧸ classicalInvolutionOddCore ↥X)
      hlt _ hGen.modU hGen.aEmpty hΦne' htrans W' hW'
    have hS3 : MuIsoS3 (oddQuotientFamily (restrictFamily Ω X)) W' := by
      refine hrows.2.1.mpr ?_
      have hpi : piSign 3 1 = false := by decide
      rw [hpi]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hcomp : CompIs 3 1 (D.kind 0) t' k := ⟨e, he, hft, hadm, hc'⟩
      rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd ⟨rfl, rfl⟩ hnot
      · exact Or.inl ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩
      · exact Or.inr (Or.inl ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩)
      · exact Or.inr (Or.inr ⟨omegaLieU_of_sysData D hGen.gen, rfl, ⟨0, Nat.one_pos⟩, hcomp⟩)
    exact false_of_muIsoZ2_of_muIsoS3 hZ2 hS3
  rcases tag_cases_of_sysData D hconj hno hΦne' htop with ⟨t', k, htag, hc⟩ | hc
  · by_cases hL3 : t' = .PSL ∧ k = 3
    · obtain ⟨rfl, rfl⟩ := hL3
      exact Or.inl ⟨D, hc⟩
    · exfalso
      refine hexcl t' k ?_ hL3 hc
      rcases htag with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr ⟨D, hc⟩

end Section

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
