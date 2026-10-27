module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Tag
public import CFSG.ClassicalInvolution.Q3.Q3T8Sect
public import CFSG.ClassicalInvolution.Q3.Q3T6FusM

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank

section Stmt

@[expose] def C26_3_S4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        SectionLieTypeU 3 1 Ω (omegaNbrGen Ω K) .PSL 3 ∨
          SectionCompU 3 1 Ω (omegaNbrGen Ω K) Q3.CompData.m11

end Stmt

section Proof


section Trans

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem dConnected_or_transitive3 {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hlt : Nat.card Y < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) :
    DConnected Φ ∨ ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : Y, conjSub g K = L := by
  by_cases htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : Y, conjSub g K = L
  · exact Or.inr htrans
  left
  push Not at htrans
  obtain ⟨K₀, hK₀, M₀, hM₀, hnc⟩ := htrans
  have hc0 : Commutes K₀ M₀ :=
    h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA K₀ hK₀ M₀ hM₀ (fun ⟨g, hg⟩ => hnc g hg)
  have hne0 : K₀ ≠ M₀ := fun h => hnc 1 (by rw [conjSub_one, h])
  have hadj0 : dAdj Φ K₀ M₀ := dAdj_of_commutes hM₀ hne0 hc0
  have hjoin : ∀ M ∈ Φ,
      Relation.ReflTransGen (fun A B : Subgroup Y => B ∈ Φ ∧ dAdj Φ A B) K₀ M ∧
        Relation.ReflTransGen (fun A B : Subgroup Y => B ∈ Φ ∧ dAdj Φ A B) M K₀ := by
    intro M hM
    by_cases hMc : ∃ g : Y, conjSub g K₀ = M
    · have hnotM : ¬ ∃ g : Y, conjSub g M = M₀ := by
        rintro ⟨g, hg⟩
        obtain ⟨y, rfl⟩ := hMc
        exact hnc (g * y) (by rw [conjSub_mul]; exact hg)
      have hc : Commutes M M₀ :=
        h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA M hM M₀ hM₀ hnotM
      have hne : M ≠ M₀ := fun h => hnotM ⟨1, by rw [conjSub_one, h]⟩
      have hadj : dAdj Φ M M₀ := dAdj_of_commutes hM₀ hne hc
      exact ⟨(Relation.ReflTransGen.single ⟨hM₀, hadj0⟩).tail ⟨hM, dAdj_symm hadj⟩,
        (Relation.ReflTransGen.single ⟨hM₀, hadj⟩).tail ⟨hK₀, dAdj_symm hadj0⟩⟩
    · push Not at hMc
      have hc : Commutes K₀ M :=
        h4 (by norm_num) (by norm_num) Y hlt Φ hΦ hO hA K₀ hK₀ M hM (fun ⟨g, hg⟩ => hMc g hg)
      have hne : K₀ ≠ M := fun h => hMc 1 (by rw [conjSub_one, h])
      have hadj : dAdj Φ K₀ M := dAdj_of_commutes hM hne hc
      exact ⟨Relation.ReflTransGen.single ⟨hM, hadj⟩,
        Relation.ReflTransGen.single ⟨hK₀, dAdj_symm hadj⟩⟩
  intro K hK L hL
  exact (hjoin K hK).2.trans (hjoin L hL).1

omit [Finite Y] in
theorem eq_of_dConnected_of_dEdgeless3 (hc : DConnected Φ) (he : DEdgeless Φ) {K L : Subgroup Y}
    (hK : K ∈ Φ) (hL : L ∈ Φ) : K = L := by
  rcases (hc K hK L hL).cases_head with h | ⟨c, ⟨hcΦ, hadj⟩, -⟩
  · exact h
  · exact absurd hadj (he K hK c hcΦ)

end Trans

section Main

theorem false_of_muIsoZ2_of_muIsoS3 {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}
    {W : Subgroup Y} (h2 : MuIsoZ2 Φ W) (h3 : MuIsoS3 Φ W) : False := by
  obtain ⟨e2⟩ := h2
  obtain ⟨e3⟩ := h3
  have h := Nat.card_congr (e2.symm.trans e3).toEquiv
  have h2' : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h3' : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [h2', h3'] at h
  omega

theorem inClassU_restrict_hull {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) {X : Subgroup G} (hX : layerHull Ω X = X)
    (hne : (restrictFamily Ω X).Nonempty) : InClassU (.sl2 3 1) (restrictFamily Ω X) := by
  classical
  have hne' : ({L | L ∈ Ω ∧ L ≤ X} : Set (Subgroup G)).Nonempty := by
    obtain ⟨_, L, hL, hLX, rfl⟩ := hne
    exact ⟨L, hL, hLX⟩
  have hgen : (⨆ L ∈ ({L | L ∈ Ω ∧ L ≤ X} : Set (Subgroup G)), L) = X := by
    refine le_antisymm (iSup₂_le fun L hL => hL.2) ?_
    refine hX.symm.le.trans ?_
    unfold layerHull
    refine iSup₂_le fun L hL => iSup_le fun hLX => ?_
    exact le_iSup₂ (f := fun L (_ : L ∈ ({L | L ∈ Ω ∧ L ≤ X} : Set (Subgroup G))) => L) L
      ⟨hL, hLX⟩
  have key := inClassU_of_isClassicalMemberU_in (t := .sl2 3 1) (H := X)
    (𝒮 := {L | L ∈ Ω ∧ L ≤ X}) hne' (fun L hL => hL.2)
    (fun n hn L hL => ⟨hΩ.conjInvariant n L hL.1, by
      have := conjSub_mono (n := n) hL.2
      rwa [conjSub_eq_self_of_mem hn] at this⟩) hgen
    (fun L hL => by
      obtain ⟨z, hz⟩ := hΩ.classical L hL.1
      exact ⟨z, hL.2 hz.mem, hz.subgroupOf hL.2⟩)
  have heq : restrictFamily {L | L ∈ Ω ∧ L ≤ X} X = restrictFamily Ω X := by
    ext L'
    constructor
    · rintro ⟨L, ⟨hL, hLX⟩, hLX', h⟩
      exact ⟨L, hL, hLX', h⟩
    · rintro ⟨L, hL, hLX, h⟩
      exact ⟨L, ⟨hL, hLX⟩, hLX, h⟩
  rwa [heq] at key

theorem c26_3_S4_of_x (hB : S26XProper) (hE : S26XEdgeless) (hT : S26XTop) (hZ : S26XMuZ2) :
    C26_3_S4 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  have hΩU : HypOmegaModU (.sl2 3 1) Ω := hs.stand.modU
  have hA : ∀ L ∈ Ω, AEmpty Ω L := hs.stand.aEmpty
  have hn : CITBelowT (.sl2 3 1) (Nat.card G) := hs.stand.below
  have hih : IH8T 3 1 (Nat.card G) := hs.stand.ih
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hXp : X ≠ ⊤ := hB G Ω K J S R T W z t hs hdisc hS4
  have hDE : DEdgeless (oddQuotientFamily (restrictFamily Ω X)) :=
    hE G Ω K J S R T W z t hs hdisc hS4
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := hT G Ω K J S R T W z t hs hdisc hS4
  obtain ⟨W', hW', hZ2⟩ := hZ G Ω K J S R T W z t hs hdisc hS4
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

end Main

end Proof

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
