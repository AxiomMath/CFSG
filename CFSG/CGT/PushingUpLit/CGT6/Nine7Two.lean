module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Amb
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Inv
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankOne

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.Open
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherKnownGroup (IsFourGroup AschbacherKnownGroupFacts)
open scoped commutatorElement

section Clique

variable {G : Type} [Group G] [Finite G]

@[expose] def Clq (A : Subgroup G) : Set (Subgroup G) := {B | B ∈ ConjCl A ∧ Rel A B}

omit [Finite G] in
theorem mem_Clq_self (A : Subgroup G) : A ∈ Clq A := ⟨mem_ConjCl_self A, Rel.refl A⟩

omit [Finite G] in
theorem Dgrp_self_eq_iSup (A : Subgroup G) : Dgrp A A = ⨆ B ∈ Clq A, B := rfl

omit [Finite G] in
theorem ConjCl_eq_of_mem {A B : Subgroup G} (hB : B ∈ ConjCl A) : ConjCl B = ConjCl A := by
  obtain ⟨x, rfl⟩ := hB
  ext C
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨x * g, CFSG.GroupTheory.conjugate_conjugate A x g⟩
  · rintro ⟨y, rfl⟩
    refine ⟨x⁻¹ * y, ?_⟩
    rw [CFSG.GroupTheory.conjugate_conjugate, mul_inv_cancel_left]

omit [Finite G] in
theorem Dgrp_base_change {A B B' : Subgroup G} (hB : B ∈ ConjCl A) : Dgrp B B' = Dgrp A B' := by
  unfold Dgrp
  rw [ConjCl_eq_of_mem hB]

theorem Dgrp_self_of_mem_Clq {A B : Subgroup G} (hB : B ∈ Clq A) (hA : QS A)
    (hs : Star A) : Dgrp B B = Dgrp A A := by
  rw [Dgrp_base_change hB.1]
  exact (Dgrp_eq hA hs (mem_ConjCl_self A) hB.1 hB.2).symm

structure Setting (A : Subgroup G) : Prop where
  qs : QS A
  star : Star A
  glaub : ∀ B ∈ ConjCl A, GlaubermanAt (↥B ⧸ Subgroup.center ↥B)
  partner : ∃ B₂ ∈ ConjCl A, ⁅A, B₂⁆ = ⊥

theorem Setting.base_change {A B : Subgroup G} (h : Setting A) (hB : B ∈ Clq A) :
    Setting B := by
  refine ⟨ConjCl.qs h.qs hB.1, ConjCl.star h.star hB.1, ?_, ?_⟩
  · rw [ConjCl_eq_of_mem hB.1]
    exact h.glaub
  · rw [ConjCl_eq_of_mem hB.1]
    by_cases hBA : B = A
    · subst hBA
      exact h.partner
    · refine ⟨A, mem_ConjCl_self A, ?_⟩
      rcases hB.2 with h' | h'
      · exact absurd h'.symm hBA
      · rw [Subgroup.commutator_comm]
        exact h'

theorem conjugate_mem_Clq {A B : Subgroup G} (hs : Setting A) (hB : B ∈ Clq A) {v : G}
    (hvD : v ∈ Subgroup.normalizer (Dgrp A A : Set G)) : conjugate B v ∈ Clq A := by
  refine ⟨ConjCl.cj hB.1 v, ?_⟩
  have h1 : Rel B (conjugate B v) := by
    apply rel_conjugate_of_mem_normalizer (ConjCl.qs hs.qs hB.1)
    rw [Dgrp_self_of_mem_Clq hB hs.qs hs.star]
    exact hvD
  exact Rel.trans' hs.qs hs.star (mem_ConjCl_self A) hB.1 (ConjCl.cj hB.1 v) hB.2 h1

end Clique

section Rank

variable {G : Type} [Group G] [Finite G]

theorem semisimple_of_qs {A : Subgroup G} (hA : QS A) : aschbacherThm5IsSemisimple A := by
  have := semisimple_of_clique {A} ⟨A, rfl⟩ (fun B hB => hB ▸ hA)
    (fun B hB B' hB' hne => absurd (hB.trans hB'.symm) hne)
  simpa using this

theorem two_le_pRank_of_no_central_involution {A : Subgroup G} (hA : QS A)
    (hnc : ∀ u ∈ A, orderOf u = 2 → u ∉ Subgroup.centralizer (A : Set G)) :
    2 ≤ Open.pRank 2 A := by
  by_contra hlt
  have hle : Open.pRank 2 A ≤ 1 := by omega
  have hrank : CFSG.pRank 2 ↥A ≤ 1 := by
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup]
    exact hle
  obtain ⟨c, hcA, hc2, huniq, -⟩ :=
    AschbacherTheorem5.Involution.unique_involution_of_rank_one_image (semisimple_of_qs hA)
      (MonoidHom.id ↥A) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) hrank
  refine hnc c hcA hc2 (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
  have hx2 : orderOf (x * c * x⁻¹) = 2 := by
    have := orderOf_conjugate_elt c x⁻¹
    rw [inv_inv] at this
    rw [this, hc2]
  have hmem : x * c * x⁻¹ ∈ A := A.mul_mem (A.mul_mem hx hcA) (A.inv_mem hx)
  have := huniq _ hmem hx2
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [this]

end Rank

section Xrest

variable {G : Type} [Group G] [Finite G]

@[expose] def Xrest (A : Subgroup G) : Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ∈ Clq A ∧ B ≠ A), B

omit [Finite G] in
theorem le_Xrest {A B : Subgroup G} (hB : B ∈ Clq A) (hne : B ≠ A) : B ≤ Xrest A :=
  le_iSup₂_of_le B ⟨hB, hne⟩ le_rfl

omit [Finite G] in
theorem Xrest_le_centralizer {A : Subgroup G} : Xrest A ≤ Subgroup.centralizer (A : Set G) := by
  refine iSup₂_le fun B hB => ?_
  rcases hB.1.2 with h | h
  · exact absurd h.symm hB.2
  · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h

theorem Xrest_semisimple {A B₂ : Subgroup G} (hs : Setting A) (hB₂ : B₂ ∈ Clq A)
    (hne : B₂ ≠ A) : aschbacherThm5IsSemisimple (Xrest A) := by
  refine semisimple_of_clique {B | B ∈ Clq A ∧ B ≠ A} ⟨B₂, hB₂, hne⟩ ?_ ?_
  · intro B hB
    exact ConjCl.qs hs.qs hB.1.1
  · intro B hB B' hB' hBB'
    have hrel : Rel B B' := Rel.trans' hs.qs hs.star hB.1.1 (mem_ConjCl_self A) hB'.1.1
      hB.1.2.symm hB'.1.2
    rcases hrel with h | h
    · exact absurd h hBB'
    · exact h

theorem conjugate_Xrest_le {A : Subgroup G} (hs : Setting A) {v : G}
    (hvA : v ∈ Subgroup.normalizer (A : Set G))
    (hvD : v ∈ Subgroup.normalizer (Dgrp A A : Set G)) :
    conjugate (Xrest A) v ≤ Xrest A := by
  unfold Xrest
  rw [conjugate_iSup]
  refine iSup_le fun B => ?_
  rw [conjugate_iSup]
  refine iSup_le fun hB => ?_
  have hBc : conjugate B v ∈ Clq A := conjugate_mem_Clq hs hB.1 hvD
  have hne : conjugate B v ≠ A := by
    intro h
    apply hB.2
    have h2 : conjugate (conjugate B v) v⁻¹ = conjugate A v⁻¹ := by rw [h]
    rw [conjugate_conjugate_inv,
      conjugate_eq_of_mem_normalizer ((Subgroup.normalizer (A : Set G)).inv_mem hvA)] at h2
    exact h2
  exact le_Xrest hBc hne

theorem mem_normalizer_Xrest {A : Subgroup G} (hs : Setting A) {v : G}
    (hvA : v ∈ Subgroup.normalizer (A : Set G))
    (hvD : v ∈ Subgroup.normalizer (Dgrp A A : Set G)) :
    v ∈ Subgroup.normalizer (Xrest A : Set G) :=
  mem_normalizer_of_conjugate_eq
    (Subgroup.eq_of_le_of_card_ge (conjugate_Xrest_le hs hvA hvD) (by rw [card_conjugate]))

end Xrest

section Lemma8

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_zpowers_le_sup_conjugate (L : Subgroup G) {w : G} (hw : orderOf w = 2) :
    ⁅L, Subgroup.zpowers w⁆ ≤ L ⊔ conjugate L w := by
  have hww : w * w = 1 := by rw [← pow_two, ← hw]; exact pow_orderOf_eq_one w
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  refine CFSG.ComponentClassification.AschbacherComponentAction.cyclic_involution_commutator_le
    L _ w hww fun x hx => ?_
  have hmem : w * x⁻¹ * w⁻¹ ∈ conjugate L w := by
    rw [mem_conjugate]
    have e : w * (w * x⁻¹ * w⁻¹) * w⁻¹ = x⁻¹ := by
      rw [hwi]
      calc w * (w * x⁻¹ * w) * w = (w * w) * x⁻¹ * (w * w) := by group
        _ = x⁻¹ := by rw [hww]; group
    rw [e]
    exact L.inv_mem hx
  have e2 : ⁅x, w⁆ = x * (w * x⁻¹ * w⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hmem)

theorem isCompIn_conjugate_normalizer {A : Subgroup G} (hs : Setting A) (g : G) :
    IsCompIn (conjugate A g) (Subgroup.normalizer (conjugate (Dgrp A A) g : Set G)) := by
  have hB₁ : conjugate A g ∈ ConjCl A := ConjCl.cj (mem_ConjCl_self A) g
  rw [Dgrp_conjugate]
  exact (isCompIn_Dgrp hs.qs hB₁).trans
    (Subgroup.normal_subgroupOf_of_le_normalizer (le_refl _)).isSubnormal Subgroup.le_normalizer

theorem lemma8_caseZ {A : Subgroup G} (hs : Setting A) (g : G)
    (hAg : A ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G)) {t : G} (htA : t ∈ A)
    (ht2 : orderOf t = 2) (htc : t ∈ Subgroup.centralizer (A : Set G)) :
    Rel A (conjugate A g) := by
  set B₁ := conjugate A g with hB₁def
  set H' := Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) with hH'def
  have hB₁ : B₁ ∈ ConjCl A := ConjCl.cj (mem_ConjCl_self A) g
  have hB₁c : IsCompIn B₁ H' := isCompIn_conjugate_normalizer hs g
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_single]
    exact (Subgroup.mem_centralizer_iff.1 htc x hx).symm
  have hAcomp : IsCompIn A (H' ⊓ Subgroup.centralizer ({t} : Set G)) :=
    isCompIn_inf_centralizer hs.qs hs.star hAg ht2 hAt
  rcases lemma_2_7_two_amb (hAg htA) ht2 hAcomp hB₁c (hs.glaub B₁ hB₁) with h | h | ⟨hne, hle⟩
  · exact Or.inr h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [card_conjugate]))
  · exfalso
    have htsup : t ∈ B₁ ⊔ conjugate B₁ t :=
      commutator_zpowers_le_sup_conjugate B₁ ht2 (hle htA)
    have hct : IsCompIn (conjugate B₁ t) H' := by
      have := hB₁c.cj t
      rwa [conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer (hAg htA))] at this
    have hcomm : ⁅B₁, conjugate B₁ t⁆ = ⊥ := commute_of_isCompIn_ne hB₁c hct (Ne.symm hne)
    obtain ⟨l, hl, l', hl', hll'⟩ := (mem_sup_iff_of_comm hcomm).1 htsup
    have hle2 : B₁ ≤ conjugate B₁ t := by
      intro z hz
      rw [mem_conjugate]
      have h1 : l' * z = z * l' := (mul_comm_of_commutator_eq_bot hcomm hz hl').symm
      have e : t * z * t⁻¹ = l * z * l⁻¹ := by
        rw [← hll']
        calc l * l' * z * (l * l')⁻¹ = l * (l' * z) * l'⁻¹ * l⁻¹ := by group
          _ = l * (z * l') * l'⁻¹ * l⁻¹ := by rw [h1]
          _ = l * z * l⁻¹ := by group
      rw [e]
      exact B₁.mul_mem (B₁.mul_mem hl hz) (B₁.inv_mem hl)
    exact hne (Subgroup.eq_of_le_of_card_ge hle2 (by rw [card_conjugate])).symm


theorem exists_V {A : Subgroup G} (hs : Setting A) (hK : AschbacherKnownGroupFacts) (g : G)
    (hAg : A ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G))
    (hnc : ∀ u ∈ A, orderOf u = 2 → u ∉ Subgroup.centralizer (A : Set G)) :
    ∃ V : Subgroup G, V ≤ conjugate A g ∧ V ≤ Subgroup.normalizer (A : Set G) ∧
      V ≤ Subgroup.normalizer (Dgrp A A : Set G) ∧ IsFourGroup V := by
  obtain ⟨B₂, hB₂, hcomm⟩ := hs.partner
  set B₁ := conjugate A g with hB₁def
  set H' := Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) with hH'def
  have hB₁c : IsCompIn B₁ H' := isCompIn_conjugate_normalizer hs g
  obtain ⟨U, hUA, hU⟩ := exists_fourGroup_of_two_le_pRank
    (two_le_pRank_of_no_central_involution hs.qs hnc)
  have hUC : ∀ w ∈ U, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤
      Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Dgrp A A : Set G) := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := fourGroup_orderOf hU hw hw1
    exact le_inf
      (centralizer_le_normalizer_of_noncentral hs.qs hs.star (mem_ConjCl_self A) hB₂ hcomm hw2
        (hUA hw) (hnc w (hUA hw) hw2))
      (centralizer_le_normalizer_Dgrp hs.qs hs.star (mem_ConjCl_self A) hB₂ hcomm hw2 (hUA hw))
  have hUg : IsFourGroup (conjugate U g) := isFourGroup_conjugate hU g
  have hUgB : conjugate U g ≤ B₁ := Subgroup.map_mono hUA
  by_cases hUN : U ≤ Subgroup.normalizer (B₁ : Set G)
  ·
    have hcontra : 2 ≤ Open.pRank 2 (AschbacherKnownGroup.centralizerJoin U B₁) := by
      by_contra hlt
      have h38 := AschbacherKnownGroup.lemma_3_8 hK B₁ U (semisimple_of_qs hB₁c.qs) hUN hU
        (by omega)
      have h2 := two_le_pRank_of_fourGroup hUgB hUg
      omega
    have hcj : AschbacherKnownGroup.centralizerJoin U B₁ ≤
        B₁ ⊓ (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Dgrp A A : Set G)) :=
      iSup_le fun u => iSup₂_le fun hu hu1 =>
        le_inf inf_le_left (inf_le_right.trans (hUC u hu hu1))
    obtain ⟨V, hV, hVfour⟩ := exists_fourGroup_of_two_le_pRank hcontra
    have hVj := hV.trans hcj
    exact ⟨V, hVj.trans inf_le_left, hVj.trans (inf_le_right.trans inf_le_left),
      hVj.trans (inf_le_right.trans inf_le_right), hVfour⟩
  ·
    obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, u ∉ Subgroup.normalizer (B₁ : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hUN fun x hx => hcon x hx
    have hmoved : conjugate B₁ u ≠ B₁ := fun h => hu (mem_normalizer_of_conjugate_eq h)
    have hB₁M : B₁ ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Dgrp A A : Set G) :=
      lemma_2_8_amb (hUA.trans hAg) hU hB₁c huU hmoved hUC
    exact ⟨conjugate U g, hUgB, (hUgB.trans hB₁M).trans inf_le_left,
      (hUgB.trans hB₁M).trans inf_le_right, hUg⟩

theorem exists_W {A : Subgroup G} (hs : Setting A) (hK : AschbacherKnownGroupFacts) (g : G)
    (hnc : ∀ u ∈ A, orderOf u = 2 → u ∉ Subgroup.centralizer (A : Set G))
    {V : Subgroup G} (hVB : V ≤ conjugate A g) (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hVD : V ≤ Subgroup.normalizer (Dgrp A A : Set G)) (hV : IsFourGroup V) :
    ∃ W : Subgroup G, W ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) ∧
      W ≤ Subgroup.centralizer (A : Set G) ∧ IsFourGroup W := by
  obtain ⟨B₂, hB₂, hcomm⟩ := hs.partner
  have hB₂c : B₂ ∈ Clq A := ⟨hB₂, Or.inr hcomm⟩
  have hB₂ne : B₂ ≠ A := fun h => qs_commutator_ne_bot hs.qs (h ▸ hcomm)
  have hXss : aschbacherThm5IsSemisimple (Xrest A) := Xrest_semisimple hs hB₂c hB₂ne
  have hVX : V ≤ Subgroup.normalizer (Xrest A : Set G) := fun v hv =>
    mem_normalizer_Xrest hs (hVA hv) (hVD hv)
  have hX2 : 2 ≤ Open.pRank 2 (Xrest A) := by
    obtain ⟨U, hUA, hU⟩ := exists_fourGroup_of_two_le_pRank
      (two_le_pRank_of_no_central_involution hs.qs hnc)
    obtain ⟨x₂, hx₂⟩ := hB₂
    refine two_le_pRank_of_fourGroup ?_ (isFourGroup_conjugate hU x₂)
    rw [hx₂] at hB₂c hB₂ne
    exact (Subgroup.map_mono hUA).trans (le_Xrest hB₂c hB₂ne)
  have hcj : 2 ≤ Open.pRank 2 (AschbacherKnownGroup.centralizerJoin V (Xrest A)) := by
    by_contra hlt
    have h38 := AschbacherKnownGroup.lemma_3_8 hK (Xrest A) V hXss hVX hV (by omega)
    omega
  obtain ⟨W, hW, hWfour⟩ := exists_fourGroup_of_two_le_pRank hcj
  have hB₁ : conjugate A g ∈ ConjCl A := ConjCl.cj (mem_ConjCl_self A) g
  have hB₂g : conjugate B₂ g ∈ ConjCl A := ConjCl.cj hB₂ g
  have hcommg : ⁅conjugate A g, conjugate B₂ g⁆ = ⊥ := by
    rw [conjugate_commutator, hcomm, conjugate_bot]
  have hCv : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) := by
    intro v hv hv1
    have hv2 : orderOf v = 2 := fourGroup_orderOf hV hv hv1
    have := centralizer_le_normalizer_Dgrp hs.qs hs.star hB₁ hB₂g hcommg hv2 (hVB hv)
    rwa [← Dgrp_conjugate] at this
  have hcjle : AschbacherKnownGroup.centralizerJoin V (Xrest A) ≤
      Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) ⊓ Xrest A :=
    iSup_le fun v => iSup₂_le fun hv hv1 =>
      le_inf (inf_le_right.trans (hCv v hv hv1)) inf_le_left
  exact ⟨W, (hW.trans hcjle).trans inf_le_left,
    ((hW.trans hcjle).trans inf_le_right).trans Xrest_le_centralizer, hWfour⟩

theorem lemma8_caseNZ {A : Subgroup G} (hs : Setting A) (hK : AschbacherKnownGroupFacts) (g : G)
    (hAg : A ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G))
    (hnc : ∀ u ∈ A, orderOf u = 2 → u ∉ Subgroup.centralizer (A : Set G)) :
    Rel A (conjugate A g) := by
  obtain ⟨V, hVB, hVA, hVD, hV⟩ := exists_V hs hK g hAg hnc
  obtain ⟨W, hWH, hWC, hW⟩ := exists_W hs hK g hnc hVB hVA hVD hV
  set B₁ := conjugate A g with hB₁def
  set H' := Subgroup.normalizer (conjugate (Dgrp A A) g : Set G) with hH'def
  have hB₁ : B₁ ∈ ConjCl A := ConjCl.cj (mem_ConjCl_self A) g
  have hB₁c : IsCompIn B₁ H' := isCompIn_conjugate_normalizer hs g
  by_contra hRel
  have hne : A ≠ B₁ := fun h => hRel (Or.inl h)
  have hnb : ⁅A, B₁⁆ ≠ ⊥ := fun h => hRel (Or.inr h)
  have hthird : ∀ w ∈ W, w ≠ 1 → conjugate B₁ w ≠ B₁ ∧ A ≤ B₁ ⊔ conjugate B₁ w := by
    intro w hw hw1
    have hw2 : orderOf w = 2 := fourGroup_orderOf hW hw hw1
    have hAw : A ≤ Subgroup.centralizer ({w} : Set G) := by
      intro x hx
      rw [mem_centralizer_single]
      exact (Subgroup.mem_centralizer_iff.1 (hWC hw) x hx).symm
    have hcomp : IsCompIn A (H' ⊓ Subgroup.centralizer ({w} : Set G)) :=
      isCompIn_inf_centralizer hs.qs hs.star hAg hw2 hAw
    rcases lemma_2_7_two_amb (hWH hw) hw2 hcomp hB₁c (hs.glaub B₁ hB₁) with h | h | ⟨hne', hle⟩
    · exact absurd h hnb
    · exact absurd (Subgroup.eq_of_le_of_card_ge h (by rw [card_conjugate])) hne
    · exact ⟨hne', hle.trans (commutator_zpowers_le_sup_conjugate B₁ hw2)⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, hw₁1, hw₂1, hw₁₂, hw₁₂'⟩ := fourGroup_exists_three hW
  obtain ⟨hc₁, hA₁⟩ := hthird w₁ hw₁ hw₁1
  obtain ⟨hc₂, hA₂⟩ := hthird w₂ hw₂ hw₂1
  have hw₂w₂ : w₂ * w₂ = 1 := by rw [← pow_two]; exact fourGroup_sq_eq_one hW hw₂
  have hc₁₂ : conjugate B₁ w₁ ≠ conjugate B₁ w₂ := by
    intro h
    apply (hthird (w₁ * w₂) (W.mul_mem hw₁ hw₂) hw₁₂').1
    rw [← CFSG.GroupTheory.conjugate_conjugate, h, CFSG.GroupTheory.conjugate_conjugate, hw₂w₂,
      conjugate_one]
  have hcomp₁ : IsCompIn (conjugate B₁ w₁) H' := by
    have := hB₁c.cj w₁
    rwa [conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer (hWH hw₁))] at this
  have hcomp₂ : IsCompIn (conjugate B₁ w₂) H' := by
    have := hB₁c.cj w₂
    rwa [conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer (hWH hw₂))] at this
  have hc01 : ⁅B₁, conjugate B₁ w₁⁆ = ⊥ := commute_of_isCompIn_ne hB₁c hcomp₁ (Ne.symm hc₁)
  have hc02 : ⁅B₁, conjugate B₁ w₂⁆ = ⊥ := commute_of_isCompIn_ne hB₁c hcomp₂ (Ne.symm hc₂)
  have hc12 : ⁅conjugate B₁ w₁, conjugate B₁ w₂⁆ = ⊥ := commute_of_isCompIn_ne hcomp₁ hcomp₂ hc₁₂
  have hperf : Group.IsPerfect ↥A := ⟨hs.qs.1⟩
  set L₀ := B₁
  set L₁ := conjugate B₁ w₁
  set L₂ := conjugate B₁ w₂
  have hAL : A ≤ L₀ := by
    refine perfect_le_of_le_mul (P := A) (X := L₀) (D := L₀ ⊔ L₁)
      (Zc := L₁ ⊓ Subgroup.centralizer (L₁ : Set G) ⊓ Subgroup.centralizer (L₀ : Set G))
      hperf hA₁ ((inf_le_left.trans inf_le_left).trans le_sup_right) ?_ ?_
    · intro z hz d hd
      have hzC : L₀ ⊔ L₁ ≤ Subgroup.centralizer ({z} : Set G) := by
        refine sup_le (fun x hx => ?_) (fun x hx => ?_)
        · rw [mem_centralizer_single]
          exact (Subgroup.mem_centralizer_iff.1 hz.2 x hx).symm
        · rw [mem_centralizer_single]
          exact (Subgroup.mem_centralizer_iff.1 hz.1.2 x hx).symm
      exact mem_centralizer_single.1 (hzC hd)
    · intro a ha
      obtain ⟨x, hx, y, hy, hxy⟩ := (mem_sup_iff_of_comm hc01).1 (hA₁ ha)
      obtain ⟨x', hx', y', hy', hxy'⟩ := (mem_sup_iff_of_comm hc02).1 (hA₂ ha)
      refine ⟨x, hx, y, ⟨⟨hy, ?_⟩, ?_⟩, hxy.symm⟩
      · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
        have hyeq : y = (x⁻¹ * x') * y' := by
          calc y = x⁻¹ * (x * y) := by group
            _ = x⁻¹ * (x' * y') := by rw [hxy, hxy']
            _ = (x⁻¹ * x') * y' := by group
        have h1 : l * (x⁻¹ * x') = (x⁻¹ * x') * l :=
          (mul_comm_of_commutator_eq_bot hc01 (L₀.mul_mem (L₀.inv_mem hx) hx') hl).symm
        have h2 : l * y' = y' * l := (mul_comm_of_commutator_eq_bot hc12 hl hy')
        rw [hyeq]
        calc l * ((x⁻¹ * x') * y') = (l * (x⁻¹ * x')) * y' := by group
          _ = ((x⁻¹ * x') * l) * y' := by rw [h1]
          _ = (x⁻¹ * x') * (l * y') := by group
          _ = (x⁻¹ * x') * (y' * l) := by rw [h2]
          _ = ((x⁻¹ * x') * y') * l := by group
      · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
        exact mul_comm_of_commutator_eq_bot hc01 hl hy
  exact hne (Subgroup.eq_of_le_of_card_ge hAL (by rw [card_conjugate]))

theorem lemma8 {A : Subgroup G} (hs : Setting A) (hK : AschbacherKnownGroupFacts) (g : G)
    (hAg : A ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G)) : Rel A (conjugate A g) := by
  by_cases hZ : ∃ t ∈ A, orderOf t = 2 ∧ t ∈ Subgroup.centralizer (A : Set G)
  · obtain ⟨t, htA, ht2, htc⟩ := hZ
    exact lemma8_caseZ hs g hAg htA ht2 htc
  · push Not at hZ
    exact lemma8_caseNZ hs hK g hAg hZ

theorem lemma8_normalizer {A : Subgroup G} (hs : Setting A) (hK : AschbacherKnownGroupFacts)
    (g : G) (hAg : A ≤ Subgroup.normalizer (conjugate (Dgrp A A) g : Set G)) :
    g ∈ Subgroup.normalizer (Dgrp A A : Set G) :=
  mem_normalizer_Dgrp_of_rel hs.qs hs.star (lemma8 hs hK g hAg)

end Lemma8

end CFSG.CGT.PushingUpLit.CGT6.Nine7
