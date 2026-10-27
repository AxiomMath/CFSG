module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.StandardType (GGInndiagCommEq ggInndiagComm GGInndiagCommExclLabel
  GGInndiagCommProvedLabel GGInndiagCommRestInput LargeEvenSimpleGuard)


theorem s265e_exists_label {Γ : Type} [Group Γ] {L B : Subgroup Γ} (h : InnerDiagMarking B L) :
    ∃ lab : GLALabel, ∀ b ∈ B, MarkedInnDiag L b lab := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨lab, fun b hb => ⟨hperf, lab, hlab, ?_⟩⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs', hna', θ', -, hind'⟩
  exact ⟨hs', hna', θ', rfl, hind' b hb⟩

section Certs


private theorem mem_innAutDerived_aux
    (hRest : GGInndiagCommRestInput) {S : Type} [Group S] [Finite S] {lab : GLALabel}
    {α : MulAut S} (hcen : Subgroup.center S = ⊥)
    (hnd : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der)
    (hin : Y10GField.InnDiagKind S lab α) : α ∈ innAutDerived S := by
  by_cases hF : Y10GField.FamOrth lab
  · obtain ⟨-, a, ha⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived S ⟨a, ha⟩
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, -, -, -, hlab, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst lab'
  have hnd' : ¬ MI.DerivedLab lab := fun h => h.elim hnd.2.1 hnd.2.2
  have hne : ¬ GGInndiagCommExclLabel lab := by
    rintro (⟨ht, hr⟩ | h)
    · exact hF (Or.inl ⟨ht, by omega⟩)
    · exact hnd.1 h
  have hall : CFSG.StandardType.LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    by_cases hp : GGInndiagCommProvedLabel lab
    · exact CFSG.StandardType.largeEvenLabelAll_inndiagComm_proved hlam hp
    · exact hRest lab hlam hne hp
  have h2 := (MI.canonAll_iff_legacyAll hlam hnd' _).2 hall _ hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, u, hu, hind⟩, hEq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists h2
  have hu' : u ∈ ggInndiagComm R := by
    rw [← hEq hs hna]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure hu)
  let e : S ≃* R := (CanonInn.quotCenterEquivOfBot hcen).symm.trans θ
  have he : ∀ s, e s = θ (QuotientGroup.mk s) := fun s => by
    show θ ((CanonInn.quotCenterEquivOfBot hcen).symm s) = _
    congr 1
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  have hconj : MulAut.congr e α = u := by
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    show e (α (e.symm (e s))) = u (e s)
    rw [MulEquiv.symm_apply_apply, he, he]
    exact (hind s (α s) rfl).symm
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e, hconj]
  exact hu'

theorem s265e_mem_innAutDerived
    {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ} {y : Γ}
    (hy : y ∈ Subgroup.normalizer (L : Set Γ)) {lab : GLALabel} (hM : MarkedInnDiag L y lab)
    (hnd : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) :
    Y10F.centerQuotAut ↥L (Y10F.conjAut L y hy) ∈ innAutDerived (↥L ⧸ Subgroup.center ↥L) := by
  have hLl : HasLabel ↥L (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hM
  exact mem_innAutDerived_aux CFSG.StandardType.ggInndiagCommRestInput_holds
    (Y10F.center_centerQuot_eq_bot (Y10F.hasLabel_isQuasisimple hLl)) hnd
    (CanonInn.innDiagKind_centerQuot hy hM)

private theorem exists_index_or_small_aux
    {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ} (h : CFSG.Blueprint.LieModel S t n 2 f) :
    (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨ Nat.card S ≤ 20160 := by
  rcases h with ⟨-, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
  · rcases classical_two_cases hm with hd | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl hd
    all_goals
      refine Or.inr ?_
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm]
      decide
  · exact Or.inl (index_of_chevalleyExceptional ht hm)
  · have ht' : t = .twistedF4 ∨ t = .Tits := by
      simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact absurd hm.1.2.2.2.1 (by norm_num)
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact Or.inl (index_of_reeTits_two ht' hm)
  · exact Or.inl (index_of_suzuki hm)

theorem s265e_sside
    {Γ : Type} [Group Γ] [Finite Γ] {L : Subgroup Γ} {lab : GLALabel}
    (hL : HasLabel ↥L (· = lab)) :
    ((lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* d.Group)) ∨
    Nat.card (↥L ⧸ Subgroup.center ↥L) ≤ 17971200 := by
  have hM := CanonSubcomp.markedModel_of_hasLabel hL
  by_cases hB : lab.tag = .B2der
  · right
    rw [CFSG.StandardType.ggMarkedModel_card_b2der hB hM]
    norm_num
  by_cases hG : lab.tag = .G2der
  · right
    rw [MI.card_markedModel_g2der hG hM]
    norm_num
  by_cases hT : lab.tag = .twF4der
  · right
    rw [MI.card_markedModel_twF4der hT hM, MI.ordTits_eq]
    norm_num
  have hc : CFSG.StandardType.markChar lab = 2 := CFSG.StandardType.markChar_eq_two_of_ne hB hG
  have hLM := hM
  unfold CFSG.StandardType.MarkedModel at hLM
  rw [hc] at hLM
  rcases exists_index_or_small_aux hLM with ⟨d, hd, ⟨e⟩⟩ | h
  · exact Or.inl ⟨⟨hB, hG, hT⟩, d, hd, ⟨e⟩⟩
  · exact Or.inr (h.trans (by norm_num))

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265

end
