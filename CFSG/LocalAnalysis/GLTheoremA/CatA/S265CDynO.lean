module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDyn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.DynO

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Targets


theorem lieModel_of_isF4two {Y : Type} [Group Y] (h : catalogIs Y S9.isF4two) :
    CFSG.Blueprint.LieModel Y .F4 0 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | F4 q =>
      simp only [S9.isF4two, onLie] at hi
      rw [TauCeti.PrimePower.card_def] at hi
      obtain ⟨hp, hexp⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hi
      have hm : CFSG.Blueprint.LieModel Y .F4 0 2 q.exponent :=
        .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
          ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
          CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv hp e⟩)
      rwa [hexp] at hm
    | _ => exact absurd hi (by simp [S9.isF4two, onLie])
  | _ => exact absurd hi (by simp [S9.isF4two, onLie])

theorem lieModel_of_isTE6two {Y : Type} [Group Y] (h : catalogIs Y S9.isTE6two) :
    CFSG.Blueprint.LieModel Y .twistedE6 0 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | twistedE6 q =>
      simp only [S9.isTE6two, onLie] at hi
      rw [TauCeti.PrimePower.card_def] at hi
      obtain ⟨hp, hexp⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hi
      have hm : CFSG.Blueprint.LieModel Y .twistedE6 0 2 q.exponent :=
        .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
          ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
          CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv hp e⟩)
      rwa [hexp] at hm
    | _ => exact absurd hi (by simp [S9.isTE6two, onLie])
  | _ => exact absurd hi (by simp [S9.isTE6two, onLie])

theorem lieModel_of_isTD4two {Y : Type} [Group Y] (h : catalogIs Y S9.isTD4two) :
    CFSG.Blueprint.LieModel Y .trialityD4 0 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | trialityD4 q =>
      simp only [S9.isTD4two, onLie] at hi
      rw [TauCeti.PrimePower.card_def] at hi
      obtain ⟨hp, hexp⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hi
      have hm : CFSG.Blueprint.LieModel Y .trialityD4 0 2 q.exponent :=
        .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
          ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
          CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv hp e⟩)
      rwa [hexp] at hm
    | _ => exact absurd hi (by simp [S9.isTD4two, onLie])
  | _ => exact absurd hi (by simp [S9.isTD4two, onLie])

theorem lieModel_of_isTitsIdx {Y : Type} [Group Y] (h : catalogIs Y isTitsIdx) :
    CFSG.Blueprint.LieModel Y .Tits 0 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | tits =>
      exact .inr (.inr (.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags],
        CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e⟩))
    | _ => exact absurd hi (by simp [isTitsIdx, onLie])
  | _ => exact absurd hi (by simp [isTitsIdx, onLie])

end Targets

section Orders


theorem card_of_target_model {X : Type} [Group X] {T : StatedLieTag}
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel X T 0 2 1) :
    Nat.card X = 3311126603366400 ∨ Nat.card X = 17971200 ∨
      Nat.card X = 76532479683774853939200 ∨ Nat.card X = 211341312 := by
  rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
  rcases hT with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inr (Or.inr (Or.inr (by decide)))

theorem false_of_classicalOr360 {X : Type} [Group X] (h : ClassicalOr360 X) {T : StatedLieTag}
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) T 0 2 1) : False := by
  rcases h with ⟨t, r, e, ht, hm⟩ | h360
  · have key : T = t := by
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · have hr : 2 ≤ r := hm.admissible.2.2.1
        rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
        · exact (CFSG.SeitzReduction.RankOne.sl2EvenTypeDet _ e T 0 1 hm hM.admissible hM).1
        · exact (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hr3 hm hM).1
      · have hr : 3 ≤ r := hm.admissible.2.2.1
        rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr4
        · exact (CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet _ e T 0 1 hm hM.admissible hM).1
        · exact (CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt hr4 _ e T 0 1 hm hM.admissible
            hM).1
      · exact (CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet r _ e T 0 1 hm hM.admissible
          hM).1
      · exact (CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r _ .POmegaPlus e T 0 1
          (Or.inl rfl) hm hM.admissible hM).1
      · exact (CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r _ .POmegaMinus e T 0 1
          (Or.inr rfl) hm hM.admissible hM).1
    subst key
    rcases hT with h | h | h | h <;> rcases ht with h' | h' | h' | h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)
  · obtain ⟨e⟩ := h360
    have hcard : Nat.card (X ⧸ Subgroup.center X) = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rcases card_of_target_model hT hM with hc | hc | hc | hc <;> omega

end Orders

section Field


theorem n_eq_one_of_component_over_two {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    {T : StatedLieTag} {r : ℕ} (hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) T r 2 1) :
    labL.n = 1 := by
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlamL := CanonSubcomp.lambda2_of_hasLabel hS
  have hn1 : 1 ≤ labL.n := hlamL.1
  rcases Nat.lt_or_ge labL.n 2 with hn | hn2
  · omega
  suffices hcan : (canonLabel labL).n = 1 by
    have hdvd := CanonSubcomp.n_dvd_canonLabel_n hlamL
    rw [hcan] at hdvd
    exact Nat.dvd_one.1 hdvd
  obtain ⟨hJ', lab', hlam', hraw'⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hJ.2.2.1 hM
  obtain ⟨_, _, _, _, _, _, _, _, _, hc', hf'⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
  have hJlab : HasLabel ↥J (· = lab') :=
    ⟨hJ', lab', hlam', CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw'⟩
  have hJn : (canonLabel lab').n = 1 := (CanonSubcomp.canonLabel_n_eq_markDeg hlam' hc').trans hf'
  have hβD : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S :=
    I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen hnd hin
  have hc := CanonSubcomp.markChar_eq_two_of_two_le hlamL hn2
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) (CFSG.StandardType.markTag labL)
      (CFSG.StandardType.markRank labL) 2 (CFSG.StandardType.markDeg labL) := by
    have h := CanonSubcomp.markedModel_of_hasLabel hS
    unfold CFSG.StandardType.MarkedModel at h
    rwa [hc] at h
  rcases CanonSubcomp.exists_index_or_small_of_lieModel_two hLM with ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
  ·
    let eS : S ≃* (TauCeti.CFSGIndex.lie d).Group :=
      (CanonInn.quotCenterEquivOfBot hcen).symm.trans e
    have hidx : KD264Lie.CompIdxAt 3 d.1 S := KD264Lie.compIdxAt_of_mulEquiv eS.symm
      (KD264Lie.lieCompIdx_all d 3 Nat.prime_three (by norm_num) (by rw [hd2]; norm_num) trivial)
    obtain ⟨i, ⟨φ⟩, hrel⟩ := hidx β hβD hβ3 hβ1 J hJ
    have hfs := CanonSubcomp.two_pow_canonLabel_n_of_lie
      CFSG.StandardType.ggLabelRigidInput_holds hS d hd2 e
    have hdvd := CanonSubcomp.dvd_canonLabel_n_of_compRelC
      CFSG.StandardType.ggLabelRigidInput_holds hJlab hd2 hfs.symm φ hrel
    rw [hJn] at hdvd
    exact Nat.dvd_one.1 hdvd
  ·
    exfalso
    have hS60 : Nat.card S = 60 := by
      rw [← h60]
      exact (Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).toEquiv).symm
    have hlt : Nat.card ↥J < 60 := by
      calc Nat.card ↥J ≤ Nat.card ↥(fixSubgroup β) := Subgroup.card_le_of_le hJ.1
        _ < Nat.card S := CanonTriL.card_fixSubgroup_lt hβ1
        _ = 60 := hS60
    haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    have hqJ := hJ.2.2
    haveI := hqJ.2
    haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J).ne hqJ.1
  ·
    exact (CanonSubcomp.canonLabel_n_eq_markDeg hlamL hc).trans h1

end Field

section Small


theorem false_of_small_order {S : Type} [Group S] [Finite S] {β : MulAut S} (hβ1 : β ≠ 1)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) {T : StatedLieTag}
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) T 0 2 1)
    (hS : Nat.card S = 360 ∨ Nat.card S = 6048 ∨ Nat.card S = 17971200 ∨
      Nat.card S = 211341312) : False := by
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card S :=
    (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)
  have hlt : Nat.card (↥J ⧸ Subgroup.center ↥J) < Nat.card S := by
    calc Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
      _ ≤ Nat.card ↥(fixSubgroup β) := Subgroup.card_le_of_le hJ.1
      _ < Nat.card S := CanonTriL.card_fixSubgroup_lt hβ1
  rcases card_of_target_model hT hM with h | h | h | h <;>
    rcases hS with h' | h' | h' | h' <;> rw [h, h'] at hdvd hlt <;>
    first | omega | exact absurd hdvd (by decide)

end Small

section Main


theorem false_of_target_of_not_isELabel {S : Type} [Group S] [Finite S] {labL : GLALabel}
    {β : MulAut S} (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) (hnE : ¬ IsELabel labL) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) {T : StatedLieTag}
    (hT : T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4)
    (hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) T 0 2 1) : False := by
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlam := CanonSubcomp.lambda2_of_hasLabel hS
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  have hcls : ClassicalOr360 ↥J → False := fun h => false_of_classicalOr360 h hT hM
  have hfld : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der → labL.n = 1 :=
    fun hnd => n_eq_one_of_component_over_two hcen hin hβ3 hβ1 hnd hJ hM
  have hsmall := false_of_small_order hβ1 hJ hT hM
  obtain ⟨tag, rank, n⟩ := labL
  cases tag with
  | A => exact hcls (classicalOr360_lin hp3 h32 hcen (Or.inl rfl) hin hβ3 hJ)
  | twA => exact hcls (classicalOr360_uni hp3 h32 hcen (Or.inl rfl) hin hβ3 hJ)
  | B => exact hcls (classicalOr360_symp hp3 h32 hcen (Or.inl rfl) hin hβ3 hJ)
  | C => exact hcls (classicalOr360_symp hp3 h32 hcen (Or.inr rfl) hin hβ3 hJ)
  | D =>
    by_cases h3 : rank = 3
    · exact hcls (classicalOr360_lin hp3 h32 hcen (Or.inr (Or.inl ⟨rfl, h3⟩)) hin hβ3 hJ)
    · exact hcls (classicalOr360_orth hp3 h32 hcen (Or.inl ⟨rfl, h3⟩) hin hβ3 hJ)
  | twD =>
    by_cases h2 : rank = 2
    · exact hcls (classicalOr360_lin hp3 h32 hcen (Or.inr (Or.inr ⟨rfl, h2⟩)) hin hβ3 hJ)
    · by_cases h3 : rank = 3
      · exact hcls (classicalOr360_uni hp3 h32 hcen (Or.inr ⟨rfl, h3⟩) hin hβ3 hJ)
      · exact hcls (classicalOr360_orth hp3 h32 hcen (Or.inr ⟨rfl, h2, h3⟩) hin hβ3 hJ)
  | E6 => exact hnE (Or.inl rfl)
  | E7 => exact hnE (Or.inr (Or.inl rfl))
  | E8 => exact hnE (Or.inr (Or.inr (Or.inl rfl)))
  | twE6 => exact hnE (Or.inr (Or.inr (Or.inr rfl)))
  | F4 => exact hcls (classicalOr360_F4 hp3 h32 hcen hin hβ3 hβ1 rfl hJ)
  | triD4 =>
    have hn : n = 1 := hfld ⟨by simp, by simp, by simp⟩
    subst hn
    have hc := CanonTriL.card_of_label_char_two hcen hS rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    exact hsmall (Or.inr (Or.inr (Or.inr (by rw [hc]; decide))))
  | G2 =>
    have hn : n = 1 := hfld ⟨by simp, by simp, by simp⟩
    have h2 : 2 ≤ n := hlam.2.2
    omega
  | twB2 =>
    have hn : n = 1 := hfld ⟨by simp, by simp, by simp⟩
    have h3 : 3 ≤ n := hlam.2.2.2
    omega
  | twF4 =>
    have hn : n = 1 := hfld ⟨by simp, by simp, by simp⟩
    have h3 : 3 ≤ n := hlam.2.2.2
    omega
  | B2der =>
    obtain ⟨-, rfl, rfl⟩ := hlam
    have h360 := card_of_B2der (CanonSubcomp.markedModel_of_hasLabel hS)
    rw [Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).toEquiv] at h360
    exact hsmall (Or.inl h360)
  | G2der =>
    obtain ⟨-, rfl, rfl⟩ := hlam
    have h6048 := card_of_G2der (CanonSubcomp.markedModel_of_hasLabel hS)
    rw [Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).toEquiv] at h6048
    exact hsmall (Or.inr (Or.inl h6048))
  | twF4der =>
    obtain ⟨-, rfl, rfl⟩ := hlam
    have hc := CanonTriL.card_of_label_char_two hcen hS rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    exact hsmall (Or.inr (Or.inr (Or.inl (by rw [hc]; decide))))

theorem dynCThreeS_O : DynCThreeS fun lab => ¬ IsELabel lab := by
  intro S _ _ labL β hcen hin hβ3 hβ1 hnE J hJ
  have key : ∀ {T : StatedLieTag}, (T = .F4 ∨ T = .Tits ∨ T = .twistedE6 ∨ T = .trialityD4) →
      CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) T 0 2 1 → False :=
    fun hT hM => false_of_target_of_not_isELabel hcen hin hβ3 hβ1 hnE hJ hT hM
  exact ⟨fun h => key (Or.inl rfl) (lieModel_of_isF4two h),
    fun h => key (Or.inr (Or.inl rfl)) (lieModel_of_isTitsIdx h),
    fun h => (key (Or.inr (Or.inr (Or.inl rfl))) (lieModel_of_isTE6two h)).elim,
    fun h => (key (Or.inr (Or.inr (Or.inr rfl))) (lieModel_of_isTD4two h)).elim⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265C.DynO

end
