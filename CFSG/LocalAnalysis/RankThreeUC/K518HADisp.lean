module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAFamSU
public import CFSG.LocalAnalysis.RankThreeUC.K518HAFamMinus
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LieType.Steinberg.CentralExt.PSLAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.Tits.GN516

private theorem hasRkModel_alt_eight {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 8)) :
    HasRkModel Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 1 := ⟨by norm_num⟩
  obtain ⟨e8⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField 2 1))).1
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_four_two_lieModel
  exact hasRkModel_psl (m := 3) (F := GaloisField 2 1) (e8.trans e.symm)

private theorem hasRkModel_model_seven {Y : Type} [Group Y]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 7 1) : HasRkModel Y := by
  obtain ⟨e7⟩ := CFSG.QuasithinUnique.Bridge.Over.nonempty_equiv_sl_three_two_of_model_seven h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasRkModel_psl (m := 2) (F := ZMod 2)
    (((QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot).trans e7.symm)

private theorem hasRkModel_lieIndex
    {Y : Type} [Group Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1)
    (hr : ¬ RankOneChevTwo Y) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : HasRkModel Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    exact hasRkModel_psl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
        e.symm)
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    by_cases hr2 : r = 2
    · subst hr2
      exact absurd (Or.inl ⟨⟨_, hv⟩, Or.inr ⟨q, hd, rfl⟩, ⟨e⟩⟩) hr
    · have hn3 := h.1.2.2.1
      exact hasRkModel_of_model_psu h (by omega)
  | B r q =>
    change q.p = 2 at hd
    have hr' := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact hasRkModel_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact hasRkModel_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact hasRkModel_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact hasRkModel_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact hasRkModel_g2 (e.trans b.symm)
  | _ => exact hd.elim

theorem mem_range_conj_of_card {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    {m : ℕ} (hdvd : Nat.card (MulAut Y) ∣ m * Nat.card Y) {c : MulAut Y} {p k : ℕ}
    (hc : orderOf c = p ^ k) (hpm : Nat.Coprime p m) :
    c ∈ (MulAut.conj : Y →* MulAut Y).range := by
  classical
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot hZ
  haveI : Finite (MulAut Y) := Finite.of_injective (fun f : MulAut Y => (f : Y → Y))
    (fun f g h => MulEquiv.ext fun x => congrFun h x)
  set N : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hN
  haveI : N.Normal := ⟨by
    rintro _ ⟨y, rfl⟩ φ
    exact ⟨φ y, (mulAut_mul_conj_mul_inv φ y).symm ▸ rfl⟩⟩
  have hNcard : Nat.card N = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hindex : N.index ∣ m := by
    have h1 := Subgroup.card_mul_index N
    rw [hNcard] at h1
    rw [← h1, mul_comm (Nat.card Y) N.index] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd
  set q : MulAut Y →* MulAut Y ⧸ N := QuotientGroup.mk' N with hq
  have hord : orderOf (q c) ∣ p ^ k := hc ▸ orderOf_map_dvd q c
  have hord2 : orderOf (q c) ∣ m := by
    have h1 : orderOf (q c) ∣ Nat.card (MulAut Y ⧸ N) := orderOf_dvd_natCard _
    rw [← Subgroup.index_eq_card] at h1
    exact h1.trans hindex
  have h3 : orderOf (q c) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hpm) hord hord2
  have h4 : q c = 1 := orderOf_eq_one_iff.1 h3
  rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4

theorem hasRkModel_or_smallAut
    {Y : Type} [Group Y] (hc : IsClassicalTwoOrG2 Y) (hr : ¬ RankOneChevTwo Y) :
    HasRkModel Y ∨ ∃ m : ℕ, (m = 4 ∨ m = 2) ∧ Nat.card (MulAut Y) ∣ m * Nat.card Y := by
  rcases hc with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact Or.inl (hasRkModel_lieIndex d hd hr e)
  · rcases hn with rfl | rfl | rfl
    · exact absurd (Or.inr ⟨e⟩) hr
    · right
      refine ⟨4, Or.inl rfl, ?_⟩
      have h1 : Nat.card (MulAut Y) ∣ 1440 := by
        rw [Nat.card_congr (MulAut.congr e).toEquiv]
        exact CFSG.HardMathSupport.Timmesfeld.Tables.Alt.card_mulAut_alternating_six_dvd
      have h2 : Nat.card Y = 360 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [h2]
      simpa using h1
    · exact Or.inl (hasRkModel_alt_eight e)
  · rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · left
      obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact hasRkModel_model_seven h
    · right
      obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
      refine ⟨2, Or.inr rfl, ?_⟩
      rw [CFSG.GH74.KGroups.U33.card_mulAut e', Nat.card_congr e'.toEquiv,
        CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
        CFSG.GH74.KGroups.U33.QP_valid.2]

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
