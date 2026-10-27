module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.HardMathSupport.Dickson.I271.U42Presentation
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest


theorem nonempty_mulEquiv_QP45_of_rels_ne_one {G : Type} [Group G] (g : Fin 2 → G)
    (hrels : ∀ w ∈ u42Words, evalW g w = 1) (hne : g 0 ≠ 1) :
    Nonempty (↥(Subgroup.closure (Set.range g)) ≃* ↥QP45.originalSubgroup) := by
  obtain ⟨hfin, hP⟩ := Certificates.certificate17350
  obtain ⟨φ₁, hφ₁⟩ := CFSG.AGLEmbeddingD2.Wilson.Census228Spor.exists_hom_range_eq_closure g
    u42Words hrels
  obtain ⟨φ₂, hφ₂⟩ := CFSG.AGLEmbeddingD2.Wilson.Census228Spor.exists_hom_range_eq_closure
    (m := 2) (![x45, y45] : Fin 2 → Equiv.Perm (Fin 45)) u42Words
    CFSG.HardMathSupport.Dickson.I271.u42Words_x45_y45
  have hN₂ : 25920 ≤ Nat.card ↥φ₂.range := by
    rw [hφ₂, CFSG.HardMathSupport.Dickson.I271.closure_range_x45_y45,
      CFSG.HardMathSupport.Dickson.I271.card_QP45_eq]
  have hb₂ : Function.Bijective φ₂.rangeRestrict :=
    φ₂.rangeRestrict_surjective.bijective_of_nat_card_le (by omega)
  let e₂ : CFSG.CosetTable.PG 2 u42Words ≃* ↥QP45.originalSubgroup :=
    (MulEquiv.ofBijective φ₂.rangeRestrict hb₂).trans
      (MulEquiv.subgroupCongr
        (hφ₂.trans CFSG.HardMathSupport.Dickson.I271.closure_range_x45_y45))
  haveI : IsSimpleGroup (CFSG.CosetTable.PG 2 u42Words) :=
    CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e₂
  have hker : φ₁.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ₁.ker with h | h
    · exact h
    · refine absurd ?_ hne
      have h0 : g 0 ∈ φ₁.range := by
        rw [hφ₁]
        exact Subgroup.subset_closure ⟨0, rfl⟩
      obtain ⟨x, hx⟩ := h0
      rw [← hx]
      exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)
  let e₁ : CFSG.CosetTable.PG 2 u42Words ≃* ↥(Subgroup.closure (Set.range g)) :=
    (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff φ₁).1 hker)).trans
      (MulEquiv.subgroupCongr hφ₁)
  exact ⟨e₁.symm.trans e₂⟩

private def pp2 : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

private theorem valid_twistedA_three : (TauCeti.LieTypeIndex.twistedA 3 pp2).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [pp2]

private theorem catalogIs_isU4of_two {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (e : X ≃* StatedProj (StatedSU 4 (2 ^ 1) K)) :
    catalogIs X (isU4of 2) := by
  have hc2 : TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 2 :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 pp2
  have hf2 : TauCeti.ValidLieTypeIndex.fieldExponent
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩ = 1 :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 3 pp2
  have eq := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 pp2
    valid_twistedA_three
  have hq : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 3 pp2, valid_twistedA_three⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩ =
        2 ^ 1 := by
    rw [hc2, hf2]
  rw [← hq] at e
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
    ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
      (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) :=
    Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField (TauCeti.ValidLieTypeIndex.characteristic
      ⟨.twistedA 3 pp2, valid_twistedA_three⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 pp2, valid_twistedA_three⟩)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card _ _ (by rw [hf2]; norm_num), hc2, hf2]
    norm_num
  refine ⟨.lie ⟨.twistedA 3 pp2, valid_twistedA_three⟩, ?_, ⟨?_⟩⟩
  · show pp2.card = 2
    rw [TauCeti.PrimePower.card_def]
    norm_num [pp2]
  · exact (e.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hc) 4 _)).trans eq.symm

theorem catalogIs_isPSp43_of_equiv_QP45 {T : Type} [Group T] (e : T ≃* ↥QP45.originalSubgroup) :
    catalogIs T isPSp43 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨i, hi, he⟩ := catalogIs_isU4of_two (K := GaloisField 2 2) hK
    (e.trans (CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP.symm.trans
      (CFSG.GH74.Exceptional.psp43EquivU2.trans CFSG.GH74.Exceptional.u2FourEquiv)))
  exact ⟨i, Or.inl hi, he⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
