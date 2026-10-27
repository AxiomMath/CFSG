module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

@[expose] def SpCompIdx : TauCeti.LieTypeIndex → Prop
  | .B s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ 2 ≤ s ∧ ¬(s = 2 ∧ IsTwoPow q 1)
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | .twistedA r q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ 2 ≤ r ∧ ¬(r = 2 ∧ IsTwoPow q 1)
  | _ => False

@[expose] def SpCompType (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* ↥(alternatingGroup (Fin 6))) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, SpCompIdx d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem isoInvariant_spCompType : IsoInvariant SpCompType := by
  intro Q Q' _ _ e h
  rcases h with h | ⟨d, hd, ⟨a⟩⟩
  · obtain ⟨a⟩ := h
    exact Or.inl ⟨e.symm.trans a⟩
  · exact Or.inr ⟨d, hd, ⟨e.symm.trans a⟩⟩

@[expose] def IsSpFirstClaimIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ 3 ∣ r + 1 ∧ 5 ≤ r ∧ ¬(r = 5 ∧ IsTwoPow q 1)
  | _ => False

theorem spCompIdx_cases {d : TauCeti.LieTypeIndex} (h : SpCompIdx d) :
    (Bal207Index 3 d ∧ ¬ IsG2EightIndex d) ∨ IsSmallTwistedIdx d ∨ IsL2EightIndex d ∨
      IsSpFirstClaimIdx d := by
  cases d with
  | B s q =>
    obtain ⟨hq, hs, hne⟩ := h
    refine Or.inl ⟨⟨rfl, ?_⟩, fun h => h⟩
    rcases hq with hq | hq
    · exact Or.inl ⟨hq, by by_contra h3; exact hne ⟨by omega, hq⟩⟩
    · exact Or.inr ⟨hq, hs⟩
  | A r q => exact Or.inr (Or.inr (Or.inl h))
  | twistedA r q =>
    obtain ⟨hq, hr, hne⟩ := h
    by_cases h3 : 3 ∣ r + 1
    · by_cases h2 : r = 2
      · subst h2
        refine Or.inr (Or.inl ⟨rfl, Or.inr ?_⟩)
        exact hq.resolve_left fun h1 => hne ⟨rfl, h1⟩
      · by_cases h5 : r = 5 ∧ IsTwoPow q 1
        · exact Or.inl ⟨⟨rfl, Or.inr ⟨h5.2, h5.1⟩⟩, fun h => h⟩
        · refine Or.inr (Or.inr (Or.inr ⟨hq, h3, ?_, h5⟩))
          obtain ⟨c, hc⟩ := h3
          omega
    · exact Or.inl ⟨⟨rfl, Or.inl ⟨hq, h3⟩⟩, fun h => h⟩
  | _ => exact h.elim

theorem spCompType_psl2 {E : Type} [Field E] [Finite E] (hE : Nat.card E = 8) :
    SpCompType (Matrix.SpecialLinearGroup (Fin 2) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField E 2 3 (by norm_num)
    (by rw [hE]; norm_num)
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact Or.inr ⟨⟨.A 1 q, hv⟩, ⟨rfl, rfl, rfl⟩, ⟨eP.trans eC.symm⟩⟩

theorem spCompType_psp {E : Type} [Field E] [Finite E] {k s : ℕ} (hE : Nat.card E = 2 ^ k)
    (hk : k = 1 ∨ k = 3) (hs : 2 ≤ s) (hne : ¬(s = 2 ∧ k = 1)) :
    SpCompType (StatedProj (StatedSp s E)) := by
  have hk0 : 0 < k := by omega
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
  have hv : (TauCeti.LieTypeIndex.B s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨hs, fun h => hne ⟨h.1, ?_⟩⟩, fun h => ?_⟩
    · have h2 : q.card = 2 := h.2
      rw [TauCeti.PrimePower.card_def] at h2
      have h2' : 2 ^ k = 2 ^ 1 := h2
      exact Nat.pow_right_injective le_rfl h2'
    · have h3 : q.card = 3 := h.2
      rw [TauCeti.PrimePower.card_def] at h3
      have h3' : 2 ^ k = 3 := h3
      rcases hk with rfl | rfl <;> norm_num at h3'
  let d : TauCeti.ValidLieTypeIndex := ⟨.B s q, hv⟩
  obtain ⟨eT⟩ : Nonempty (d.Group ≃* StatedProj (StatedSp s ↥d.fixedField)) := by
    rcases (show s = 2 ∨ 3 ≤ s by omega) with rfl | hs3
    · exact ⟨CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv⟩
    · exact ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj s q hv rfl
        hs3⟩
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      TauCeti.ValidLieTypeIndex.card_fixedField, hE]
    simp only [d, q, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B,
      TauCeti.PrimePower.card_def]
  let φ : E ≃+* d.fixedField := FiniteField.ringEquivOfCardEq hcard
  let e₁ := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ s)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine Or.inr ⟨d, ⟨?_, hs, fun h => hne ⟨h.1, h.2.2⟩⟩, ⟨e₁.trans eT.symm⟩⟩
  rcases hk with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem spCompType_psu {E : Type} [Field E] [Finite E] {k m : ℕ}
    (hE : Nat.card E = (2 ^ k) ^ 2) (hk : k = 1 ∨ k = 3) (hm : 3 ≤ m)
    (hmq : (m, 2 ^ k) ≠ (3, 2)) :
    SpCompType (↥(StatedSU m (2 ^ k) E) ⧸ Subgroup.center ↥(StatedSU m (2 ^ k) E)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : 0 < k := by omega
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) hE hm hmq
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨by omega, fun hr => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 2 ^ k
    rcases hk with rfl | rfl
    · exact absurd (by subst hr; rfl) hmq
    · norm_num
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hE]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (r + 1) (2 ^ k)
  let eC := QuotientGroup.quotientMulEquivOfEq hQ.2
  refine Or.inr ⟨⟨.twistedA r q, hv⟩, ⟨?_, by omega, fun h => hmq ?_⟩,
    ⟨(eC.trans eP).trans e₀.symm⟩⟩
  · rcases hk with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · obtain ⟨h2, -, h1⟩ := h
    have : k = 1 := h1
    subst this h2
    rfl

theorem exists_psp_of_famSp {Y : Type} [Group Y] (h : IsLieQuot Y (FamSp 3)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (f r : ℕ), Nat.card F = 2 ^ f ∧ (f = 1 ∨ f = 3) ∧
      2 ≤ r ∧ ¬(r = 2 ∧ f = 1) ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSp r F)) := by
  obtain ⟨⟨d, hv⟩, ⟨hi, hsp⟩, ⟨e⟩⟩ := h
  cases d with
  | B r q =>
    obtain ⟨-, ⟨⟨hq2, hq1⟩, hr⟩ | ⟨⟨hq2, hq3⟩, hr⟩⟩ := hi
    ·
      let dv : TauCeti.ValidLieTypeIndex := ⟨.B r q, hv⟩
      haveI : Finite dv.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField dv
      refine ⟨dv.fixedField, inferInstance, inferInstance, 1, r, ?_, Or.inl rfl, by omega,
        by omega, ⟨e.trans
          (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr)⟩⟩
      rw [TauCeti.ValidLieTypeIndex.card_fixedField]
      simp only [dv, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B,
        TauCeti.PrimePower.card_def, hq2, hq1]
    ·
      let dv : TauCeti.ValidLieTypeIndex := ⟨.B r q, hv⟩
      haveI : Finite dv.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField dv
      have hcard : Nat.card dv.fixedField = 2 ^ 3 := by
        rw [TauCeti.ValidLieTypeIndex.card_fixedField]
        simp only [dv, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B,
          TauCeti.PrimePower.card_def, hq2, hq3]
      rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
      · exact ⟨dv.fixedField, inferInstance, inferInstance, 3, 2, hcard, Or.inr rfl, le_rfl,
          by omega, ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)⟩⟩
      · exact ⟨dv.fixedField, inferInstance, inferInstance, 3, r, hcard, Or.inr rfl, hr,
          by omega, ⟨e.trans
            (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2
              hr3)⟩⟩
  | _ => exact hsp.elim

end CFSG.HardMathSupport.Dickson.Bal207
