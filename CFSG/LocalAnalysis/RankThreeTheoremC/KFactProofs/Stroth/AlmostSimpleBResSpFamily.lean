module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResSpOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLeaves

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem fixesPair_of_spModel {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (eL : L ≃* StatedProj (StatedSp n K)) {α : MulAut L}
    (hα : α ∉ inner L) (hαp : α ^ p = 1) : FixesIndepPair p α := by
  obtain ⟨-, hge⟩ := rank_data_of_pRank hp hrk eL
  have h := sp_outer_fixesPair hn hp hp2 hge (α := MulAut.congr eL α)
    ((congr_mem_inner_iff eL α).not.2 hα) (by rw [← map_pow, hαp, map_one])
  exact FixesIndepPair.of_mulEquiv eL h

theorem chevTwoOuterFixesPair_sp : ChevTwoOuterFixesPair LieIndexSp := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | B r q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hq2 : q.p = 2 := hchar
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr2 : 2 ≤ r := hrange.1
    haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B r q, hv⟩
    haveI : CharP (TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) 2 := by
      have h0 : CharP (TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)
        (TauCeti.ValidLieTypeIndex.characteristic ⟨.B r q, hv⟩) := inferInstance
      have e1 : TauCeti.ValidLieTypeIndex.characteristic ⟨.B r q, hv⟩ = 2 := by
        change (TauCeti.LieTypeIndex.B r q).characteristic = 2
        rw [TauCeti.LieTypeIndex.characteristic_B]
        exact hq2
      exact CharP.congr _ e1
    by_cases hr : r = 2
    · subst hr
      exact fixesPair_of_spModel hp hp2 hrk le_rfl
        (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)) hα hαp
    · exact fixesPair_of_spModel hp hp2 hrk (by omega)
        (e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv
          hq2 (by omega))) hα hαp
  | C r q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hq2 : q.p = 2 := hchar
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr3 : 3 ≤ r := hrange.1
    haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
    haveI : CharP (TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) 2 := by
      have h0 : CharP (TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩)
        (TauCeti.ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩) := inferInstance
      have e1 : TauCeti.ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩ = 2 := by
        change (TauCeti.LieTypeIndex.C r q).characteristic = 2
        rw [TauCeti.LieTypeIndex.characteristic_C]
        exact hq2
      exact CharP.congr _ e1
    exact fixesPair_of_spModel hp hp2 hrk (by omega)
      (e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)) hα hαp
  | A _ _ => exact absurd hF (by simp [LieIndexSp])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexSp])
  | D _ _ => exact absurd hF (by simp [LieIndexSp])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexSp])
  | E6 _ => exact absurd hF (by simp [LieIndexSp])
  | E7 _ => exact absurd hF (by simp [LieIndexSp])
  | E8 _ => exact absurd hF (by simp [LieIndexSp])
  | F4 _ => exact absurd hF (by simp [LieIndexSp])
  | G2 _ => exact absurd hF (by simp [LieIndexSp])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexSp])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexSp])
  | suzuki _ => exact absurd hF (by simp [LieIndexSp])
  | reeG2 _ => exact absurd hF (by simp [LieIndexSp])
  | reeF4 _ => exact absurd hF (by simp [LieIndexSp])
  | tits => exact absurd hF (by simp [LieIndexSp])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
