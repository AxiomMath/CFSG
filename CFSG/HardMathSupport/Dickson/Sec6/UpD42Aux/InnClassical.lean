module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Symp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly
public import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.TriD4 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem not_upD42Pumpup_of_componentsNoD4 {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hlayer : PerfectInLayer β) (hno : ComponentsNoD4 β) : ¬ UpD42Pumpup S β := by
  rintro ⟨-, -, I, hI, hD⟩
  obtain ⟨hcomp, hDI⟩ := exists_component_of_isD42_two hlayer hI hD
  exact hno I hcomp (card_centerQuotient_of_isD42 hDI)

theorem not_upD42Pumpup_innAutDerived_linear {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hp : q.p = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    {α : MulAut S} (hα : α ∈ innAutDerived S) : ¬ UpD42Pumpup S α := by
  intro hx
  obtain ⟨e⟩ := he
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp]
  have hno := componentsNoD4_projectiveSL (by omega) q.exponent_pos hK
    ((mem_innAutDerived_congr e').2 hα) (by rw [← map_pow, hx.1, map_one])
  have hlayer := lieSemisimpleCentLinearUnitary S hs hnab ⟨.A r q, hv⟩ rfl ⟨e⟩ 3
    Nat.prime_three (by norm_num) (by simpa using (show (3 : ℕ) ≠ q.p by omega))
    α hx.1 hx.2.1
  exact not_upD42Pumpup_of_componentsNoD4 hlayer (ComponentsNoD4.of_congr e' hno) hx

theorem not_upD42Pumpup_innAutDerived_unitary {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hp : q.p = 2)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    {α : MulAut S} (hα : α ∈ innAutDerived S) : ¬ UpD42Pumpup S α := by
  intro hx
  obtain ⟨e⟩ := he
  let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA r q, hv⟩
  obtain ⟨r', q', K, _, hU, hr, hd, hne, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := d) trivial
  have hp' : q'.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_twistedA r' q', ← hd]
    simpa only [d, TauCeti.LieTypeIndex.characteristic_twistedA] using hp
  have hq : ¬ (r' + 1 = 3 ∧ q'.p ^ q'.exponent = 2) := fun h =>
    hne ⟨h.1, (TauCeti.PrimePower.card_def q').trans h.2⟩
  let e' : S ≃* primeFormP hU (idGram K (r' + 1)) := e.trans eP.symm
  have hno := componentsNoD4_primeFormP hU (by omega) hq hp'
    ((mem_innAutDerived_congr e').2 hα) (by rw [← map_pow, hx.1, map_one])
  have hlayer := lieSemisimpleCentLinearUnitary S hs hnab d rfl ⟨e⟩ 3
    Nat.prime_three (by norm_num) (by
      simpa only [d, TauCeti.LieTypeIndex.characteristic_twistedA] using
        (show (3 : ℕ) ≠ q.p by omega)) α hx.1 hx.2.1
  exact not_upD42Pumpup_of_componentsNoD4 hlayer (ComponentsNoD4.of_congr e' hno) hx

theorem not_upD42Pumpup_conj_symplectic {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : isSymplecticIdx d.1)
    (hc : d.1.characteristic = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    (x : S) : ¬ UpD42Pumpup S (MulAut.conj x) := by
  intro hx
  haveI := hs
  obtain ⟨r, hr, -, -, ⟨eP⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  obtain ⟨e⟩ := he
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let e' : S ≃* StatedProj (StatedSp r ↥d.fixedField) := e.trans eP.symm
  have hK : Nat.card ↥d.fixedField = 2 ^ d.fieldExponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    change d.1.characteristic ^ d.fieldExponent = 2 ^ d.fieldExponent
    rw [hc]
  have hx3 : x ^ 3 = 1 := CFSG.mulAutConj_injective_of_center_eq_bot
    (up34_center_eq_bot_of_simple hnab) (by rw [map_pow, map_one]; exact hx.1)
  obtain ⟨y, hy, hy3⟩ := exists_proj_eq_pow_eq_one_sp (r := r) (K := ↥d.fixedField)
    (by omega) Nat.prime_three (by norm_num)
    (by rw [← map_pow, hx3, map_one] : (e' x) ^ 3 = 1)
  obtain ⟨hlayer, hno⟩ := layer_componentsNoD4_conj_statedSp (by omega)
    d.fieldExponent_pos hK y hy3
  rw [hy, ← CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj e' x] at hlayer hno
  exact not_upD42Pumpup_of_componentsNoD4
    (perfectInLayer_of_congr e' (MulAut.conj x) hlayer) (ComponentsNoD4.of_congr e' hno) hx

theorem upD42Chev2Inn_classical_holds : UpD42Chev2Inn KD.IsClassicalLieIndex := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  have hin : MulAut.conj x ∈ innAutDerived S := inner_le_innAutDerived S ⟨x, rfl⟩
  cases d with
  | A r q =>
    exact (not_upD42Pumpup_innAutDerived_linear hs hnab hv hc ⟨e⟩ hin hx).elim
  | twistedA r q =>
    exact (not_upD42Pumpup_innAutDerived_unitary hs hnab hv hc ⟨e⟩ hin hx).elim
  | B r q =>
    exact (not_upD42Pumpup_conj_symplectic hs hnab ⟨.B r q, hv⟩ (Or.inr hc)
      (by simpa only [TauCeti.LieTypeIndex.characteristic_B] using (show q.p = 2 from hc))
      ⟨e⟩ x hx).elim
  | C r q =>
    exact (not_upD42Pumpup_conj_symplectic hs hnab ⟨.C r q, hv⟩ trivial
      (by simpa only [TauCeti.LieTypeIndex.characteristic_C] using (show q.p = 2 from hc))
      ⟨e⟩ x hx).elim
  | D r q =>
    exact upD42Chev2Inn_orthogonal_holds S hs hnab ⟨.D r q, hv⟩ trivial hc ⟨e⟩ x hx
  | twistedD r q =>
    exact upD42Chev2Inn_orthogonal_holds S hs hnab ⟨.twistedD r q, hv⟩ trivial hc ⟨e⟩ x hx
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
