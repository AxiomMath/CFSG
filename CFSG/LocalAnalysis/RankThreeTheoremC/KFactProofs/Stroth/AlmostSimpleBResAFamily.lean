module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPSL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBFamilies

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LieType.SeitzGeneration (RankLE2)

@[expose] def ChevTwoOuterFixesPair (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (L : Type) [Group L] [Finite L],
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
    (∃ d : TauCeti.ValidLieTypeIndex, IsChevIndexTwo d.1 ∧ F d.1 ∧
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ¬ (p = 3 ∧ IsLThreeTwo L) →
    ∀ α : MulAut L, α ∉ inner L → α ^ p = 1 → FixesIndepPair p α

section Transfer

variable {L : Type} [Group L] [Finite L] {p : ℕ}

theorem rank_data_of_pRank {P : Type} [Group P] (hp : p.Prime)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) (eL : L ≃* P) :
    RankLE2 p P ∧ ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  refine ⟨RankLE2.of_mulEquiv eL (RankLE2.of_pRank hp hrk.le), ?_⟩
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_pRank_eq_two hp hrk
  refine ⟨E.map eL.toMonoidHom, CFSG.Open.IsElemAbelian.map hE eL.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective eL.injective]
  exact hEc

theorem fixesPair_catA (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) {r : ℕ} {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) (hne : ¬ (p = 3 ∧ IsLThreeTwo L))
    {α : MulAut L} (hα : α ∉ inner L) (hαp : α ^ p = 1) : FixesIndepPair p α := by
  classical
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq2
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr1 : 1 ≤ r := hrange.1
  let eL : L ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  obtain ⟨hle, hge⟩ := rank_data_of_pRank hp hrk eL
  by_cases hr : r = 1
  · subst hr
    exfalso
    obtain ⟨E, hE, hEc⟩ := hge
    exact false_of_elemAbelian_sq_projectiveSL_two hp hp2 hE hEc
  · have hn3 : 3 ≤ r + 1 := by omega
    have hnp : ¬ (r + 1 = 3 ∧ p = 3) := by
      rintro ⟨h3, rfl⟩
      obtain rfl : r = 2 := by omega
      exact hne ⟨rfl, q, hq2, Or.inl ⟨hv, ⟨e⟩⟩⟩
    have h := linear_outer_fixesPair hn3 hp hp2 hnp hle hge (α := MulAut.congr eL α)
      ((congr_mem_inner_iff eL α).not.2 hα) (by rw [← map_pow, hαp, map_one])
    exact FixesIndepPair.of_mulEquiv eL h

theorem fixesPair_catTwistedA (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) = 2) {r : ℕ} {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hne : ¬ (p = 3 ∧ IsLThreeTwo L)) {α : MulAut L} (hα : α ∉ inner L) (hαp : α ^ p = 1) :
    FixesIndepPair p α := by
  classical
  have hr2 : 2 ≤ r := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  have hq : ¬ (r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
      hmodel
  let eL : L ≃* primeFormP hU (idCn (r + 1) K) := e.trans eP
  obtain ⟨hle, hge⟩ := rank_data_of_pRank hp hrk eL
  have hn3 : 3 ≤ r + 1 := by omega
  have hnp : ¬ (r + 1 = 3 ∧ p = 3) := by
    rintro ⟨h3, rfl⟩
    obtain rfl : r = 2 := by omega
    exact hne ⟨rfl, q, hq2, Or.inr ⟨hv, ⟨e⟩⟩⟩
  have hpℓ : p ≠ q.p := by rw [hq2]; exact hp2
  have h := unitary_outer_fixesPair hU hn3 hq hp hp2 hpℓ hnp hle hge (α := MulAut.congr eL α)
    ((congr_mem_inner_iff eL α).not.2 hα) (by rw [← map_pow, hαp, map_one])
  exact FixesIndepPair.of_mulEquiv eL h

end Transfer

theorem chevTwoOuterFixesPair_A : ChevTwoOuterFixesPair LieFamilyA := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hfam, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact fixesPair_catA hp hp2 hrk hchar hv e hne hα hαp
  | twistedA r q => exact fixesPair_catTwistedA hp hp2 hrk hchar hv e hne hα hαp
  | B _ _ => exact absurd hfam (by simp [LieFamilyA])
  | C _ _ => exact absurd hfam (by simp [LieFamilyA])
  | D _ _ => exact absurd hfam (by simp [LieFamilyA])
  | twistedD _ _ => exact absurd hfam (by simp [LieFamilyA])
  | E6 _ => exact absurd hfam (by simp [LieFamilyA])
  | E7 _ => exact absurd hfam (by simp [LieFamilyA])
  | E8 _ => exact absurd hfam (by simp [LieFamilyA])
  | F4 _ => exact absurd hfam (by simp [LieFamilyA])
  | G2 _ => exact absurd hfam (by simp [LieFamilyA])
  | twistedE6 _ => exact absurd hfam (by simp [LieFamilyA])
  | trialityD4 _ => exact absurd hfam (by simp [LieFamilyA])
  | suzuki _ => exact absurd hfam (by simp [LieFamilyA])
  | reeG2 _ => exact absurd hfam (by simp [LieFamilyA])
  | reeF4 _ => exact absurd hfam (by simp [LieFamilyA])
  | tits => exact absurd hfam (by simp [LieFamilyA])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
