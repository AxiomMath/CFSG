module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.HardMathSupport.Curtis.Proving.ToralCaseSplit
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar

theorem isLocallyBalancedAbs_primeFormP {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (h32 : ¬(p = 3 ∧ ℓ ^ f = 2)) :
    IsLocallyBalancedAbs p 3 (primeFormP h (idGram K n)) := by
  intro D hD hcard H hH _
  obtain ⟨E, hED, hEin, hE, hEc⟩ :=
    exists_inner_plane_primeFormP h isPrimeFormGram_idGram hn hne hp hpg D hD hcard
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE.2 x x.2) }
  have hbot := localDeltaIn_eq_bot_primeFormP h hn hne hp hp2 hpℓ hpg h32 E hEin hEel hEc hH
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)

@[expose] def regimeTwistedA (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧
    ¬ (p ∣ q.card + 1 ∧ p ∣ r + 1) ∧ ¬ (p = 3 ∧ q.card = 2)

theorem crossCharFamAt_twistedA : CrossCharFamAt .twistedA regimeTwistedA := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, h1, h2⟩
  change d = _ at hd
  subst hd
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : Cat ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpg : ¬ p ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := fun hd =>
    h1 ⟨by rw [hcard]; exact hd.trans (Nat.gcd_dvd_right _ _), hd.trans (Nat.gcd_dvd_left _ _)⟩
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_primeFormP h (by omega) hq' hp hp2 hpq hpg (by rwa [← hcard]))

theorem crossCharFamCat_twistedA_of_residual
    (h : CrossCharFamAt .twistedA fun idx p => ¬ regimeTwistedA idx p) :
    CrossCharFamCat .twistedA :=
  crossCharFamCat_of_at regimeTwistedA crossCharFamAt_twistedA h

@[expose] def regimeTwistedADiag (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p ∣ q.card + 1 ∧ p ∣ r + 1

@[expose] def regimeTwistedAThreeTwo (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA r q ∧ p = 3 ∧ q.card = 2

theorem not_regimeTwistedA_iff {idx : TauCeti.ValidLieTypeIndex}
    (hk : LieFamily.twistedA.Matches idx.1) {p : ℕ} :
    ¬ regimeTwistedA idx p ↔ regimeTwistedADiag idx p ∨ regimeTwistedAThreeTwo idx p := by
  obtain ⟨r, q, hd⟩ := hk
  constructor
  · intro h
    by_cases h1 : p ∣ q.card + 1 ∧ p ∣ r + 1
    · exact Or.inl ⟨r, q, hd, h1⟩
    · refine Or.inr ⟨r, q, hd, ?_⟩
      by_contra h2
      exact h ⟨r, q, hd, h1, h2⟩
  · rintro (⟨r', q', hd', h1⟩ | ⟨r', q', hd', h2⟩) ⟨r'', q'', hd'', h1', h2'⟩
    · obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj (hd'.symm.trans hd'')
      exact h1' ⟨h1.1, h1.2⟩
    · obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj (hd'.symm.trans hd'')
      exact h2' h2

theorem crossCharFamAt_not_regimeTwistedA_iff :
    (CrossCharFamAt .twistedA fun idx p => ¬ regimeTwistedA idx p) ↔
      CrossCharFamAt .twistedA regimeTwistedADiag ∧
        CrossCharFamAt .twistedA regimeTwistedAThreeTwo := by
  constructor
  · intro h
    exact ⟨fun idx hk p hp hp2 hc hr =>
        h idx hk p hp hp2 hc ((not_regimeTwistedA_iff hk).2 (Or.inl hr)),
      fun idx hk p hp hp2 hc hr =>
        h idx hk p hp hp2 hc ((not_regimeTwistedA_iff hk).2 (Or.inr hr))⟩
  · rintro ⟨h1, h2⟩ idx hk p hp hp2 hc hr
    rcases (not_regimeTwistedA_iff hk).1 hr with hr | hr
    · exact h1 idx hk p hp hp2 hc hr
    · exact h2 idx hk p hp hp2 hc hr

theorem crossCharFamCat_twistedA_of_diag
    (hdiag : CrossCharFamAt .twistedA regimeTwistedADiag)
    (h32 : CrossCharFamAt .twistedA regimeTwistedAThreeTwo) : CrossCharFamCat .twistedA :=
  crossCharFamCat_twistedA_of_residual (crossCharFamAt_not_regimeTwistedA_iff.2 ⟨hdiag, h32⟩)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
