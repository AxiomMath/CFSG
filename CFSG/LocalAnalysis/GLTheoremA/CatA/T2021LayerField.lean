module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal
import CFSG.LocalAnalysis.StandardType.GGInndiagCommRest
import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPFieldN
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPMI
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphPlanes
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
import CFSG.LieType.SeitzGeneration.OuterSpPair
import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
import CFSG.LieType.SeitzGeneration.RootPairSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA.FR CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.ComponentClassification.OuterAutomorphisms

section D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

theorem t2021Layer_d4_field_not_mem (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p ≠ 1)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))))
    (hord : orderOf f = p) :
    f ∉ innAutDerived (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) := by
  obtain ⟨σ, hσ⟩ := hf
  have hcongr : MulAut.congr (isoAdj K) f = entrywiseAdjointAut Tag.D4 σ := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨c, rfl⟩ := (isoAdj K).surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have h1 : f (QuotientGroup.mk x) = QuotientGroup.mk (sigmaOmega σ x) :=
      hσ x (sigmaOmega σ x) (val_sigmaOmega σ x)
    show (isoAdj K) (f ((isoAdj K).symm ((isoAdj K) (QuotientGroup.mk x)))) = _
    rw [MulEquiv.symm_apply_apply, h1, isoAdj_mk, isoAdj_mk, thetaOmega_sigmaOmega]
  intro hmem
  have hmem' : MulAut.congr (isoAdj K) f ∈ innAutDerived (adjointGroup Tag.D4 K) :=
    (mem_innAutDerived_congr (isoAdj K)).2 hmem
  have hker : innAutDerived (adjointGroup Tag.D4 K) ≤ (fieldPart :
      MulAut (adjointGroup Tag.D4 K) →* (K ≃+* K)).ker :=
    sup_le (by rintro _ ⟨g, rfl⟩; exact fieldPart_conj g)
      (fun η hη => fieldPart_eq_one_of_mem_commutator hη)
  have h1 : fieldPart (MulAut.congr (isoAdj K) f) = 1 := hker hmem'
  have hσ1 : σ = 1 := by
    rw [hcongr, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.entrywiseAdjointAut_D4_eq,
      ← mul_one (exactNormalAut Tag.D4 K 1 σ 0),
      ← CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero (K := K), fieldPart_normalForm] at h1
    exact h1
  subst hσ1
  have hf1 : f = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have := hσ x x (by ext i j; rfl)
    simpa using this
  rw [hf1, orderOf_one] at hord
  exact hp hord.symm

end D4

section Field

theorem t2021Layer_field_not_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    CAll lab (LargeEvenSimpleGuard fun R _ _ F => ∀ f ∈ F, orderOf f = p → f ∉ innAutDerived R) := by
  by_cases hD4 : lab.tag = .D ∧ lab.rank = 4
  · obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hl⟩ := hD4
    dsimp only at ht hl
    subst ht hl
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GClsOrth.canonicalLabelAll_omegaPlus rfl le_rfl
      fun K _ _ _ _ _ _ f hf hord => t2021Layer_d4_field_not_mem K hp.ne_one hf hord
  by_cases hsmall : lab.tag = .B2der ∨ DerivedLab lab
  · have hn : lab.n = 1 := by
      obtain ⟨t, l, n⟩ := lab
      rcases hsmall with h | h | h <;> (simp only at h; subst h; exact hlab.2.2)
    have hdeg : CFSG.LocalAnalysis.GLTheoremA.FP.fieldDeg lab = 1 := by
      obtain ⟨t, l, n⟩ := lab
      simp only at hn
      subst hn
      rcases hsmall with h | h | h <;> (simp only at h; subst h; rfl)
    refine CAll.mono ?_ (CFSG.LocalAnalysis.GLTheoremA.FP.canonFieldDeg hlab)
    intro R _ I F hF _ _ f hf hord
    have h1 := hF f hf
    rw [hdeg, hord] at h1
    exact absurd (Nat.dvd_one.1 h1) hp.ne_one
  have hnd : ¬ DerivedLab lab := fun h => hsmall (Or.inr h)
  have hne : ¬ GGInndiagCommExclLabel lab := by
    rintro (h | h)
    · exact hD4 h
    · exact hsmall (Or.inl h)
  have hall : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    by_cases hP : GGInndiagCommProvedLabel lab
    · exact largeEvenLabelAll_inndiagComm_proved hlab hP
    · exact ggInndiagCommRestInput_holds lab hlab hne hP
  have hcomm := (canonAll_iff_legacyAll hlab hnd _).2 hall
  refine CAll.mono ?_ ((canonRawInn hp hp2 hlab).and hcomm)
  rintro R _ I F ⟨hInn, hEq⟩ hs hna f hf hord hmem
  obtain ⟨hImul, hIinv, hIconj, hFI⟩ := hInn hs hna
  let J : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun ha hb => hImul _ ha _ hb
      one_mem' := by simpa using hIconj 1
      inv_mem' := fun ha => hIinv _ ha }
  have hle : innAutDerived R ≤ J := by
    rw [← ggInndiagComm_eq_innAutDerived, ← hEq hs hna]
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hIconj r
    · rw [Subgroup.closure_le]
      exact fun x hx => hx
  exact hFI f hf hord (hle hmem)

theorem t2021Layer_not_mem {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (Q ⧸ Subgroup.center Q)}
    (ha : GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (· = MulAut.congr θ α)) :
    orderOf α = p ∧ α ∉ innAutDerived (Q ⧸ Subgroup.center Q) := by
  obtain ⟨-, lab, hlab, hraw⟩ := ha
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, ⟨-, f, hfF, u, -, hfp, hind⟩⟩, hnot⟩⟩ :=
    Canonical.largeEvenRawDatum_exists (t2021Layer_field_not_mem hp hp2 hlab _ hraw)
  have hord : orderOf α = p := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj u) f
    rw [MulAut.conj_apply, hind, MulEquiv.orderOf_eq] at h1
    rw [h1, hfp]
  refine ⟨hord, fun hmem => ?_⟩
  have h1 : MulAut.congr θ α ∈ innAutDerived R := (mem_innAutDerived_congr θ).2 hmem
  rw [← hind] at h1
  have h2 : f ∈ innAutDerived R := by
    have := (innAutDerived_normal R).conj_mem _ h1 u⁻¹
    simpa [mul_assoc] using this
  exact hnot hs hna f hfF hfp h2

end Field

section Subfield

theorem t2021Layer_subfield {Q : Type} [Group Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (Q ⧸ Subgroup.center Q)}
    (ha : GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (· = MulAut.congr θ α)) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) ∧
      MarkedModel lab (Q ⧸ Subgroup.center Q) ∧ p ∣ lab.n ∧
      ∃ D : Subgroup (Q ⧸ Subgroup.center Q), SubfieldGrp α D ∧
        (CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩
            (fun R' _ _ _ => Nonempty (↥D ≃* R')) ∨ SubfieldExc p lab D) := by
  have h := CFSG.LocalAnalysis.GLTheoremA.FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I F => ¬ (lab.tag = .triD4 ∧ p = 3) → SubfieldBody p lab R I F)
    (fun lab hlab => by
      by_cases h3 : lab.tag = .triD4 ∧ p = 3
      · exact (canonRawInnAny hp.ne_one hlab).mono fun R _ I F _ hs hna h => absurd h3 h
      · exact (canonSubfield hp hp2 hlab h3).mono fun R _ I F h' hs hna _ => h' hs hna) ha
  obtain ⟨lab, hlab, R, _, I, F, θ, hs, hna, ⟨hP, hSub⟩, hM⟩ :=
    Canonical.largeEvenMarking_exists_markedModel h
  obtain ⟨hne, f, hf, u, hu, hord, he⟩ := hP
  have h3 : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, h'⟩
    rcases hne with h0 | h0
    · exact h0 h
    · exact h0 h'
  obtain ⟨hpn, D, hD, hdat⟩ := hSub h3 f hf hord
  have hDu : SubfieldGrp (u * f * u⁻¹) (D.map (u : R ≃* R).toMonoidHom) :=
    subfieldGrp_map (u : R ≃* R) (fun x => by simp) hD
  have hDS : SubfieldGrp α ((D.map (u : R ≃* R).toMonoidHom).map θ.symm.toMonoidHom) := by
    refine subfieldGrp_map θ.symm (f := u * f * u⁻¹) (fun x => ?_) hDu
    rw [he]
    simp [MulAut.congr_apply]
  have eD : ↥((D.map (u : R ≃* R).toMonoidHom).map θ.symm.toMonoidHom) ≃* ↥D :=
    (equivMapEquiv θ.symm _).symm.trans (equivMapEquiv (u : R ≃* R) D).symm
  refine ⟨lab, hlab, h3, MarkedModel.of_mulEquiv θ.symm hM, hpn, _, hDS, ?_⟩
  rcases hdat with hdat | hexc
  · exact Or.inl (Canonical.largeEvenRawDatum_mono (fun R' _ I' F' ⟨e⟩ => ⟨eD.trans e⟩) hdat)
  · refine Or.inr ?_
    rcases hexc with ⟨h1, h2, h4⟩ | h5
    · exact Or.inl ⟨h1, h2, Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom)
        eD.injective⟩
    · exact Or.inr h5

end Subfield

section TwF4

open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA.FR.Res

theorem t2021Layer_twF4Core {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel S .twistedF4 0 2 p) {β : MulAut S} (hβord : orderOf β = p)
    (hβi : β ∉ (MulAut.conj : S →* MulAut S).range) : CoreSub (FP.fixSub β) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hadm, a, hfa, K, _, _, hK, ⟨e0⟩⟩ := hL.reeTitsModel (by simp [reeTitsTags])
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      exact absurd hfa (by simpa using hp.ne_one)
    · exact h0
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ := ree_fix_equiv ha hK' hp hp2 e0 β hβord hβi
  have hb0 : b₀ = 0 := by
    have h1 : (2 * b₀ + 1) * p = 1 * p := by rw [hb, hfa, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have hC : DatumCore ↥(FP.fixSub β) := datumCore_of_equiv eF (datumCore_reeGamma_zero hk2)
  exact coreSub_of_subfield ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl,
    by rw [Subgroup.relIndex_self]; exact odd_one⟩ hC

end TwF4

section Core

theorem t2021Layer_coreSub {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (Q ⧸ Subgroup.center Q)}
    (ha : GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (· = MulAut.congr θ α))
    (hT : ∃ T : Subgroup (Q ⧸ Subgroup.center Q), T ≤ FP.fixSub α ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) :
    CoreSub (FP.fixSub α) := by
  obtain ⟨lab, hlab, h3, hM, hpn, D, hD, hdat⟩ := t2021Layer_subfield hp hp2 ha
  obtain ⟨T, hTC, hTp, hTne⟩ := hT
  have hTD : T ≤ D := hTp ▸ (Subgroup.commutator_mono hTC hTC).trans hD.2.1
  have hna := exists_noncomm_of_perfect hTD hTp hTne
  rcases hdat with hdat | hexc
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩
    · have hG : lab.tag ≠ .G2der := by
        intro h
        obtain ⟨t, r, n⟩ := lab
        dsimp only at h hpn hlab
        subst h
        have : n = 1 := hlab.2.2
        rw [this] at hpn
        exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
      have hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Nonempty (↥D ≃* R) →
          ∃ a b : R, a * b ≠ b * a := fun R _ I F ⟨e⟩ => by
        obtain ⟨x, y, h⟩ := hna
        exact ⟨e x, e y, fun h' => h (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
      obtain ⟨R', _, I', F', ⟨e'⟩, hMR⟩ :=
        Canonical.largeEvenRawDatum_exists (Canonical.largeEvenRawDatum_markedModel hΛ hQ hdat)
      obtain ⟨hs, hch⟩ := simple_chev_of_markedModel (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hG
        (MarkedModel.of_mulEquiv e'.symm hMR)
      exact coreSub_of_subfield hD (datumCore_of_simple hs hna hch)
    · rcases CFSG.LocalAnalysis.GLTheoremA.FR.Res.smallDatum_holds p lab ↥D hp hlab hpn hΛ hdat with
        hsol | hC
      · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
      · exact coreSub_of_subfield hD hC
  · rcases hexc with ⟨htag, hn, hsol⟩ | ⟨htag, hn⟩
    · exact (false_of_perfect_solvable hTD hTp hTne hsol).elim
    · obtain ⟨hord, hnot⟩ := t2021Layer_not_mem hp hp2 ha
      have hL : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .twistedF4 0 2 p := by
        obtain ⟨t, r, n⟩ := lab
        dsimp only at htag hn
        subst htag hn
        exact hM
      exact t2021Layer_twF4Core hp hp2 hL hord fun hinn => hnot (inner_le_innAutDerived _ hinn)

end Core

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
