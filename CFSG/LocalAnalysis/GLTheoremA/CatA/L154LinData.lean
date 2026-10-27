module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLinMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MICore
public import CFSG.Adapters.LinearCatalog
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinMark
open scoped commutatorElement MatrixGroups

theorem exists_psl_of_l154Lin {T : Type} [Group T] (h : catalogIs T l154Lin) :
    ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ m ∧
      Nonempty (T ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [l154Lin, onLie] at hi
  | alternating n hn => simp [l154Lin, onLie] at hi
  | sporadic s => simp [l154Lin, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | A r q =>
      have hq : q.p = 2 := by simpa [l154Lin, onLie] using hi
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      haveI : NeZero q.exponent := ⟨Nat.pos_iff_ne_zero.1 q.exponent_pos⟩
      have hr : 1 ≤ r :=
        ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      refine ⟨r + 1, q.exponent, GaloisField q.p q.exponent, inferInstance, inferInstance, by omega, ?_,
        ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (r + 1)
            (GaloisField q.p q.exponent))⟩⟩
      rw [GaloisField.card q.p q.exponent (Nat.pos_iff_ne_zero.1 q.exponent_pos), hq]
    | _ => simp [l154Lin, onLie] at hi

theorem famLin_of_canon {lab : GLALabel} {a m : ℕ} (h : canonLabel lab = ⟨.A, a, m⟩) : FamLin lab := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals first
    | exact Or.inl rfl
    | (simp [canonLabel] at h; done)
    | skip
  · by_cases h3 : rank = 3
    · exact Or.inr (Or.inl ⟨rfl, h3⟩)
    · simp [canonLabel, h3] at h
  · by_cases h3 : rank = 3
    · simp [canonLabel, h3] at h
    · by_cases h2 : rank = 2
      · exact Or.inr (Or.inr ⟨rfl, h2⟩)
      · simp [canonLabel, h3, h2] at h

theorem lin_data_transport {L : Type} [Group L] {d : ℕ} {K : Type} [Field K]
    {H : Subgroup (GL (Fin d) K)} (hH : H = StatedSL d K)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj H) (rx ry : L → L → Prop)
    (φx u f : MulAut (LargeEvenProj H)) (A U : GL (Fin d) K) (σ : K ≃+* K)
    (hA : ∀ h h' : ↥H, (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φx (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hU : ∀ h h' : ↥H, (h' : GL (Fin d) K) = U * (h : GL (Fin d) K) * U⁻¹ →
      u (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hfσ : ∀ h h' : ↥H, ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ →
      f (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hindx : LargeEvenInduces θ rx φx) (hindy : LargeEvenInduces θ ry (u * f * u⁻¹)) :
    ∃ (θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (StatedSL d K)) (B : GL (Fin d) K)
      (φx' ψ : MulAut (LargeEvenProj (StatedSL d K))),
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        φx' (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ g g' : ↥(StatedSL d K), (g' : GL (Fin d) K) = B * glMap σ (g : GL (Fin d) K) * B⁻¹ →
        ψ (LargeEvenProjMk (StatedSL d K) g) = LargeEvenProjMk (StatedSL d K) g') ∧
      LargeEvenInduces θ' rx φx' ∧ LargeEvenInduces θ' ry ψ := by
  subst hH
  refine ⟨θ, U * glMap σ U⁻¹, φx, u * f * u⁻¹, hA, ?_, hindx, hindy⟩
  intro g g' hg'
  have hnorm : (StatedSL d K).Normal := inferInstance
  have hg1 : U⁻¹ * (g : GL (Fin d) K) * U ∈ StatedSL d K := by
    have := hnorm.conj_mem _ g.2 U⁻¹
    simpa using this
  have hg2 : glMap σ (U⁻¹ * (g : GL (Fin d) K) * U) ∈ StatedSL d K := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hg1 ⊢
    rw [det_glMap, hg1, map_one]
  have h1 : u⁻¹ (LargeEvenProjMk (StatedSL d K) g) =
      LargeEvenProjMk (StatedSL d K) ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩ := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    symm
    exact hU ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩ g (by simp [mul_assoc])
  have h2 : f (LargeEvenProjMk (StatedSL d K) ⟨U⁻¹ * (g : GL (Fin d) K) * U, hg1⟩) =
      LargeEvenProjMk (StatedSL d K) ⟨glMap σ (U⁻¹ * (g : GL (Fin d) K) * U), hg2⟩ :=
    hfσ _ _ (by rw [coe_glMap])
  have h3 : u (LargeEvenProjMk (StatedSL d K) ⟨glMap σ (U⁻¹ * (g : GL (Fin d) K) * U), hg2⟩) =
      LargeEvenProjMk (StatedSL d K) g' := by
    refine hU _ g' ?_
    rw [hg']
    show _ = U * glMap σ (U⁻¹ * (g : GL (Fin d) K) * U) * U⁻¹
    rw [map_mul, map_mul, map_inv]
    group
  show u (f (u⁻¹ (LargeEvenProjMk (StatedSL d K) g))) = _
  rw [h1, h2, h3]

section Certs


theorem lin_marking_data (hLD : Y10GInnLin.LinLabelDict) {p : ℕ} (hp : p.Prime)
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    (hQ : catalogIs (PSimple p S) l154Lin)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hF : FieldOn p y S) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (θ : PSimple p S ≃* LargeEvenProj (StatedSL d K))
      (A B : GL (Fin d) K) (σ : K ≃+* K) (φx ψ : MulAut (LargeEvenProj (StatedSL d K))),
      2 ≤ d ∧ (2 : K) = 0 ∧ σ ≠ 1 ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        φx (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ g g' : ↥(StatedSL d K), (g' : GL (Fin d) K) = B * glMap σ (g : GL (Fin d) K) * B⁻¹ →
        ψ (LargeEvenProjMk (StatedSL d K) g) = LargeEvenProjMk (StatedSL d K) g') ∧
      LargeEvenInduces θ (indRel p S x) φx ∧ LargeEvenInduces θ (indRel p S y) ψ := by
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p S)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p S x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hInn.2
  have h1 := CFSG.LocalAnalysis.GLTheoremA.MI.marking_transport (indRel p S x) hdiag hF.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := h1
  have hlab : HasLabel (PQuot p S) (fun l : GLALabel => l = lab) :=
    ⟨hperf, lab, hΛ, Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨a, m, E, hEf, hEfin, ha, hE, ⟨e⟩⟩ := exists_psl_of_l154Lin hQ
  have hcanon := hLD (PQuot p S) lab a m E ha hE hlab ⟨e⟩
  have hfam := famLin_of_canon hcanon
  obtain ⟨d, m0, hd, hm0, hiff⟩ := famLin_recipe hΛ hfam
  obtain ⟨K, instF, instFin, hK, hs, hna, θ, ⟨hlt, f, hf, u, hu, hord, hindy⟩, φx, hφx, hindx⟩ :=
    (hiff _).1 hraw
  haveI : CharP K 2 := charP_two_of_card_pow hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨A, -, hA⟩ := hφx
  obtain ⟨U, -, hU⟩ := hu
  obtain ⟨σ, hfσ⟩ := hf
  have hσ : σ ≠ 1 := by
    rintro rfl
    have hf1 : f = 1 := MulEquiv.ext (fld_fix_of_one f hfσ)
    rw [hf1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨θ', B, φx', ψ, hA', hψ, hix, hiy⟩ := lin_data_transport
    (largeEvenSLGroup_eq_statedSL (K := K) d) θ (indRel p S x) (indRel p S y) φx u f A U σ hA hU hfσ hindx hindy
  exact ⟨d, K, instF, instFin, θ', A, B, σ, φx', ψ, hd, h2, hσ, hA', hψ, hix, hiy⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.K155X
