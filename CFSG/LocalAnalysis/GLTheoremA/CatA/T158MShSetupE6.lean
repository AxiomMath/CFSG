module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6F
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
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
import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
import CFSG.Goldschmidt.Steps.G37Transport
import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacF4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
import Certificates.Certificate10050
import Certificates.Certificate8117

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly CFSG.StandardType
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def T158CompE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G),
    PreSetup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧
      (i = .E6 q ∨ i = .twistedE6 q)) →
    (CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧ ¬ InducesInnerMod 3 L d

section Glue


variable {G : Type} [Group G] [Finite G]

private theorem indAut_mul {p : ℕ} {L : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (k : ℤ) :
    MI.indAut p L ((x * y) ^ k) (Subgroup.zpow_mem _ (Subgroup.mul_mem _ hx hy) k) =
      (MI.indAut p L y hy * MI.indAut p L x hx) ^ k := by
  unfold MI.indAut
  rw [← map_mul, ← map_zpow]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
  rw [← inv_zpow, mul_inv_rev]

theorem innDiagOn_zpowers_mul {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    (hchev : IsChevSimple 2 (PSimple 3 L)) {x y : G} (hx : InnDiagOn 3 (Subgroup.zpowers x) L)
    (hy : InnDiagOn 3 (Subgroup.zpowers y) L) : InnDiagOn 3 (Subgroup.zpowers (x * y)) L := by
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hx.1 (Subgroup.mem_zpowers x)
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hy.1 (Subgroup.mem_zpowers y)
  refine ⟨Subgroup.zpowers_le.2 (Subgroup.mul_mem _ hxN hyN), ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have h0 := CFSG.StandardType.ChevTwo.ys08_holds (PQuot 3 L) hq hchev
  have h1 := MI.canon_marking_and_labelAll_simple (P' := MI.RawInnBody 3)
    (fun lab hlab => MI.canonRawInn' Nat.prime_three (by norm_num) hlab) h0
  have hxm : CFSG.Assembly.LargeEvenMarking (PQuot 3 L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel 3 L x) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh x (Subgroup.mem_zpowers x)) hx.2
  have hym : CFSG.Assembly.LargeEvenMarking (PQuot 3 L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel 3 L y) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh y (Subgroup.mem_zpowers y)) hy.2
  have h2 := MI.marking_transport (indRel 3 L y) hym (MI.marking_transport (indRel 3 L x) hxm h1)
  refine Canonical.largeEvenMarking_mono ?_ h2
  rintro lab R _ I F θ ⟨⟨⟨-, hmul, hinv, hinn, -⟩, φx, hφx, hindx⟩, φy, hφy, hindy⟩ a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have ex : φx = MulAut.congr θ (MI.indAut 3 L x hxN) := (MI.induces_indRel_iff hxN θ).1 hindx
  have ey : φy = MulAut.congr θ (MI.indAut 3 L y hyN) := (MI.induces_indRel_iff hyN θ).1 hindy
  let SI : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun ha hb => hmul _ ha _ hb
      one_mem' := by simpa using hinn 1
      inv_mem' := fun ha => hinv _ ha }
  have hk : (x * y) ^ k ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpow_mem _ (Subgroup.mul_mem _ hxN hyN) k
  refine ⟨MulAut.congr θ (MI.indAut 3 L ((x * y) ^ k) hk), ?_, (MI.induces_indRel_iff hk θ).2 rfl⟩
  rw [indAut_mul hxN hyN k, map_zpow, map_mul, ← ex, ← ey]
  exact SI.zpow_mem (SI.mul_mem hφy hφx) k

end Glue

theorem t158SetupE6_of
    (hC : T158CompE6) : T158SetupE6 := by
  intro G _ _ L J A d b hP hcat
  obtain ⟨hcomp, hdI⟩ := hC G L J A d b hP hcat
  have hL : GLAPComponent 3 L L :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hP.qs hP.core
  have hchev : IsChevSimple 2 (PSimple 3 L) := hP.chev2
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hP.norm hP.d_mem
  have hdD : InnDiagOn 3 (Subgroup.zpowers d) L :=
    innDiagOn_mono ((innDiagOn_iff hL hP.qs).1 hP.idiag₂) le_sup_left
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  obtain ⟨-, -, -, R, _, I0, F0, θ0, hRs, hRna, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists (CFSG.StandardType.ChevTwo.ys08_holds (PQuot 3 L) hq hchev)
  haveI : IsSimpleGroup (PSimple 3 L) := hq.2
  have hna : ∃ x y : PSimple 3 L, x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := hRna
    refine ⟨θ0.symm u, θ0.symm v, fun h => huv ?_⟩
    have := congrArg θ0 h
    simpa using this
  obtain ⟨Q, lin, hE, hdvd⟩ : ∃ (Q : ℕ) (lin : Bool),
      CFSG.LocalAnalysis.GLTheoremA.IsE6Eps (PSimple 3 L) Q lin ∧
        3 ∣ CFSG.LocalAnalysis.GLTheoremA.qEps lin Q := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    cases i with
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
    | lie idx =>
      obtain ⟨dd, hv⟩ := idx
      obtain ⟨q, hshape, hq'⟩ := hi
      rcases hq' with rfl | rfl
      · refine ⟨q.card, true, ⟨.lie ⟨.E6 q, hv⟩, rfl, ⟨e⟩⟩, ?_⟩
        exact hshape.2.2
      · refine ⟨q.card, false, ⟨.lie ⟨.twistedE6 q, hv⟩, rfl, ⟨e⟩⟩, ?_⟩
        exact hshape.2.2
  have hA : ∀ a ∈ A, InnDiagOn 3 (Subgroup.zpowers a) L := by
    intro a ha
    by_contra hna'
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hP.norm ha
    set N := Subgroup.normalizer (L : Set G)
    set D : Subgroup (MulAut (PSimple 3 L)) := (A.subgroupOf N).map (chevAut 3 L) with hD
    have hDel : IsElemAbelian 3 D := (hP.elem.subgroupOf N).map (chevAut 3 L)
    have hle := kd26fE6_holds (PSimple 3 L) inferInstance hna Q lin hE hdvd D hDel
    set φ := MI.indAut 3 L a haN with hφ
    set δ := MI.indAut 3 L d hdN with hδ
    have hφD : φ ∈ D := ⟨⟨a⁻¹, Subgroup.inv_mem _ haN⟩, Subgroup.mem_subgroupOf.2 (A.inv_mem ha), rfl⟩
    have hδD : δ ∈ D :=
      ⟨⟨d⁻¹, Subgroup.inv_mem _ hdN⟩, Subgroup.mem_subgroupOf.2 (A.inv_mem hP.d_mem), rfl⟩
    have hφI : φ ∉ inner (PSimple 3 L) := fun h =>
      hna' (MI.inner_innDiag_holds Nat.prime_three hL hchev haN
        ((MI.indAut_mem_inner_iff Nat.prime_three hL haN).1 h))
    obtain ⟨i, hi3, hiI⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.exists_pow_mul_mem_of_card_le_three_mul
        D (inner (PSimple 3 L)) hDel hle hφD hφI δ hδD
    have hdaN : d * a ^ i ∈ N := Subgroup.mul_mem _ hdN (Subgroup.pow_mem _ haN i)
    have hind : MI.indAut 3 L (d * a ^ i) hdaN = φ ^ i * δ := by
      unfold MI.indAut
      rw [hφ, hδ]
      unfold MI.indAut
      rw [← map_pow, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
      rw [mul_inv_rev, inv_pow]
    have hinnda : InducesInnerMod 3 L (d * a ^ i) :=
      (MI.indAut_mem_inner_iff Nat.prime_three hL hdaN).1 (hind ▸ hiI)
    have hdinv : InnDiagOn 3 (Subgroup.zpowers d⁻¹) L := by rwa [Subgroup.zpowers_inv]
    have ha3 : a ^ 3 = 1 := hP.elem.2 a ha
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hdI (by simpa using hinnda)
    · have h1 : InnDiagOn 3 (Subgroup.zpowers (d * a ^ 1)) L :=
        MI.inner_innDiag_holds Nat.prime_three hL hchev hdaN hinnda
      have h2 := innDiagOn_zpowers_mul hL hchev hdinv h1
      rw [pow_one, inv_mul_cancel_left] at h2
      exact hna' h2
    · have h1 : InnDiagOn 3 (Subgroup.zpowers (d * a ^ 2)) L :=
        MI.inner_innDiag_holds Nat.prime_three hL hchev hdaN hinnda
      have h2 := innDiagOn_zpowers_mul hL hchev hdinv h1
      rw [inv_mul_cancel_left] at h2
      have hle' : Subgroup.zpowers a ≤ Subgroup.zpowers (a ^ 2) := by
        rw [Subgroup.zpowers_le]
        refine ⟨2, ?_⟩
        change (a ^ 2) ^ (2 : ℤ) = a
        rw [zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha3, one_mul]
      exact hna' (innDiagOn_mono h2 hle')
  have hInn : InnDiagOn 3 A L := MI.innDiag_unif_holds hP.norm hA
  exact
    { prime := hP.prime
      odd := hP.odd
      qs := hP.qs
      chev2 := hP.chev2
      elem := hP.elem
      idiag := inner_of_innDiagOn hL hP.qs hInn
      faithful := hP.faithful
      d_mem := hP.d_mem
      d_ne := hP.d_ne
      b_mem := hP.b_mem
      comp := hcomp
      pcomp := hP.pcomp
      chevJ := hP.chevJ
      b_norm := hP.b_norm
      nonID := hP.fg.elim (fun hF => (MI.field_nonInnDiag_holds hP.prime hP.odd hF).2)
        (fun hG => hG.1.2) }

end CFSG.LocalAnalysis.GLTheoremA.T158

end
