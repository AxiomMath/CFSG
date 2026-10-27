module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup
import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
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

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def T158CompLin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N m : ℕ),
    PreSetup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .A (N - 1) q ∧ q.exponent = m ∧ I171.I171LieShape p i) →
    (CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧ 2 * p ≤ N ∧
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .A (N / p - 1) q ∧ q.p = 2 ∧ q.exponent = m * p)

@[expose] def T158CompUni : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N m : ℕ),
    PreSetup p L J A d b →
    catalogIs (PSimple p L) (onLie fun i => ∃ q : TauCeti.PrimePower,
      i = .twistedA (N - 1) q ∧ q.exponent = m ∧ I171.I171LieShape p i) →
    (CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧ 2 * p ≤ N ∧
    catalogIs (PSimple p J) (onLie fun i => ∃ q : TauCeti.PrimePower,
      q.p = 2 ∧ q.exponent = m * p ∧
      ((N / p = 2 ∧ i = .A 1 q) ∨ (3 ≤ N / p ∧ i = .twistedA (N / p - 1) q)))

@[expose] def T158LinTypeOneW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 3 ≤ N →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) →
    (hw : WSetup p L J A d b) →
    CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) →
    ¬ InnDiagOn p (Subgroup.zpowers b) J →
    ∀ M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS,
      (∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p)) → False

@[expose] def T158UniTypeOneW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p N n : ℕ) (L J A : Subgroup G) (d b : G)
    (K : Type) [Field K] [Finite K] (_ : UnitaryFieldData 2 n K),
    p.Prime → p ∣ 2 ^ n + 1 → 3 ≤ N → (N, 2 ^ n) ≠ (3, 2) →
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)) →
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ) →
    (hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))) →
    (hw : WSetup p L J A d b) →
    CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) →
    ¬ InnDiagOn p (Subgroup.zpowers b) J →
    ∀ M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS,
      (∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p)) → False

theorem t158CompLU_of (hL : T158CompLin) (hU : T158CompUni) : T158CompLU := by
  intro G _ _ p L J A d b N hpre hcat
  obtain ⟨c, hc, e⟩ := hcat
  cases c with
  | lie i =>
    obtain ⟨q, hq | hq, hsh⟩ := hc
    · obtain ⟨hcomp, h2p, hJ⟩ := hL G p L J A d b N q.exponent hpre ⟨.lie i, ⟨q, hq, rfl, hsh⟩, e⟩
      refine ⟨hcomp, h2p, S9.catalogIs_mono (fun c hc => ?_) hJ⟩
      cases c with
      | lie j =>
        obtain ⟨q', hj, hq2, -⟩ := hc
        exact ⟨q', hq2, Or.inl hj⟩
      | _ => exact hc.elim
    · obtain ⟨hcomp, h2p, hJ⟩ := hU G p L J A d b N q.exponent hpre ⟨.lie i, ⟨q, hq, rfl, hsh⟩, e⟩
      refine ⟨hcomp, h2p, S9.catalogIs_mono (fun c hc => ?_) hJ⟩
      cases c with
      | lie j =>
        obtain ⟨q', hq2, -, ⟨hN2, hj⟩ | ⟨-, hj⟩⟩ := hc
        · exact ⟨q', hq2, Or.inl (by rw [hN2]; exact hj)⟩
        · exact ⟨q', hq2, Or.inr hj⟩
      | _ => exact hc.elim
  | _ => exact hc.elim

end CFSG.LocalAnalysis.GLTheoremA.T158

end
