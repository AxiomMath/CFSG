module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
public import CFSG.RankThree.PartOne.CTP.StrongPCharPU
public import CFSG.Open.StatedDefs
import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open (StatedSU)
open CFSG.RankThree.PartOne.StrongP (IsUnitri rkFin rkFin_lt noncentralPair_su3)
open CFSG.LieType.Universal.Unitary (SU rootMatrix longRootMatrix rootHom longRootHom
  coe_rootHom coe_longRootHom conjEquiv exists_wittMatrix SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive
  exists_unitaryInvolution_ne exists_unitaryInvolution_eq_neg exists_add_unitaryInvolution_eq)

section Pair

variable {F : Type} [Field F] (σ : F ≃+* F)

private theorem wcU_lt_of_single {n : ℕ} {a b : Fin n} (hab : a < b) (u : F) {k l : Fin n}
    (h : Matrix.single a b u k l ≠ 0) : k < l := by
  by_cases h1 : a = k ∧ b = l
  · obtain ⟨rfl, rfl⟩ := h1
    exact hab
  · exact absurd (Matrix.single_apply_of_ne a b u k l h1) h

private theorem wcU_lt_of_single_sub {n : ℕ} {a b a' b' : Fin n} (h1 : a < b) (h2 : a' < b')
    (u u' : F) {k l : Fin n}
    (h : (Matrix.single a b u - Matrix.single a' b' u' : Matrix (Fin n) (Fin n) F) k l ≠ 0) :
    k < l := by
  rw [Matrix.sub_apply] at h
  by_cases h3 : Matrix.single a b u k l = 0
  · rw [h3, zero_sub, neg_ne_zero] at h
    exact wcU_lt_of_single h2 u' h
  · exact wcU_lt_of_single h1 u h3

theorem wcU_nonscalarPPair_su_of_lt (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [Fact p.Prime] [CharP F p]
    {n : ℕ} {i j : Fin n} (h12 : i < j) (h23 : j < Fin.rev j) {c : F} (hc0 : c ≠ 0)
    (hc : c + σ c = 0) : NonscalarPPair p (SU σ n) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h34 : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.2 h12
  have hij : i ≠ j := h12.ne
  have hjj : j ≠ Fin.rev j := h23.ne
  have hii : i ≠ Fin.rev i := (h12.trans (h23.trans h34)).ne
  have hrj : Fin.rev j ≠ i := (h12.trans h23).ne'
  let x : SU σ n := rootHom σ hσ hij hii hjj (Multiplicative.ofAdd 1)
  let y : SU σ n := longRootHom σ (i := j) hjj (Multiplicative.ofAdd ⟨c, hc⟩)
  have hxm : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = rootMatrix σ i j 1 :=
    coe_rootHom σ hσ hij hii hjj _
  have hym : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = longRootMatrix j c :=
    coe_longRootHom σ hjj _
  refine NonscalarPPair.of_unitri (r := rkFin n) (m := n) (rkFin_lt n) x.2 y.2 ?_ ?_ ?_
  · intro a b hab
    change (((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b ≠ 0 at hab
    rw [hxm] at hab
    have e : rootMatrix σ i j 1 - 1 =
        Matrix.single i j 1 - Matrix.single (Fin.rev j) (Fin.rev i) (σ 1) := by
      rw [rootMatrix]; abel
    rw [e] at hab
    exact wcU_lt_of_single_sub h12 h34 _ _ hab
  · intro a b hab
    change (((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b ≠ 0 at hab
    rw [hym, longRootMatrix, add_sub_cancel_left] at hab
    exact wcU_lt_of_single h23 c hab
  · intro h
    have h' := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h
    simp only [Units.val_mul] at h'
    rw [hxm, hym, longRootMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h'
    have h2 := congrFun (congrFun h' i) (Fin.rev j)
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_single_apply_same,
      Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h2
    have hx : rootMatrix σ i j 1 i j = 1 := by
      rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hij,
        Matrix.single_apply_same, Matrix.single_apply_of_ne _ _ _ _ _ (fun h => hrj h.1)]
      simp
    rw [hx, one_mul, add_zero] at h2
    exact hc0 (by linear_combination h2)

theorem wcU_nonscalarPPair_su_of_four_le (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [Fact p.Prime]
    [CharP F p] {n : ℕ} (hn : 4 ≤ n) {c : F} (hc0 : c ≠ 0) (hc : c + σ c = 0) :
    NonscalarPPair p (SU σ n) :=
  wcU_nonscalarPPair_su_of_lt σ hσ (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (Fin.mk_lt_mk.2 (by omega)) (by simp only [Fin.lt_def, Fin.val_rev]; omega) hc0 hc

end Pair

section Transport

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem wcU_nonscalarPPair_su (hp2 : p ≠ 2) (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) : NonscalarPPair p (SU (unitaryInvolution F p f) n) := by
  have hσ := unitaryInvolution_involutive hF
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · obtain rfl : n = 3 := by omega
    obtain ⟨a', ha'⟩ := exists_unitaryInvolution_ne hF
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    exact NonscalarPPair.of_noncentralPair
      (noncentralPair_su3 _ hσ hp3 (fun a ha => exists_add_unitaryInvolution_eq hF ha) ha')
  · obtain ⟨c, hc0, hc⟩ := exists_unitaryInvolution_eq_neg hF
    exact wcU_nonscalarPPair_su_of_four_le _ hσ h4 hc0 (by rw [hc]; ring)

theorem wcU_nonscalarPPair_statedSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)
    (h : NonscalarPPair p (SU (unitaryInvolution F p f) n)) :
    NonscalarPPair p (StatedSU n (p ^ f) F) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  refine NonscalarPPair.conj P (fun g hg => ?_) h
  rw [← SUid_eq_statedSU hF n]
  exact (conjEquiv P hP ⟨g, hg⟩).2

end Transport

private theorem wcU_charP {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (h : Nat.card F = p ^ f) : CharP F p := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

theorem wcOn_psu {K : Type} [Group K] [Finite K] {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (h : CFSG.Open.StatedClassicalModel K .PSU n p f) : WCOn p K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  haveI : CharP F p := wcU_charP (f := f * 2) (by rw [hF, pow_mul])
  exact NonscalarPPair.wcOn e
    (wcU_nonscalarPPair_statedSU hF n (wcU_nonscalarPPair_su hp2 hF hn))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
