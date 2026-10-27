module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three10
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.RankThree.PartOne.KE.E7ThreePerX
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIndexLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcRootTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped Matrix MatrixGroups Pointwise

def e7T3BetaOne : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank [0, 1, 0, 1, 0, 0, 0]

def e7T3BetaTwo : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank [0, 1, 0, 1, 1, 0, 0]

def e7T3OrthWord : List (Fin Tag.E7.rank) :=
  [5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 1, 3, 4, 0, 2, 3]

def e7T3OrthComp : E7T3Comp := { kind := 0, u := [0, 2], rot := false }

theorem isRoot_e7T3BetaOne : IsRoot Tag.E7 e7T3BetaOne :=
  isRoot_toVec (by decide +kernel)

theorem isRoot_e7T3BetaTwo : IsRoot Tag.E7 e7T3BetaTwo :=
  isRoot_toVec (by decide +kernel)

theorem cartanCoord_e7T3BetaOne :
    ExceptionalCover.cartanCoord e7T3BetaOne = e7T3AVec := by decide +kernel

theorem cartanCoord_e7T3BetaTwo :
    ExceptionalCover.cartanCoord e7T3BetaTwo = e7T3DVec := by decide +kernel

theorem e7T3OrthComp_good : e7T3OrthComp.Good e7T3Word e7T3OrthWord := by decide +kernel

theorem e7T3BetaOne_eq_wordProd :
    (coxeterSystem Tag.E7).wordProd e7T3OrthWord • toVec Tag.E7.rank [1, 0, 0, 0, 0, 0, 0] =
      e7T3BetaOne := by
  rw [wordProd_smul_toVec7]
  decide +kernel

theorem e7T3BetaTwo_eq_wordProd :
    (coxeterSystem Tag.E7).wordProd e7T3OrthWord • toVec Tag.E7.rank [1, 0, 1, 0, 0, 0, 0] =
      e7T3BetaTwo := by
  rw [wordProd_smul_toVec7]
  decide +kernel

private theorem chainRoot13_zero_one :
    chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 1 =
      toVec Tag.E7.rank [1, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

private theorem chainRoot13_zero_two :
    chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 2 =
      toVec Tag.E7.rank [1, 0, 1, 0, 0, 0, 0] := by
  decide +kernel

theorem e7T3BetaOne_mem_sigmaSet :
    e7T3BetaOne ∈ sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3OrthWord) := by
  refine ⟨chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 1,
    CFSG.RankThree.PartOne.KE.chainRoot13_mem_parabolicRoots (by decide), ?_⟩
  show (coxeterSystem Tag.E7).wordProd e7T3OrthWord •
    chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 1 = e7T3BetaOne
  rw [chainRoot13_zero_one, e7T3BetaOne_eq_wordProd]

theorem e7T3BetaOne_neg_mem_sigmaSet :
    -e7T3BetaOne ∈ sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3OrthWord) := by
  have hpos := CFSG.RankThree.PartOne.KE.chainRoot13_mem_parabolicRoots
    (show (0 : Fin 3) ≠ 1 by decide)
  refine ⟨-chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 1,
    ⟨IsRoot.neg hpos.1, fun i hi => ?_⟩, ?_⟩
  · rw [Pi.neg_apply, hpos.2 i hi, neg_zero]
  · show (coxeterSystem Tag.E7).wordProd e7T3OrthWord • (-chainRoot
      CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 1) = -e7T3BetaOne
    rw [smul_neg, chainRoot13_zero_one, e7T3BetaOne_eq_wordProd]

theorem e7T3BetaTwo_mem_sigmaSet :
    e7T3BetaTwo ∈ sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3OrthWord) := by
  refine ⟨chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 2,
    CFSG.RankThree.PartOne.KE.chainRoot13_mem_parabolicRoots (by decide), ?_⟩
  show (coxeterSystem Tag.E7).wordProd e7T3OrthWord •
    chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 2 = e7T3BetaTwo
  rw [chainRoot13_zero_two, e7T3BetaTwo_eq_wordProd]

theorem e7T3BetaTwo_neg_mem_sigmaSet :
    -e7T3BetaTwo ∈ sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3OrthWord) := by
  have hpos := CFSG.RankThree.PartOne.KE.chainRoot13_mem_parabolicRoots
    (show (0 : Fin 3) ≠ 2 by decide)
  refine ⟨-chainRoot CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 2,
    ⟨IsRoot.neg hpos.1, fun i hi => ?_⟩, ?_⟩
  · rw [Pi.neg_apply, hpos.2 i hi, neg_zero]
  · show (coxeterSystem Tag.E7).wordProd e7T3OrthWord • (-chainRoot
      CFSG.RankThree.PartOne.KE.chain13 (0 : Fin 3) 2) = -e7T3BetaTwo
    rw [smul_neg, chainRoot13_zero_two, e7T3BetaTwo_eq_wordProd]

section Selection

variable {p : ℕ} [NeZero p]

private theorem e7T3XColumn_val_modEq {ε : ℤ} {q : ZMod p} (k : Fin Tag.E7.rank) (e : ℤ)
    (he : (e : ZMod p) = (ε : ZMod p) * q) :
    ((e7T3XColumn ε q k).val : ℤ) ≡ e7T3AVec k + e7T3DVec k * e [ZMOD p] := by
  have hcol : e7T3XColumn ε q k =
      (e7T3AVec k : ZMod p) + (e : ZMod p) * (e7T3DVec k : ZMod p) := by
    rw [show e7T3XColumn ε q k =
      (e7T3AVec k : ZMod p) + ((ε : ZMod p) * q) * (e7T3DVec k : ZMod p) from rfl, ← he]
  have hcalc : ((e7T3AVec k : ZMod p) + (e : ZMod p) * (e7T3DVec k : ZMod p)) =
      ((e7T3AVec k + e7T3DVec k * e : ℤ) : ZMod p) := by
    simp only [Int.cast_add, Int.cast_mul]
    ring
  refine (ZMod.intCast_eq_intCast_iff _ _ p).1 ?_
  push_cast
  rw [ZMod.natCast_zmod_val, hcol, hcalc]
  rw [Int.cast_add, Int.cast_mul]

theorem rootDiagUnit_e7T3XColumn_eq_mul {L : Type} [Field L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} :
    rootDiagUnit Tag.E7 (fun k => ζ ^ (e7T3XColumn ε q k).val) =
      rootTorusSL2 Tag.E7 L e7T3BetaOne ζ *
        rootTorusSL2 Tag.E7 L e7T3BetaTwo (ζ ^ ((((ε : ZMod p) * q).val : ℕ) : ℤ)) := by
  rw [rootTorusSL2_eq_rootDiagUnit_cartanCoord rfl isRoot_e7T3BetaOne,
    rootTorusSL2_eq_rootDiagUnit_cartanCoord rfl isRoot_e7T3BetaTwo,
    cartanCoord_e7T3BetaOne, cartanCoord_e7T3BetaTwo, ← rootDiagUnit_mul]
  have hab : (fun k => ζ ^ (e7T3XColumn ε q k).val) =
      (fun k => ζ ^ e7T3AVec k *
        (ζ ^ ((((ε : ZMod p) * q).val : ℕ) : ℤ)) ^ e7T3DVec k) := by
    funext k
    rw [← zpow_natCast ζ (e7T3XColumn ε q k).val, ← _root_.zpow_mul, ← _root_.zpow_add]
    have hmod := e7T3XColumn_val_modEq (p := p) (ε := ε) (q := q) k
      (((ε : ZMod p) * q).val : ℤ) (by
        push_cast
        exact ZMod.natCast_zmod_val ((ε : ZMod p) * q))
    rw [zpow_eq_zpow_iff_modEq]
    simpa only [hζ.eq_orderOf, mul_comm] using hmod
  rw [hab]
  rfl

end Selection

section Factor

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem e7T3XTuple_mem_sigmaFactor (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      P = rootSpan Tag.E7 L (sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3OrthWord)) ⊓
        twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      Finite P ∧ CFSG.IsQuasisimple ↥P ∧ P ≤ adjointGroup Tag.E7 L ∧
      P ≤ twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn ε (Nat.card K : ZMod p) i).val) ∈ P := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hq : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  have hq2 : ε = -1 → 2 < ℓ ^ f := by
    intro hεm
    have hKq : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [← hK]
    exact e7T3_q_gt_two hp3 hεm hKq hpf hεm
  obtain ⟨hg, hact⟩ := e7T3_comp_eps (L := L) hε F.hnW e7T3OrthComp_good
  have hg' : (coxeterSystem Tag.E7).wordProd e7T3OrthComp.u ∈
      parabolicWeylGroup Tag.E7 support13 := by
    simpa [e7T3OrthComp, e7T3J] using hg
  obtain ⟨P, hPeq, hfac, h₀, hh₀⟩ :=
    e7_a2_factor hf hK hε hq2
      ((coxeterSystem Tag.E7).wordProd e7T3OrthWord) F.n F.hnm
      ((coxeterSystem Tag.E7).wordProd e7T3OrthComp.u) hg' (fun α hα => by
        have h1 := hact α hα
        simpa [e7T3OrthComp, e7T3Beta, permLattice_one] using h1)
  refine ⟨P, hPeq, hfac.finite (), hfac.quasi (), hfac.le_adj (), hfac.le_fix (), ?_⟩
  rw [hPeq]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [rootDiagUnit_e7T3XColumn_eq_mul hζ]
    exact mul_mem
      (a2ci_rootTorusSL2_mem_rootSpan isRoot_e7T3BetaOne e7T3BetaOne_mem_sigmaSet
        e7T3BetaOne_neg_mem_sigmaSet ζ)
      (a2ci_rootTorusSL2_mem_rootSpan isRoot_e7T3BetaTwo e7T3BetaTwo_mem_sigmaSet
        e7T3BetaTwo_neg_mem_sigmaSet _)
  · have h := rootDiagUnit_mem_twistedTorus_e7T3XTuple (K := K) (L := L) F hK hζ hε hq
    rw [mem_twistedTorusOf] at h
    exact h.2

theorem exists_adjointGroup_e7T3XTuple (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ x : adjointGroup Tag.E7 K, adjEmb Tag.E7 K L x = F.g0 *
      rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn ε (Nat.card K : ZMod p) i).val) * F.g0⁻¹ := by
  classical
  obtain ⟨P, -, hPfin, hPq, hPadj, hPfix, htP⟩ :=
    e7T3XTuple_mem_sigmaFactor F hf hK hp hp3 hε hpf hζ
  exact exists_adjointGroup_of_mem_perfectFixed F hPfin hPadj hPfix
    (CFSG.Quasithin.F6.InspRest.commutator_eq_self_of_isQuasisimple hPq) htP

end Factor

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
