module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedWeylData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTwParab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

@[expose] def twE6Step1 : OrbitCert .E6 where
  lam := 9013640
  pts := [
    8022663, 8029833, 9865863, 9873033]
  parents := [
    2, 4, 20]
  table := [
    8590000128, 12884901888, 196608, 4295098368]
  lens := [
    0, 1, 1, 2]

@[expose] def twE6Step2 : OrbitCert .E6 where
  lam := 9021832
  pts := [
    7907431, 8022663, 8029833, 9865863, 9873033, 9988265]
  parents := [
    3, 18, 20, 36, 67]
  table := [
    16777216, 12885032960, 17213489152, 4345561088, 8674017280, 21542273024]
  lens := [
    0, 1, 2, 2, 3, 4]

@[expose] def twE6Step3 : OrbitCert .E6 where
  lam := 9021864
  pts := [
    7899303, 7907431, 8022663, 8029833, 9865863, 9873033, 9988265, 9996393]
  parents := [
    1, 19, 34, 36, 52, 83, 97]
  table := [
    256, 4328587264, 17196843520, 21525299968, 8657372160, 12985828608,
    25854084864, 30182671872]
  lens := [
    0, 1, 2, 3, 3, 4, 5, 6]

@[expose] def twE6Step4 : OrbitCert .E6 where
  lam := 8951944
  pts := [
    8890232, 9005464]
  parents := [
    3]
  table := [
    16777216, 1099511627777]
  lens := [
    0, 1]

@[expose] def twE6Step5 : OrbitCert .E6 where
  lam := 8951976
  pts := [
    8882104, 8894296, 9067144]
  parents := [
    1, 19]
  table := [
    256, 1099545182209, 2199040033282]
  lens := [
    0, 1, 2]

@[expose] def twE6Step6 : OrbitCert .E6 where
  lam := 8947864
  pts := [
    8943784, 8951912]
  parents := [
    1]
  table := [
    256, 1103806660609]
  lens := [
    0, 1]

@[expose] def twE6Coat0 : List (TwistedStep TwistTag.E6) := [
  ⟨30, 28, twE6Step3, [(2, 4), (3, 1)]⟩,
  ⟨28, 20, twE6Step2, [(2, 3), (2, 1)]⟩,
  ⟨20, 0, twE6Step1, [(2, 2)]⟩]

theorem twE6Coat0_check : twistedChainCheck twE6Coat0 30 = true := by
  decide +kernel

@[expose] def twE6Coat1 : List (TwistedStep TwistTag.E6) := [
  ⟨43, 41, twE6Step5, [(3, 1)]⟩,
  ⟨41, 33, twE6Step4, [(2, 1)]⟩,
  ⟨33, 0, twE6Cert1, [(2, 2)]⟩]

theorem twE6Coat1_check : twistedChainCheck twE6Coat1 43 = true := by
  decide +kernel

@[expose] def twE6Coat2 : List (TwistedStep TwistTag.E6) := [
  ⟨55, 53, twE6Step6, [(2, 1)]⟩,
  ⟨53, 33, twE6Cert2, [(3, 2)]⟩,
  ⟨33, 0, twE6Cert1, [(2, 2)]⟩]

theorem twE6Coat2_check : twistedChainCheck twE6Coat2 55 = true := by
  decide +kernel

@[expose] def twE6Coat3 : List (TwistedStep TwistTag.E6) := [
  ⟨61, 53, twE6Cert3, [(2, 5), (2, 3), (2, 1)]⟩,
  ⟨53, 33, twE6Cert2, [(3, 2)]⟩,
  ⟨33, 0, twE6Cert1, [(2, 2)]⟩]

theorem twE6Coat3_check : twistedChainCheck twE6Coat3 61 = true := by
  decide +kernel


@[expose] def twE6Mask : Fin TwistTag.E6.foldedTag.rank → ℕ := ![30, 43, 55, 61]

@[expose] def twE6Fac : Fin TwistTag.E6.foldedTag.rank → List (ℕ × ℕ) :=
  ![[(2, 2), (2, 3), (2, 1), (2, 4), (3, 1)], [(2, 2), (2, 1), (3, 1)],
    [(2, 2), (3, 2), (2, 1)], [(2, 2), (3, 2), (2, 5), (2, 3), (2, 1)]]

@[expose] def twE6Full : List (ℕ × ℕ) :=
  [(2, 2), (3, 2), (2, 5), (2, 3), (2, 1), (2, 9), (2, 6), (2, 4), (3, 1)]

theorem foldMask_compl_E6 (a : Fin TwistTag.E6.foldedTag.rank) :
    foldMask TwistTag.E6 {b | b ≠ a} =
      ((maskSet TwistTag.E6.tag (twE6Mask a) : Finset (Fin TwistTag.E6.tag.rank)) :
        Set (Fin TwistTag.E6.tag.rank)) := by
  ext i
  simp only [foldMask, Set.mem_setOf_eq, Finset.mem_coe, mem_maskSet]
  revert a i
  decide

section Sums

variable
  [Fintype (WeylGroup TwistTag.E6.tag)]

theorem twistedParabolicSum_twE6_coat0 (q : ℕ) :
    twistedParabolicSum TwistTag.E6 (maskSet TwistTag.E6.tag 30) q =
      ([(2, 2), (2, 3), (2, 1), (2, 4), (3, 1)].map fun f => geomSum f.1 f.2 q).prod := by
  rw [twistedParabolicSum_eq_of_chainCheck q _ _ twE6Coat0_check]
  simp only [twE6Coat0, TwistedStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  ring

theorem twistedParabolicSum_twE6_coat1 (q : ℕ) :
    twistedParabolicSum TwistTag.E6 (maskSet TwistTag.E6.tag 43) q =
      ([(2, 2), (2, 1), (3, 1)].map fun f => geomSum f.1 f.2 q).prod := by
  rw [twistedParabolicSum_eq_of_chainCheck q _ _ twE6Coat1_check]
  simp only [twE6Coat1, TwistedStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  ring

theorem twistedParabolicSum_twE6_coat2 (q : ℕ) :
    twistedParabolicSum TwistTag.E6 (maskSet TwistTag.E6.tag 55) q =
      ([(2, 2), (3, 2), (2, 1)].map fun f => geomSum f.1 f.2 q).prod := by
  rw [twistedParabolicSum_eq_of_chainCheck q _ _ twE6Coat2_check]
  simp only [twE6Coat2, TwistedStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  ring

theorem twistedParabolicSum_twE6_coat3 (q : ℕ) :
    twistedParabolicSum TwistTag.E6 (maskSet TwistTag.E6.tag 61) q =
      ([(2, 2), (3, 2), (2, 5), (2, 3), (2, 1)].map fun f => geomSum f.1 f.2 q).prod := by
  rw [twistedParabolicSum_eq_of_chainCheck q _ _ twE6Coat3_check]
  simp only [twE6Coat3, TwistedStep.value, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil]
  ring

theorem twistedParabolicSum_twE6_coat_eq (a : Fin TwistTag.E6.foldedTag.rank) (q : ℕ) :
    twistedParabolicSum TwistTag.E6 (maskSet TwistTag.E6.tag (twE6Mask a)) q =
      ((twE6Fac a).map fun f => geomSum f.1 f.2 q).prod := by
  fin_cases a
  · exact twistedParabolicSum_twE6_coat0 q
  · exact twistedParabolicSum_twE6_coat1 q
  · exact twistedParabolicSum_twE6_coat2 q
  · exact twistedParabolicSum_twE6_coat3 q

theorem twistedParabolicSum_twE6_univ_eq (q : ℕ) :
    twistedParabolicSum TwistTag.E6 Set.univ q =
      (twE6Full.map fun f => geomSum f.1 f.2 q).prod := by
  rw [twistedParabolicSum_univ, sum_length_relWeylTwist_E6]
  simp only [twE6Full, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

end Sums

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
