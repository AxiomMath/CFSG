module

public import CFSG.LieType.Steinberg.CentralExt.CoverAssembly
public import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.POmegaMinusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LieType.Steinberg.Families
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverPrime
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFive
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.G2
public import CFSG.Open.QuasithinDefs

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint.Multiplier
  CFSG.LieType.Steinberg.CentralExt

namespace CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem lieModel_plus (hK : Nat.card K = 2) (hn : 4 ≤ n) :
    CFSG.Blueprint.LieModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, hn⟩, K, inferInstance, inferInstance,
    by rw [hK, pow_one], ⟨MulEquiv.refl _⟩⟩

theorem pomegaPlus_two_hopfMultiplier
    {p f : ℕ} (hn : 5 ≤ n) (hK : Nat.card K = p ^ f)
    (hK2 : Nat.card K = 2) :
    commutator (StatedProj (StatedOmega (StatedQuadPlus n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃*
        generic .POmegaPlus n p f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num)
    (hK2.trans (pow_one 2).symm)
  set q := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn3)
  obtain ⟨hq, -, hker⟩ := spinToStatedProj_quadPlus (K := K) hn3
  have : Group.IsPerfect (spinGroup (quadPlus n K)) := isPerfect_spinGroup_quadPlus hn3
  have : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    Group.IsPerfect.ofSurjective hq
  have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) := Finite.of_surjective q hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (plusDatum n K hn3).isFiniteType
    (Dv := (plusDatum n K hn3).divisible) rfl
  have hsplit := CoverAssembly.exists_section_of_cover_and_coprime (p := 2) (θ := q) hq hker.le
    (fun P _ _ _ η hη hC h2 => (even_split_orthogonal_prime_field_central_two_cover_trivial η hη
      hC h2 hn (lieModel_plus hK2 (by omega))).1)
    (fun E _ _ π hπ hcen hc => FieldFour.exists_section_of_coprime (SpinPlus.isCTGroupDatum hn3)
      (Spin.plusDatum_steinbergExtras hn3)
      (SpinPlus.chevalleyExtras hn3 O SpinPlus.commC (SpinPlus.commutatorFormula hn3 O)) E π hπ
      hcen hc)
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover
      (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => hsplit _ π hπ hcen)
  obtain ⟨e3⟩ := SpinPlusClosed.nonempty_scalarSpin_mulEquiv_generic (K := K) hn3 hK
  obtain ⟨-, hkerZ, -⟩ := spinToStatedProj_quadPlus (K := K) hn3
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans e3))⟩

theorem lieModel_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    (hn : 4 ≤ n) :
    CFSG.Blueprint.LieModel (StatedProj (StatedOmega (StatedQuadMinus n K b c))) .POmegaMinus n 2
      1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, hn⟩, K, inferInstance, inferInstance,
    by rw [hK, pow_one], b, c, hirr, ⟨MulEquiv.refl _⟩⟩

theorem pomegaMinus_two_hopfMultiplier
    {b c : K} {p f : ℕ} (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = p ^ f) (hK2 : Nat.card K = 2) :
    commutator (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃*
          Multiplicative (ZMod (Nat.gcd 4 ((p ^ f) ^ n + 1)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num)
    (hK2.trans (pow_one 2).symm)
  set q := spinToStatedProj (quadMinus n K b c) (range_spinMatrix_quadMinus hn hirr)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadMinus (K := K) hn hirr
  have : Group.IsPerfect (spinGroup (quadMinus n K b c)) := isPerfect_spinGroup_quadMinus hn hirr
  have : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
    Group.IsPerfect.ofSurjective hq
  have : Finite (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := Finite.of_surjective q hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have htriv : ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
      (η : P →* StatedProj (StatedOmega (StatedQuadMinus n K b c))),
      Function.Surjective η → η.ker ≤ Subgroup.center P → IsPGroup 2 η.ker → η.ker = ⊥ := by
    intro P _ _ _ η hη hC h2
    have hJ := lieModel_minus hirr hK2 hn
    rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
    · exact (even_nonsplit_orthogonal_four_prime_field_central_two_cover_trivial η hη hC h2 hJ).1
    · exact (even_nonsplit_orthogonal_five_prime_field_central_two_cover_trivial η hη hC h2 hJ).1
    · exact (even_higher_nonsplit_orthogonal_prime_field_central_two_cover_trivial η hη hC h2 h6
        hJ).1
  have hsplit := CoverAssembly.exists_section_of_cover_and_coprime (p := 2) (θ := q) hq hker.le
    htriv (fun E _ _ π hπ hcen hc =>
      SpinMinusClosed.spinMinus_exists_section_of_coprime hirr hn hπ hcen hc)
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover
      (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n K b c))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => hsplit _ π hπ hcen)
  obtain ⟨hcard, hcyc⟩ := SpinMinusClosed.card_scalarSpinM hirr hn hK
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo
