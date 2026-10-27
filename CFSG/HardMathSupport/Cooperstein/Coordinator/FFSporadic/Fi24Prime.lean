module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.PerfectLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi23
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCover

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.RankThree.PerfectCover CFSG.EvenSporadicStandard

noncomputable def fi23ToFi24 :
    NativeSporadic.Fi23 →* NativeSporadic.Fi24prime :=
  (CFSG.Sporadic.Fi24.fi24EquivJ.symm : CFSG.Sporadic.Fi24.J →* NativeSporadic.Fi24prime).comp
    ((CFSG.Sporadic.Fi24.M).subtype.comp
      ((CFSG.Sporadic.Fi24.fi23EquivM.symm : CFSG.Sporadic.Fi23.J →* CFSG.Sporadic.Fi24.M).comp
        (CFSG.Sporadic.Fi23.fi23EquivJ : NativeSporadic.Fi23 →* CFSG.Sporadic.Fi23.J)))

theorem fi23ToFi24_injective :
    Function.Injective (fi23ToFi24) := by
  intro x y h
  have h1 := CFSG.Sporadic.Fi24.fi24EquivJ.symm.injective h
  have h2 := Subtype.ext_iff.2 (Subtype.ext_iff.1 h1)
  have h3 : CFSG.Sporadic.Fi24.fi23EquivM.symm (CFSG.Sporadic.Fi23.fi23EquivJ x) =
      CFSG.Sporadic.Fi24.fi23EquivM.symm (CFSG.Sporadic.Fi23.fi23EquivJ y) := Subtype.ext h1
  exact CFSG.Sporadic.Fi23.fi23EquivJ.injective
    (CFSG.Sporadic.Fi24.fi23EquivM.symm.injective h3)

theorem fi24_outer_bound
    (B : Subgroup (MulAut NativeSporadic.Fi24prime)) (_ : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (_ : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : NativeSporadic.Fi24prime →* MulAut _).range) :=
  card_le_two_mul_inf_inner_of_index CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime B

noncomputable def fi24CarrierEquiv : NativeSporadic.Fi24prime ≃* NativeSporadic.Carrier .Fi24Prime :=
  MulEquiv.refl _

theorem fi24_carrierFacts : CarrierFacts .Fi24Prime := by
  have hs : IsSimpleGroup NativeSporadic.Fi24prime := CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
  have hcard : Nat.card NativeSporadic.Fi24prime = 1255205709190661721292800 :=
    CFSG.Sporadic.Fi24.card_Fi24prime
  have hfin : Finite NativeSporadic.Fi24prime :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hperf : Group.IsPerfect NativeSporadic.Fi24prime :=
    isPerfect_of_isSimpleGroup_of_not_prime hs
      (Proving.not_prime_card_of_even_gt_two hcard (by norm_num) (by norm_num))
  exact ⟨hfin, hs, hperf, @exists_not_commute_of_perfect_simple _ _ hperf hs⟩

theorem fi24_card_hopfMultiplier
    : Nat.card (hopfMultiplier (NativeSporadic.Carrier .Fi24Prime)) = 3 :=
  nativeRow_of_two_zero_three_one (s := .Fi24Prime) rfl fi24_carrierFacts rowBound_Fi24Prime
    (Fi24Three.nativeCell3_Fi24Prime_of_fi23 kernelTrivialAt_three_Fi23)
    (Proving.bigPrimeFacts_of_ne_M .Fi24Prime (by decide))

theorem fi24_center_dvd
    (L : Type) [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.Fi24prime) :
    Nat.card (Subgroup.center L) ∣ 3 := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans fi24CarrierEquiv)
  rwa [fi24_card_hopfMultiplier] at h

theorem noIrrFFOffender_Fi24Prime_native
    : NoIrrFFOffender NativeSporadic.Fi24prime := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have h1 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h2 : (2 : ZMod 3) ≠ 1 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime h1 h2
  obtain ⟨hfin, hs, hperf, -⟩ := fi23_carrierFacts
  have hfin' : Finite NativeSporadic.Fi23 := hfin
  have hperf' : Group.IsPerfect NativeSporadic.Fi23 := hperf
  have hk : KernelTrivialAt NativeSporadic.Fi23 3 := kernelTrivialAt_three_Fi23
  obtain ⟨_, _, _, h, -⟩ := fi23_heisCfg
  have hZd := fi24_center_dvd ↥L hq e
  have hZp : IsPGroup 3 (Subgroup.center ↥L) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rwa [pow_one])
  have hb := two_pow_le_card_of_heisCfg_of_embedding hW e (by norm_num) hZp hk fi23ToFi24
    fi23ToFi24_injective h
  refine exclusion_of_card_lt_of_outer hW hq hirr hEN hE hel e fi24_outer_bound
    (lt_of_lt_of_le ?_ hb)
  have hZ3 : Nat.card (Subgroup.center ↥L) ≤ 3 := Nat.le_of_dvd (by norm_num) hZd
  rw [hord, CFSG.Sporadic.Fi24.card_Fi24prime]
  calc 2 * (Nat.card (Subgroup.center ↥L) * 1255205709190661721292800)
      ≤ 2 * (3 * 1255205709190661721292800) := by gcongr
    _ < 2 ^ (3 ^ 4 * 2) := by norm_num

theorem noIrrFFOffender_Fi24Prime
    : NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
  noIrrFFOffender_transfer noIrrFFOffender_Fi24Prime_native
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Fi24Prime
    : GF2NoFFSporadicFor .Fi24Prime :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Fi24Prime

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
