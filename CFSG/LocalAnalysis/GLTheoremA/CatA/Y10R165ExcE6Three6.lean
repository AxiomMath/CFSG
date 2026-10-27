module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6ScBound
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitTorus
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem not_dvd_card_center_e6_three {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 3) :
    ¬ p ∣ Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) =
      Nat.gcd 3 (Nat.card F - 1) :=
    (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 F).1
  rw [hZ]
  intro h
  have hp3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 (Nat.card F - 1))
  have hp3eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
  have hp2 : p ≠ 2 := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  have hpowne : ((2 : ZMod p) ^ n) ≠ 0 := pow_ne_zero n h2ne
  have hdvd : orderOf ((2 : ZMod p) ^ n) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hpowne
  change rk2Ord p n ∣ p - 1 at hdvd
  rw [hrk] at hdvd
  omega

theorem pRank_adjoint_e6_three {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 F)) = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h0
      have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
    have hdvd : orderOf ((2 : ZMod p) ^ n) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (pow_ne_zero n h2ne)
    change rk2Ord p n ∣ p - 1 at hdvd
    rw [hrk] at hdvd
    have hp3ne : p ≠ 3 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    have hp5ne : p ≠ 5 := by
      intro h
      rw [h] at hdvd
      norm_num at hdvd
    have hpge2 : 2 ≤ p := hp.two_le
    rcases hdvd with ⟨k, hk⟩
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have he : orderOf ((Nat.card F : ℕ) : ZMod p) = 3 := by
    rw [hcard]
    rw [show (((2 ^ n : ℕ) : ZMod p)) = (2 : ZMod p) ^ n by push_cast; rfl]
    exact hrk
  have hS : SylowTorus (adjointGroup Tag.E6 F) p 3 :=
    CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_three F hp hp3 he
  have hle : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 F)) ≤ 3 :=
    CFSG.LocalAnalysis.GLTheoremA.pRank_le_of_sylowTorusDatum hS hp
  have hge : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 F)) := by
    obtain ⟨T, E, -, -, hE, -, hEel, hEcard⟩ := hS.exists_torus
    exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hEcard
  omega

theorem ker_e6Isogeny_coprime_three {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hrk : rk2Ord p n = 3) :
    Nat.Coprime p (Nat.card (e6Isogeny F).ker) := by
  have hker : (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := F)
  rw [hker]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (not_dvd_card_center_e6_three hcard hp hrk)

theorem pRank_minGroup_e6_three {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) = 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (e6Isogeny F).ker) :=
    ker_e6Isogeny_coprime_three hcard hp hrk
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel p hp
    (e6Isogeny F) (e6Isogeny_surjective F) hcop, pRank_adjoint_e6_three hcard hp hp2 hrk]

theorem card_maximal_elemAbelian_e6_three {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : rk2Ord p n = 3) {Ã : Subgroup ↥(e6Data_valid.minGroup F)}
    (hAe : IsElemAbelian p Ã)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup ↥(e6Data_valid.minGroup F)) ≤
      CFSG.Open.pRank p Ã)
    (hA3 : 3 ≤ CFSG.Open.pRank p Ã) :
    Nat.card Ã = p ^ 3 := by
  have hprank := pRank_minGroup_e6_three hcard hp hp2 hrk
  have hAle : CFSG.Open.pRank p Ã ≤ 3 := by
    rw [← hprank]
    exact CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have hAge : 3 ≤ CFSG.Open.pRank p Ã := by
    rw [← hprank]
    exact hmax
  have hArank : CFSG.Open.pRank p Ã = 3 := le_antisymm hAle hAge
  rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe, hArank]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
