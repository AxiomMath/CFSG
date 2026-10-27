module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem k1419ClsCentre_eq_one {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) {a : S} (haJ : a ∈ J)
    (hcen : ∀ j ∈ J, a * j = j * a) (ha3 : a ^ 3 = 1) : a = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : ↥J := ⟨a, haJ⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa [x] using ha3)
  have hxc : (QuotientGroup.mk x : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcen y y.2).symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxc
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card
  let y : GLAPPrimeCore 3 ↥J := ⟨x, hxc⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext hx3
  have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have h2 : orderOf y ∣ Nat.card (GLAPPrimeCore 3 ↥J) := orderOf_dvd_natCard y
  have h3 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : y = 1 := orderOf_eq_one_iff.1 h3
  have h5 : x = 1 := congrArg Subtype.val h4
  exact congrArg Subtype.val h5

end CFSG.LocalAnalysis.GLTheoremA.K1419
