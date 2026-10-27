module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bA6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bL27
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bL28
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bSmall1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bU33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bU52
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTits
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubFHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open TauCeti

structure I264bResidual : Prop where
  td42 : ∀ p, KDescFam p fTD42
  u38 : ∀ p, KDescFam p fU38
  linear : ∀ p, KDescFam p fLinear
  unitary : ∀ p, KDescFam p fUnitary
  symplectic : ∀ p, KDescFam p fSymplectic
  omegaPlus : ∀ p, KDescFam p fOmegaPlus
  omegaMinus : ∀ p, KDescFam p fOmegaMinus
  e6 : ∀ p, KDescFam p fE6
  e7 : ∀ p, KDescFam p fE7
  e8 : ∀ p, KDescFam p fE8
  f4 : ∀ p, KDescFam p fF4
  g2 : ∀ p, KDescFam p fG2
  twE6 : ∀ p, KDescFam p fTwE6
  triD4 : ∀ p, KDescFam p fTriD4
  suzuki : ∀ p, KDescFam p fSuzuki
  reeTits : ∀ p, KDescFam p fReeTits


theorem i264bFacts_of_residual (R : I264bResidual) (p : ℕ) : I264bFacts p :=
  have hR : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.LocalAnalysis.GLTheoremA.Rank23At Y :=
    fun Y _ _ => CatB.rank23At_holds Y
  have hS : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.LocalAnalysis.GLTheoremA.StdSubFAt Y :=
    fun Y _ _ => CatB.stdSubFAt_holds Y
  { alt5 := kDescFam_alt5 p
    alt6 := kDescFam_alt6 p
    alt8 := kDescFam_alt8 p
    l27 := kDescFam_l27 p
    u33 := kDescFam_u33 p
    tits := kDescFam_tits p
    sp62 := kDescFam_sp62 hR hS p
    u42 := kDescFam_u42 hR hS p
    u52 := kDescFam_u52 hR p
    o8p2 := kDescFam_o8p2 hR p
    td42 := R.td42 p
    l28 := kDescFam_l28 p
    u38 := R.u38 p
    linear := R.linear p
    unitary := R.unitary p
    symplectic := R.symplectic p
    omegaPlus := R.omegaPlus p
    omegaMinus := R.omegaMinus p
    e6 := R.e6 p
    e7 := R.e7 p
    e8 := R.e8 p
    f4 := R.f4 p
    g2 := R.g2 p
    twE6 := R.twE6 p
    triD4 := R.triD4 p
    suzuki := R.suzuki p
    reeTits := R.reeTits p }

theorem i264bAt_of_residual {G : Type} [Group G] [Finite G] {p : ℕ}
    (hLB : p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p) (R : I264bResidual) :
    I264bAt G p :=
  i264bAt_of_facts hLB (i264bFacts_of_residual R p)

theorem i264ChevTwoAt_of_residual {G : Type} [Group G] [Finite G] {p : ℕ}
    (hLB : p.Prime → ∀ (Y : Type) [Group Y] [Finite Y], LBalanceAt Y p) (R : I264bResidual) :
    I264ChevTwoAt G p :=
  i264ChevTwoAt_of_facts hLB (i264bFacts_of_residual R p)

end CFSG.LocalAnalysis.GLTheoremA
