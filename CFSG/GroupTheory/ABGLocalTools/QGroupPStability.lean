module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQGroup
import CFSG.GroupTheory.ABGLocalTools.PStabilityQBorel
import CFSG.GroupTheory.ABGLocalTools.PStabilityQChoice
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.GroupTheory.ABGLocalTools.PStabilityQOuter
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate42
public import Certificates.Certificate43
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion CFSG.ABGQGroups

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem isPStable_of_qGroup
    (hp : p ≠ 2) {q : ℕ} (hst : QGroupStanding p q H) (hchar : ¬ p ∣ q)
    (hOp : pCore p H ≠ ⊥) (hfacts : QGroupStabilityFacts q H) : IsPStable p H := by
  refine isPStable_of_qGroup_of_facts hp hst hchar hOp hfacts sl2ElementChoice
    sl2BorelOfSplitElement sl2OddNormal sl2DicksonQuotient ?_
  intro G M _ _ _ π hπ hker V _ _ _ ρ hρ x hx J _ F _ _ hF hpF e hC hxp
  exact mem_of_quadratic_of_pow_eq_one hp π hπ hker ρ hρ hx J hF hpF e hC sl2FieldAutomorphism hxp

end CFSG.ABGLocalTools
