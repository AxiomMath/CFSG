
module

import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalInputs

@[expose] public section

namespace CFSG.SectionRank

open CFSG.Blueprint
open scoped commutatorElement

theorem mathieuWord_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ∀ w, mathieuWord a b w ∈ H
  | [] => H.one_mem
  | c :: w => by
    unfold mathieuWord
    refine H.mul_mem ?_ (mathieuWord_mem ha hb w)
    split_ifs
    · exact ha
    · exact hb
    · exact H.inv_mem hb

end CFSG.SectionRank
