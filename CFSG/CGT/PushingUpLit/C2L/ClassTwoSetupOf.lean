module

public import CFSG.CGT.PushingUpLit.C2L.ClassTwoQ
public import CFSG.CGT.PushingUpLit.C2L.LemmaM
public import CFSG.CGT.PushingUpLit.T2KR.Asc78Gen
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
import CFSG.CGT.PushingUpLit.T2KSW.FieldAutNonsplit
import CFSG.CGT.PushingUpLit.T2KSW.NonsplitWC
public import CFSG.CGT.PushingUpLit.C2L.Defs

public section

namespace CFSG.CGT.PushingUpLit.C2L.ClassTwoQ

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem exists_conj_Ec_le_of_not_eWeaklyClosed (h : ¬ EWeaklyClosed L T) :
    ∃ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T ∧
      (Ec L T).map (MulAut.conj g).toMonoidHom ≠ Ec L T := by
  by_contra hcon
  exact h fun g hg => by_contra fun hne => hcon ⟨g, hg, hne⟩

theorem TIRDSetup.of_wleVE (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight)
    (h25 : Asc76Lemma25) (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) :
    TIRDSetup G L M T n :=
  ⟨hs, hs.hyp.normal hE1, (hs.hyp.four_four hE1 hE8 h25 hs.sylow).2.2, hE,
    rdFacts_struct_of_wleVE hs hE1 hWVE hRD⟩

theorem Ec_le_ZT_of_not_eWeaklyClosed (hc : TIRDSetup G L M T n)
    (hcl : ClassLETwo T) (hnwc : ¬ EWeaklyClosed L T) : Ec L T ≤ ZT T := by
  obtain ⟨-, -, -, -, -, -, -, -, hEZ, -⟩ :=
    classTwo_Q_facts hc hcl (exists_conj_Ec_le_of_not_eWeaklyClosed hnwc)
  exact hEZ

theorem classTwoSetup_of_wleVE
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥) (hcl : ClassLETwo T) (hnwc : ¬ EWeaklyClosed L T)
    (hWVE : oTwoIn L ≤ blockU L ⊔ Ec L T) (hRD : T ≤ Rl L T ⊔ Dc L T) :
    ClassTwoSetup G L M T n :=
  have hc : TIRDSetup G L M T n := TIRDSetup.of_wleVE hE1 hE8 h25 hs hE hWVE hRD
  ⟨hs, hc.MN, hc.ME, hE, hc.facts, hRD, hcl, Ec_le_ZT_of_not_eWeaklyClosed hc hcl hnwc⟩

end CFSG.CGT.PushingUpLit.C2L.ClassTwoQ

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW CFSG.CGT.Timmesfeld75
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

theorem classTwoSetup_of
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification) (hA78 : Aschbacher78OneGen)
    {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}
    (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥) (hcl : ClassLETwo T) (hnwc : ¬ EWeaklyClosed L T) :
    ClassTwoSetup G L M T n :=
  have hRD : T ≤ Rl L T ⊔ Dc L T := t_le_rd_all hs hE1 hA78 hE
  ClassTwoQ.classTwoSetup_of_wleVE hE1 hE8 h25 hs hE hcl hnwc
    (wleVE_of_Rl_sup_Dc hE1 hE8 h25 hSCL hList hs hE hRD) hRD

end CFSG.CGT.PushingUpLit.C2L
