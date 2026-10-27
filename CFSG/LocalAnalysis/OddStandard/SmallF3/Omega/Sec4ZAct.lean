module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def sec4ZAct (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) :
    ↥(normalizer (L : Set G)) →* ProjOrth Sec4IQ where
  toFun s := Classical.choose (exists_sec4IActs e s.2)
  map_one' :=
    (Classical.choose_spec (exists_sec4IActs e (1 : ↥(normalizer (L : Set G))).2)).unique
      (Sec4IActs.one e)
  map_mul' a b :=
    (Classical.choose_spec (exists_sec4IActs e (a * b).2)).unique
      ((Classical.choose_spec (exists_sec4IActs e a.2)).mul
        (Classical.choose_spec (exists_sec4IActs e b.2)))

theorem sec4ZAct_spec (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    (s : ↥(normalizer (L : Set G))) : Sec4IActs e (s : G) (sec4ZAct e s) :=
  Classical.choose_spec (exists_sec4IActs e s.2)

theorem sec4ZAct_eq (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G}
    (hs : s ∈ normalizer (L : Set G)) {y : ProjOrth Sec4IQ} (h : Sec4IActs e s y) :
    sec4ZAct e ⟨s, hs⟩ = y :=
  (sec4ZAct_spec e ⟨s, hs⟩).unique h

@[expose] noncomputable def sec4ZImage (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    (S : Subgroup G) : Subgroup (ProjOrth Sec4IQ) :=
  (S.subgroupOf (normalizer (L : Set G))).map (sec4ZAct e)

theorem mem_sec4ZImage_iff (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) (S : Subgroup G)
    (y : ProjOrth Sec4IQ) :
    y ∈ sec4ZImage e S ↔ ∃ s ∈ S, Sec4IActs e s y := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s : G), hs, sec4ZAct_spec e s⟩
  · rintro ⟨s, hs, hy⟩
    exact ⟨⟨s, hy.1⟩, hs, sec4ZAct_eq e hy.1 hy⟩

theorem mem_sec4ZImage_of_mem (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {S : Subgroup G}
    {w : G} (hwS : w ∈ S) (hwL : w ∈ L) :
    ((e (QuotientGroup.mk (⟨w, hwL⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) ∈
      sec4ZImage e S :=
  (mem_sec4ZImage_iff e S _).mpr ⟨w, hwS, Sec4IActs.of_mem e hwL⟩

theorem sec4ZImage_isPGroup (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) (hSN : S ≤ normalizer (L : Set G)) :
    IsPGroup 2 ↥(sec4ZImage e S) :=
  (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm).map (sec4ZAct e)

end CFSG.OddStandard.SmallF3.Omega
