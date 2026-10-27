module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecStd
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Solv

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}

theorem solvable_centralizer_of_exactShape (h : ExactShape t A m) :
    Group.IsSolvable ↥(centralizer (A : Set X)) := by
  classical
  set K := centralizer (A : Set X) with hK
  have d := cyc_of_exactShape h
  obtain ⟨hNK, hNconj, hNodd, hNQ, hNmul⟩ := oddPart_spec d.le d.pgroup d.odd_index d.cyclic
  set N := oddPart K with hN
  have htK : t ∈ K := mem_centralizer_of_exactShape h
  let N' : Subgroup ↥K := N.subgroupOf K
  have hN'normal : N'.Normal := by
    refine ⟨fun n hn k => ?_⟩
    exact hNconj k k.2 n hn
  have hN'solv : Group.IsSolvable ↥N' := by
    have : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNK).injective
  let t' : ↥K := ⟨t, htK⟩
  let g : ↥(zpowers t') →* ↥K ⧸ N' := (QuotientGroup.mk' N').comp (zpowers t').subtype
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, hx, q, hq, hkxq⟩ := hNmul k k.2
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    refine ⟨⟨t' ^ j, mem_zpowers_iff.2 ⟨j, rfl⟩⟩, ?_⟩
    have hxN' : (⟨x, hNK hx⟩ : ↥K) ∈ N' := hx
    have hkeq : k = ⟨x, hNK hx⟩ * t' ^ j := Subtype.ext (by simpa using hkxq)
    show QuotientGroup.mk' N' (t' ^ j) = (k : ↥K ⧸ N')
    rw [hkeq, QuotientGroup.mk_mul]
    have : ((⟨x, hNK hx⟩ : ↥K) : ↥K ⧸ N') = 1 := (QuotientGroup.eq_one_iff _).2 hxN'
    rw [this, one_mul]
    rfl
  have hcyc : IsCyclic (↥K ⧸ N') := isCyclic_of_surjective g hg
  have hqsolv : Group.IsSolvable (↥K ⧸ N') :=
    Group.isSolvable_of_comm (fun a b => hcyc.isMulCommutative.is_comm.comm a b)
  exact Group.isSolvable_of_ker_le_range N'.subtype (QuotientGroup.mk' N') (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Solv

end CFSG.OddStandard.AltStdSec
