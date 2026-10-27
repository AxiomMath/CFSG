module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open scoped commutatorElement

section Family


variable {Y : Type} [Group Y] [Finite Y]

structure FBase (Ω : Set (Subgroup Y)) (b : Y) (K : Subgroup Y) (t : Y) : Prop where
  hyp : HypOmegaGen Ω
  mem : K ∈ Ω
  inv : IsUniqueInvolution K t
  comm : t * b = b * t
  syl : ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b K) ∧ IsQuatSub Q

@[expose] def fFamY (b : Y) (K : Subgroup Y) : Set (Subgroup Y) :=
  {M | ∃ c ∈ Subgroup.centralizer ({b} : Set Y), M = coreAt b (conjSub c K)}

@[expose] def fFam (b : Y) (K : Subgroup Y) : Set (Subgroup ↥(Subgroup.centralizer ({b} : Set Y))) :=
  restrictFamily (fFamY b K) (Subgroup.centralizer ({b} : Set Y))

variable {Ω : Set (Subgroup Y)} {b : Y} {K : Subgroup Y} {t : Y}

theorem FBase.t_mem_core (h : FBase Ω b K t) : t ∈ coreAt b K := by
  have htK : t ∈ K := h.inv.mem
  have htC : t ∈ Subgroup.centralizer ({b} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm
  exact Subgroup.subset_closure ⟨⟨htK, htC⟩, isPGroup_zpowers_of_mul_self_eq_one h.inv.sq h.inv.ne_one⟩

theorem FBase.inv_core (h : FBase Ω b K t) : IsUniqueInvolution (coreAt b K) t :=
  isUniqueInvolution_mono h.inv (TwinADescent.coreAt_le_left b K) h.t_mem_core

theorem FBase.memberData (h : FBase Ω b K t) {c : Y} (hc : c ∈ Subgroup.centralizer ({b} : Set Y)) :
    conjSub c K ∈ Ω ∧ IsUniqueInvolution (conjSub c K) (c * t * c⁻¹) ∧
      c * t * c⁻¹ ∈ coreAt b (conjSub c K) := by
  refine ⟨h.hyp.conjInvariant c K h.mem, h.inv.conj c, ?_⟩
  have := conj_mem_conjSub (n := c) h.t_mem_core
  rwa [TwinADescent.conjSub_coreAt hc K] at this

theorem FBase.clauses (h : FBase Ω b K t) : TwinEdge.Fam.Clauses (fFamY b K) := by
  obtain ⟨Q, hQ, hqQ⟩ := h.syl
  have hnc : ¬ IsMulCommutative ↥Q := by
    intro hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hqQ.exists_not_commute
    exact hxy (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩ |> congrArg Subtype.val)
  refine clauses_of_fcores h.hyp (Subgroup.centralizer ({b} : Set Y)) (e := Nat.card ↥Q) ?_
  rintro M ⟨c, hc, rfl⟩
  obtain ⟨hJ, hz, hzm⟩ := h.memberData hc
  have hS : IsSylow2In (conjSub c Q) (coreAt b (conjSub c K)) := by
    have := hQ.conj c
    rwa [TwinADescent.conjSub_coreAt hc K] at this
  refine ⟨conjSub c K, hJ, rfl, ⟨_, hz, hzm⟩, ⟨conjSub c Q, hS, ?_⟩, ?_⟩
  · intro hcomm
    exact hnc (TwinEdge.Fam.isMulCommutative_of_conjSub c hcomm)
  · intro P' hP'
    rw [← AscL62.natCard_conjSub c Q]
    exact (hS.natCard_eq hP').symm

theorem fFamY_conj (b : Y) (K : Subgroup Y) {n : Y} (hn : n ∈ Subgroup.centralizer ({b} : Set Y))
    {M : Subgroup Y} (hM : M ∈ fFamY b K) : conjSub n M ∈ fFamY b K := by
  obtain ⟨c, hc, rfl⟩ := hM
  refine ⟨n * c, Subgroup.mul_mem _ hn hc, ?_⟩
  rw [conjSub_mul, TwinADescent.conjSub_coreAt hn]

theorem FBase.hypOmegaGen_fFam (h : FBase Ω b K t) : HypOmegaGen (fFam b K) := by
  refine (h.clauses.restrict (Subgroup.centralizer ({b} : Set Y))).hypOmegaGen ?_
  rintro n _ ⟨L, hL, hLC, rfl⟩
  refine ⟨conjSub (n : Y) L, fFamY_conj b K n.2 hL, ?_, Generic.conjSub_subgroupOf _ n _⟩
  have := conjSub_mono (n := (n : Y)) hLC
  rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer n.2)] at this

end Family

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
