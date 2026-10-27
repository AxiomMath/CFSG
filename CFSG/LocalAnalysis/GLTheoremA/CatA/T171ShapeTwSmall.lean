module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmallDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2Ambig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section SuzukiCerts

theorem setup_false_of_suzuki {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b)
    (hcat : catalogIs (PSimple p L) CFSG.LocalAnalysis.GLTheoremA.K155X.l154ExcSuz) : False := by
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime h.pcomp
  have hJleL : J ≤ L := h.comp.1.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hLself : GLAPComponent p L L := glaPComponent_self_of_dvd_card h.prime h.qs hpL
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking h.idiag h.d_mem
  have hdp : d ^ p = 1 := h.elem.2 d h.d_mem
  have hcm : ¬ CentMod p L d := by
    intro hc
    exact chevAut_ne_one_of_setup h (hdN := hdN)
      ((chevAut_eq_one_iff h.prime hLself hdN).2 hc)
  have hInn : InnDiagOn p (Subgroup.zpowers d) L :=
    S10.innDiagOn_of_inner hLself h.qs
      (S171.innerDiagMarking_mono h.idiag (Subgroup.zpowers_le.2 h.d_mem))
  exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_false_of_suzuki h.prime h.odd hLself hcat hdp
    hdN hcm hInn h.pcomp

end SuzukiCerts

section TitsCerts

theorem setup_false_of_tits {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (h : Setup p L J A d b) (hv : (TauCeti.LieTypeIndex.tits).Valid)
    (he : Nonempty (PSimple p L ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) : False := by
  haveI : IsSimpleGroup (PSimple p L) := isSimpleGroup_pSimple h
  have hnc := exists_ne_comm_pSimple h
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking h.idiag h.d_mem
  have hdp : d ^ p = 1 := h.elem.2 d h.d_mem
  have hβp : chevAut p L ⟨d, hdN⟩ ^ p = 1 := chevAut_pow_eq_one p L hdN hdp
  have hβ1 : chevAut p L ⟨d, hdN⟩ ≠ 1 := chevAut_ne_one_of_setup h (hdN := hdN)
  have hsolve : Group.IsSolvable ↥(fixSubgroup (chevAut p L ⟨d, hdN⟩)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_tits hv hnc he
      h.prime h.odd hβp hβ1
  have hdP : IsPGroup p (Subgroup.zpowers d) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hx : ((x : G) ^ p) = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
    simpa using hx
  obtain ⟨hperf, hle, hne⟩ := chevTransfer_perfect_ne_bot h (hdN := hdN) hdP
  haveI hsolveI : Group.IsSolvable ↥(fixSubgroup (chevAut p L ⟨d, hdN⟩)) := hsolve
  have hJsolv : Group.IsSolvable ↥(chevTransfer p L J) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Nontrivial ↥(chevTransfer p L J) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  haveI : Group.IsPerfect ↥(chevTransfer p L J) := Subgroup.isPerfect_iff.2 hperf
  exact Group.IsPerfect.not_isSolvable ↥(chevTransfer p L J) hJsolv

end TitsCerts

section MainCerts

theorem innerCompNonShape_excTwisted_charTwo_of
    (hE : InnerCompNonShape fun i => (∃ q, i = .twistedE6 q) ∧ i.characteristic = 2)
    (hR : ReeF4CompInner) :
    InnerCompNonShape fun i => KD264Lie.isExcTwistedIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape hin
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    cases idx with
    | twistedE6 q =>
      exact hE p L J A d b hS ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨⟨q, rfl⟩, hi.2⟩, ⟨e⟩⟩ hshape hin
    | suzuki k =>
      exact (setup_false_of_suzuki hS ⟨.lie ⟨.suzuki k, hv⟩, trivial, ⟨e⟩⟩).elim
    | reeF4 k =>
      exact hR p L J A d b hS ⟨.lie ⟨.reeF4 k, hv⟩, ⟨k, rfl⟩, ⟨e⟩⟩ hshape hin
    | reeG2 k =>
      exact absurd (hi.2.symm.trans (TauCeti.LieTypeIndex.characteristic_reeG2 k)) (by norm_num)
    | tits => exact (setup_false_of_tits hS hv ⟨e⟩).elim
    | _ => exact hi.1.elim

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
