module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open

variable {S : Type*} [Group S]

theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  haveI := hs
  have hZ : Subgroup.center Q = ⊥ := b3Lie_center_eq_bot hnc
  have hq := b3Lie_isQuasisimple_of_simple hnc
  refine ⟨⟨hq.1⟩, hq.2, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

theorem perfectInLayer_of_isSolvable_fixSubgroup (β : MulAut S)
    (h : Group.IsSolvable (fixSubgroup β)) : PerfectInLayer β := by
  haveI := h
  intro P hPC hP
  refine le_trans (fun x hx => ?_) bot_le
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val
    (map_eq_one_of_perfect hPC hP (MonoidHom.id ↥(fixSubgroup β)) x hx)

theorem perfectInLayer_of_normal_quasisimple {β : MulAut S} {J : Subgroup S}
    (hJC : J ≤ fixSubgroup β) [(J.subgroupOf (fixSubgroup β)).Normal]
    (hJq : CFSG.IsQuasisimple J)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β))) :
    PerfectInLayer β := fun P hPC hP =>
  (perfect_le_of_solvable_quotient hJC hsol hPC hP).trans
    (le_sSup ⟨hJC, CFSG.Open.IsSubnormal.step hJC inferInstance (CFSG.Open.IsSubnormal.refl _),
      open_isQuasisimple hJq⟩)

theorem perfectInLayer_of_isSimpleGroup (β : MulAut S) (hs : IsSimpleGroup (fixSubgroup β))
    (hnc : ∃ a b : fixSubgroup β, a * b ≠ b * a) : PerfectInLayer β := by
  haveI : ((fixSubgroup β).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  haveI : Subsingleton (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)
  exact perfectInLayer_of_normal_quasisimple (J := fixSubgroup β) le_rfl
    (isQuasisimple_of_isSimpleGroup hs hnc) inferInstance

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
