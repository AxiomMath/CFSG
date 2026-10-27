module

public import CFSG.CGT.Timmesfeld75.O2Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

abbrev jQuot (R : Type) [Group R] : Type :=
  (R ⧸ CFSG.pCore 2 R) ⧸ Subgroup.center (R ⧸ CFSG.pCore 2 R)

@[expose] def jMap (R : Type) [Group R] : R →* jQuot R :=
  (QuotientGroup.mk' (Subgroup.center (R ⧸ CFSG.pCore 2 R))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 R))

section Basic

variable {R : Type} [Group R]

theorem jMap_surjective : Function.Surjective (jMap R) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem mem_ker_jMap {w : R} : w ∈ (jMap R).ker ↔ ∀ r : R, ⁅w, r⁆ ∈ CFSG.pCore 2 R := by
  constructor
  · intro hw r
    have hz : QuotientGroup.mk' (CFSG.pCore 2 R) w ∈ Subgroup.center (R ⧸ CFSG.pCore 2 R) :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hw)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 hz (QuotientGroup.mk' (CFSG.pCore 2 R) r)).symm
  · intro h
    refine MonoidHom.mem_ker.2 ((QuotientGroup.eq_one_iff _).2 (Subgroup.mem_center_iff.2 ?_))
    intro g
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 R) g
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 R) ⁅w, r⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (h r)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem pCore_le_ker_jMap : CFSG.pCore 2 R ≤ (jMap R).ker := fun o ho => by
  rw [mem_ker_jMap]
  intro r
  have e : ⁅o, r⁆ = o * (r * o⁻¹ * r⁻¹) := by simp only [commutatorElement_def, mul_assoc]
  rw [e]
  exact (CFSG.pCore 2 R).mul_mem ho
    ((CFSG.pCore_normal (p := 2) (G := R)).conj_mem _ ((CFSG.pCore 2 R).inv_mem ho) r)

variable [Finite R]

theorem conj_conjSubgroup_eq_of_mem_ker_jMap {T : Subgroup R} (hT : IsWC T) {w : R}
    (hw : w ∈ (jMap R).ker) (g : R) : conjSubgroup w (conjSubgroup g T) = conjSubgroup g T := by
  have hO : IsPGroup 2 (CFSG.pCore 2 R) := CFSG.pCore_isPGroup
  exact mem_normalizer_iff_conjSubgroup_eq.1 (mem_normalizer_of_commutator_mem (hT.conj g) hO
    fun x _ => mem_ker_jMap.1 hw x)

end Basic

end CFSG.CGT.Timmesfeld75
