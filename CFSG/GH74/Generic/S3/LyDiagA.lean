module

public import CFSG.GH74.Generic.S3.LyRank3
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section

variable {H : Type} [Group H]

theorem mul_comm_of_commutator_eq_bot' {A B : Subgroup H} (h : ⁅A, B⁆ = ⊥) {a b : H} (ha : a ∈ A)
    (hb : b ∈ B) : a * b = b * a := by
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

variable [Finite H]

theorem eq_or_eq_conj_of_gen4 (hH : Gen4 H) {L : Subgroup H} (hL : CFSG.IsComponent L) {t : H}
    (hLs : conjSub t⁻¹ L ≠ L) {J : Subgroup H} (hJ : CFSG.IsComponent J) :
    J = L ∨ J = conjSub t⁻¹ L := by
  by_contra hcon
  rw [not_or] at hcon
  have hL' : CFSG.IsComponent (conjSub t⁻¹ L) := isComponent_conjSub hL _
  have hAB := commutator_conjSub_eq_bot hL hLs
  have hJL : ⁅J, L⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hJ hL).resolve_left hcon.1
  have hJL' : ⁅J, conjSub t⁻¹ L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ hL').resolve_left hcon.2
  exact not_gen4_of_three_commuting_quasisimple (A := L) (B := conjSub t⁻¹ L) (J := J) hL.1 hL'.1 hJ.1
    (fun a ha b hb => mul_comm_of_commutator_eq_bot' hAB ha hb)
    (fun a ha j hj => (mul_comm_of_commutator_eq_bot' hJL hj ha).symm)
    (fun b hb j hj => (mul_comm_of_commutator_eq_bot' hJL' hj hb).symm) hH

omit [Finite H] in
theorem eq_range_swapDiag_of_subnormal {t : H} (ht : orderOf t = 2) {L : Subgroup H}
    (hL : CFSG.IsQuasisimple ↥L) (hAB : ⁅L, conjSub t⁻¹ L⁆ = ⊥) {I : Subgroup H}
    (hI : CFSG.IsQuasisimple ↥I)
    (hIsub : (I.subgroupOf (centralizer ({t} : Set H))).IsSubnormal)
    (hIle : I ≤ (swapDiag hAB).range) : I = (swapDiag hAB).range := by
  have ht' : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  set Δ := (swapDiag hAB).range with hΔ
  have hΔC : Δ ≤ centralizer ({t} : Set H) := by
    rintro _ ⟨x, rfl⟩
    exact swapDiag_mem_centralizer hAB ht' x
  have hΔq : CFSG.IsQuasisimple ↥Δ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
      (isQuasisimple_range_swapDiag hAB
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hL))
  have hsubΔ : (I.subgroupOf Δ).IsSubnormal :=
    CFSG.GH74.GLS.TwoThin.isSubnormal_inf_subgroupOf hIsub hΔC
  rcases quasisimple_subnormal_subgroups hΔq hsubΔ with htop | hcen
  · rw [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm hIle htop
  · exfalso
    obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hI
    apply hab
    have ha : (⟨a.1, hIle a.2⟩ : ↥Δ) ∈ center ↥Δ := hcen (show _ ∈ I.subgroupOf Δ from a.2)
    have := Subgroup.mem_center_iff.1 ha ⟨b.1, hIle b.2⟩
    exact Subtype.ext (congrArg Subtype.val this).symm

end

end CFSG.GH74.Generic.S3
