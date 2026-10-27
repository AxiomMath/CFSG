module

public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutOuter
import CFSG.LargeExtraspecial.OutSixUnitary
import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LargeExtraspecial.S14

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem center_timmesfeldPSU_six : Subgroup.center (timmesfeldPSU 6) = ⊥ := by
  have hK := unitaryFieldData_two_one.card_eq_sq
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 2 2) 2 1
    hK 6 (by norm_num) (by decide)
  have hperfSU := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) hK
    (n := 6) (by norm_num) (by decide)
  have hperf : Group.IsPerfect (StatedProj (StatedSU 6 (2 ^ 1) (GaloisField 2 2))) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let e := (timmesfeldPSUEquiv (n := 6) (by norm_num)).trans
    (unitaryPSUEquiv unitaryFieldData_two_one (n := 6) (by norm_num))
  have hs' : IsSimpleGroup (timmesfeldPSU 6) := e.isSimpleGroup
  have hperf' : Group.IsPerfect (timmesfeldPSU 6) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases hs'.eq_bot_or_eq_top_of_normal (Subgroup.center _) with hc | hc
  · exact hc
  · exfalso
    have hcomm : ∀ a b : timmesfeldPSU 6, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top a) b).symm
    have : IsMulCommutative (timmesfeldPSU 6) := ⟨⟨hcomm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (timmesfeldPSU 6) this

section Model

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem sigmaQ_mul_self : sigmaQ h * sigmaQ h = 1 := by
  rw [sigmaQ, ← map_mul, barEquiv_mul_self, map_one]

theorem sixFieldFactor_conj (s : sixQ h) : sixFieldFactor h (MulAut.conj s) = 1 := by
  obtain ⟨g, rfl⟩ := sixProj_surjective h s
  rw [conj_sixProj_eq]
  have := primeFormFieldFactor_apply h (isPrimeFormGram_sixJ h) three_le_six not_six_eq_three
    ⟨g, g.2.1⟩ 1
  rwa [map_one, mul_one] at this

theorem sigmaQ_not_mem_inner : sigmaQ h ∉ inner (sixQ h) := by
  rintro ⟨s, hs⟩
  have h1 := sixFieldFactor_conj h s
  rw [hs, sixFieldFactor_sigmaQ] at h1
  exact barEquiv_ne_one h h1

end Model

theorem exists_outer_involution_timmesfeldPSU_six :
    ∃ τ : MulAut (timmesfeldPSU 6), τ * τ = 1 ∧ τ ∉ inner (timmesfeldPSU 6) := by
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv unitaryFieldData_two_one
    (isPrimeFormGram_sixJ unitaryFieldData_two_one)
  let f : timmesfeldPSU 6 ≃* sixQ unitaryFieldData_two_one :=
    (timmesfeldPSUEquiv (n := 6) (by norm_num)).trans eP.symm
  refine ⟨(MulAut.congr f).symm (sigmaQ unitaryFieldData_two_one), ?_, fun hmem => ?_⟩
  · rw [← map_mul, sigmaQ_mul_self, map_one]
  · refine sigmaQ_not_mem_inner unitaryFieldData_two_one ?_
    rw [← inner_map_congr f]
    exact ⟨_, hmem, (MulAut.congr f).apply_symm_apply _⟩

end CFSG.LargeExtraspecial.S14
