module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Dickson.Sec6.I923

theorem isQuasisimple_of_open_up34 {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, exists_not_comm_of_quasisimple h⟩

theorem exists_component_of_isLThreeFour {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β) {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hT : IsLThreeFour (barOf 3 I)) :
    IsComponentOf I (fixSubgroup β) ∧ IsLThreeFour (↥I ⧸ Subgroup.center ↥I) := by
  have hle : I ≤ GLALayer (fixSubgroup β) := hβ I hI.1 (glaPComponent_perfect hI)
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hI hle
  refine ⟨hcomp, ?_⟩
  have hq : CFSG.IsQuasisimple ↥I := isQuasisimple_of_open_up34 hcomp.2.2
  obtain ⟨hsimp, hnab⟩ := isSimpleGroup_of_isLThreeFour hT
  have hZ : Subgroup.center (barOf 3 I) = ⊥ := up34_center_eq_bot_of_simple hnab
  set N : Subgroup ↥I := GLAPPrimeCore 3 ↥I with hN
  have hNn : N.Normal := GLAPPrimeCore.normal 3 ↥I
  have hNZ : N ≤ Subgroup.center ↥I := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with h | h
    · exfalso
      have hsub : Subsingleton (barOf 3 I) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            change a⁻¹ * b ∈ GLAPPrimeCore 3 ↥I
            rw [← hN, h]
            exact Subgroup.mem_top _
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subsingleton.elim _ _)
    · exact h
  have hZN : Subgroup.center ↥I ≤ N := by
    intro z hz
    have hz' : (QuotientGroup.mk z : barOf 3 I) ∈ Subgroup.center (barOf 3 I) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.1 hz g
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  have hNeq : N = Subgroup.center ↥I := le_antisymm hNZ hZN
  exact IsLThreeFour.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hNeq) hT

theorem noL34Layer_of_components {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β)
    (h : ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
      ¬ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) : NoL34Layer β := by
  intro I hI hT
  obtain ⟨hcomp, hK⟩ := exists_component_of_isLThreeFour hβ hI hT
  exact h I hcomp hK

end CFSG.HardMathSupport.Dickson.Sec6
