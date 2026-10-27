module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L3Rank
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.U62Sylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SuzOddCore Cover


theorem exists_suzD_subgroup_suzM : ∃ K : Subgroup ↥suzM, Nonempty (↥K ≃* ↥suzD) := by
  obtain ⟨K, hKM, hKc, hKp, hKcard, -⟩ := suz_pinned_data
  have hperf : Group.IsPerfect ↥K := isPerfect_iff.mpr hKp
  have ht0 : suzInv 0 ∈ suzM := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht0M, -⟩ := suz_row_facts
    exact ht0M
  have hP : SuzPair (Equiv.Perm (Fin 1782)) suzM K (suzInv 0) :=
    ⟨ht0, orderOf_eq_two_of_mul_self (suzInv_sq (by norm_num)) (suzInv_ne_one (by norm_num)), hKM,
      hKc, hperf, hKcard⟩
  obtain ⟨e⟩ := suz_K_equiv hP suzM.subtype suzM.subtype_injective (fun x => x.2) rfl
  exact ⟨K.subgroupOf suzM, ⟨(Subgroup.subgroupOfEquivOfLe hKM).trans e⟩⟩

theorem suz_cover_rank (hb : LieModel ↥suzD .PSL 3 2 2) {X : Type} [Group X] [Finite X]
    (hS : IsSporadic (X ⧸ center X) .Suz) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨f⟩ := suz_equiv_of_isSporadic hS
  obtain ⟨K', ⟨e⟩⟩ := exists_suzD_subgroup_suzM
  let ψ : X →* ↥suzM := f.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hψ : Function.Surjective ψ := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ∀ x : X, ψ x = 1 → x ∈ center X := fun x hx => by
    have h1 : f (QuotientGroup.mk x) = 1 := hx
    rw [map_eq_one_iff f f.injective, QuotientGroup.eq_one_iff] at h1
    exact h1
  let J : Subgroup X := K'.comap ψ
  let φ : ↥J →* ↥K' := ψ.subgroupComap K'
  have hφ : Function.Surjective φ := ψ.subgroupComap_surjective K' hψ
  have hφk : φ.ker ≤ center ↥J := by
    intro x hx
    have h1 : ψ (x : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 := hψk _ h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
  have hL : LieModel ↥K' .PSL 3 2 2 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hb
  exact (three_le_pRank_of_cover_L3 le_rfl hL hφ hφk).trans
    (CFSG.RankThree.GroupTheory.SteinbergBY.pRank_subgroup_le_pRank (by norm_num) J)

end CFSG.EvenSporadicStandard.Induction
