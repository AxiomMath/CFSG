module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0Model
public import CFSG.Sporadic.SuzRecog.Generation
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.LargeExtraspecial

section Dat


@[expose] noncomputable def suzT1 : ↥suzT :=
  ⟨suzInv 1, suzM_le_suzT (CFSG.Sporadic.SuzRecog.suzInv_mem_suzM (by norm_num))⟩

@[expose] noncomputable def suzQT : Subgroup ↥suzT := coord_qVec.Q.subgroupOf suzT

@[expose] def USuz : Prop :=
  ∀ F X : Subgroup ↥suzT, F ≤ Subgroup.centralizer ({suzT1} : Set ↥suzT) →
    X ≤ Subgroup.centralizer ({suzT1} : Set ↥suzT) → IsElemAbelian 3 F → Nat.card F = 3 ^ 3 →
    IsPGroup 2 X → F ≤ Subgroup.normalizer (X : Set ↥suzT) → X ≤ suzQT

theorem Q_le_suzT : coord_qVec.Q ≤ suzT := fun _ hx =>
  suzM_le_suzT ((invE_le_centM (by norm_num) (Q_le_invE hx)).2)

theorem normalizer_Q_of_comm {g : Equiv.Perm (Fin 1782)} (hgT : g ∈ suzT)
    (hgt : g * suzInv 1 = suzInv 1 * g) :
    g ∈ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) := by
  by_cases hgM : g ∈ suzM
  · have hgE : g ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgt, hgM⟩
    exact (invE_le hgE).1
  · have hg₀D := q0OuterGen_mem_invD
    rw [invD_eq_centT (by norm_num)] at hg₀D
    obtain ⟨hg₀t, hg₀T⟩ := Subgroup.mem_inf.mp hg₀D
    have hg₀N : q0OuterGen ∈ Subgroup.normalizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) :=
      coord_qVec.mem_normalizer (Subgroup.mem_centralizer_singleton_iff.mp hg₀t) fun i hi => by
        rw [q0OuterGen_conj hi]
        exact coord_qVec.mem_Q_iff.mpr ⟨_, (oact_lt i hi).1, _, (oact_lt i hi).2, rfl⟩
    have hcM : q0OuterGen⁻¹ * g ∈ suzM := by
      have h := (Subgroup.mul_mem_iff_of_index_two suzM_index_T
        (a := (⟨q0OuterGen, hg₀T⟩ : ↥suzT)⁻¹) (b := ⟨g, hgT⟩)).mpr
        ⟨fun h => absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) q0OuterGen_not_mem,
          fun h => absurd (Subgroup.mem_subgroupOf.mp h) hgM⟩
      exact Subgroup.mem_subgroupOf.mp h
    have hct : (q0OuterGen⁻¹ * g) * suzInv 1 = suzInv 1 * (q0OuterGen⁻¹ * g) := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg₀t
      calc (q0OuterGen⁻¹ * g) * suzInv 1 = q0OuterGen⁻¹ * (suzInv 1 * g) := by rw [mul_assoc, hgt]
        _ = q0OuterGen⁻¹ * (suzInv 1 * q0OuterGen) * q0OuterGen⁻¹ * g := by group
        _ = q0OuterGen⁻¹ * (q0OuterGen * suzInv 1) * q0OuterGen⁻¹ * g := by rw [h1]
        _ = suzInv 1 * (q0OuterGen⁻¹ * g) := by group
    have hcE : q0OuterGen⁻¹ * g ∈ invE 1 := by
      rw [invE_eq_centM (by norm_num)]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hct, hcM⟩
    have := Subgroup.mul_mem _ hg₀N (invE_le hcE).1
    rwa [mul_inv_cancel_left] at this

theorem twoCentralData_suz (hU : USuz) : TwoCentralData 3 suzT1 suzQT := by
  refine ⟨?_, ?_, coord_qVec.t_mem, fun h => coord_qVec.t_ne (congrArg Subtype.val h), ?_, ?_, ?_,
    hU⟩
  · have h1 : timmesfeldIsExtraspecial ↥coord_qVec.Q :=
      (Bridge.timmesfeldIsExtraspecial_iff ↥coord_qVec.Q).2 coord_qVec.isExtraspecialPGroup_Q.1
    exact Bridge.timmesfeldIsExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe Q_le_suzT).symm h1
  · rw [suzQT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_suzT).toEquiv, coord_qVec.card_Q]
    norm_num
  · intro p hp
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (invE_le (Q_le_invE hp)).2)
  · intro g hgz hgc
    have hcent : (g : Equiv.Perm (Fin 1782)) ∈
        Subgroup.centralizer (coord_qVec.Q : Set (Equiv.Perm (Fin 1782))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val (hgc ⟨q, Q_le_suzT hq⟩ hq)
    exact Subgroup.zpowers_le.2 coord_qVec.t_mem (mem_zpowers_of_mem_centralizer_Q g.2 hcent)
  · intro g hgz
    have hN := normalizer_Q_of_comm g.2 (congrArg Subtype.val hgz)
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    have := Subgroup.mem_normalizer_iff.1 hN (h : Equiv.Perm (Fin 1782))
    simpa [suzQT, Subgroup.mem_subgroupOf] using this

end Dat

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
