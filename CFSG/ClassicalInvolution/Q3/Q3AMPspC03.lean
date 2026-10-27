module

public import CFSG.ClassicalInvolution.Q3.Q3AMPspC02
public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Main


theorem pspVertexC_proved : PspVertexCLeaf := by
  intro G _ _ _ Ω K J S R T W z t K' hset t₁ t₂ t₃ R₁ R₂ R₃ hax
  have hbad := hset.bad
  have hstd := hbad.std
  have hnab := hbad.nonabelian
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have eKJ : EdgeSetup K z K J z t :=
    hbad.toEdgeSetup hset.intrinsic hstd.stand.mem hstd.hJ hax.uniq₁ hax.uniq₂
  have eKK' : EdgeSetup K z K K' z (z * t) :=
    hbad.toEdgeSetup hset.intrinsic hstd.stand.mem hset.nbrK hax.uniq₁ hax.uniq₃
  have eJK' : EdgeSetup K z J K' t (z * t) :=
    hbad.toEdgeSetup hset.intrinsic hstd.hJ.1 hset.nbrJ hax.uniq₂ hax.uniq₃
  have hz₁sq : z * z = 1 := hax.z₁_sq
  have hz₂sq : t * t = 1 := hax.z₂_sq
  have hzt : z * t = t * z := hax.z_comm
  have ht1 : t ≠ 1 := hax.uniq₂.ne_one
  have ht₁K : t₁ ∈ K := hax.syl₁.1 hax.mem₁
  have ht₂J : t₂ ∈ J := hax.syl₂.1 hax.mem₂
  have ht₃K' : t₃ ∈ K' := hax.syl₃.1 hax.mem₃
  have hc12 : t₁ * t₂ = t₂ * t₁ := hax.comm₁₂ t₁ hax.mem₁ t₂ hax.mem₂
  have hc13 : t₁ * t₃ = t₃ * t₁ := hax.comm₁₃ t₁ hax.mem₁ t₃ hax.mem₃
  have hc23 : t₂ * t₃ = t₃ * t₂ := hax.comm₂₃ t₂ hax.mem₂ t₃ hax.mem₃
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, t, t₁ * t₂ * t₃} : Set G)) := by
    rw [closure_triple_eq_insert]
    exact hax.isElemAbelian_axis
  have c1 : z * (z * t) = (z * t) * z := by
    calc z * (z * t) = z * (t * z) := by rw [hzt]
      _ = (z * t) * z := (mul_assoc _ _ _).symm
  have c2 : t * (z * t) = (z * t) * t := by
    calc t * (z * t) = (t * z) * t := (mul_assoc _ _ _).symm
      _ = (z * t) * t := by rw [← hzt]
  have s1 : z * (z * t) = t := by rw [← mul_assoc, hz₁sq, one_mul]
  have s2 : t * (z * t) = z := by
    calc t * (z * t) = (t * z) * t := (mul_assoc _ _ _).symm
      _ = (z * t) * t := by rw [← hzt]
      _ = z * (t * t) := mul_assoc _ _ _
      _ = z := by rw [hz₂sq, mul_one]
  have s3 : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * (z * t)) := mul_assoc _ _ _
      _ = z * z := by rw [s2]
      _ = 1 := hz₁sq
  refine ⟨?_, ?_, ?_⟩
  · exact hyp51At_vertex_of_edges hnab hBelow eKJ eKK' hz₁sq hzt c1 s2 hax.ne.symm ht₁K ht₂J
      ht₃K' (hax.comm₁₂ z hax.z_mem₁ t₂ hax.mem₂) (hax.comm₁₃ z hax.z_mem₁ t₃ hax.mem₃)
      (mul_assoc _ _ _) hB (closure_triple_perm z t _)
  · refine hyp51At_vertex_of_edges hnab hBelow eKJ.symm eJK' hz₂sq hzt.symm c2 s1 hax.ne ht₂J
      ht₁K ht₃K' (hax.comm₁₂ t₁ hax.mem₁ t hax.z_mem₂).symm
      (hax.comm₂₃ t hax.z_mem₂ t₃ hax.mem₃) ?_ hB (closure_triple_swap z t _)
    calc t₁ * t₂ * t₃ = (t₂ * t₁) * t₃ := by rw [hc12]
      _ = t₂ * (t₁ * t₃) := mul_assoc _ _ _
  · have hzt₁ : z * t₁ = t₁ * z := (isUniqueInvolution_comm hax.uniq₁ ht₁K).symm
    have htt₁ : t * t₁ = t₁ * t := (hax.comm₁₂ t₁ hax.mem₁ t hax.z_mem₂).symm
    have hzt₂ : z * t₂ = t₂ * z := hax.comm₁₂ z hax.z_mem₁ t₂ hax.mem₂
    have htt₂ : t * t₂ = t₂ * t := (isUniqueInvolution_comm hax.uniq₂ ht₂J).symm
    have hac : z ≠ z * t := fun h => ht1 (mul_left_cancel (a := z) (by rw [mul_one]; exact h.symm))
    refine hyp51At_vertex_of_edges hnab hBelow eKK'.symm eJK'.symm s3 c1.symm c2.symm rfl hac
      ht₃K' ht₁K ht₂J ?_ ?_ ?_ hB (closure_triple_mul t _ hz₁sq).symm
    · calc z * t * t₁ = z * (t * t₁) := mul_assoc _ _ _
        _ = z * (t₁ * t) := by rw [htt₁]
        _ = (z * t₁) * t := (mul_assoc _ _ _).symm
        _ = (t₁ * z) * t := by rw [hzt₁]
        _ = t₁ * (z * t) := mul_assoc _ _ _
    · calc z * t * t₂ = z * (t * t₂) := mul_assoc _ _ _
        _ = z * (t₂ * t) := by rw [htt₂]
        _ = (z * t₂) * t := (mul_assoc _ _ _).symm
        _ = (t₂ * z) * t := by rw [hzt₂]
        _ = t₂ * (z * t) := mul_assoc _ _ _
    · calc t₁ * t₂ * t₃ = t₁ * (t₂ * t₃) := mul_assoc _ _ _
        _ = t₁ * (t₃ * t₂) := by rw [hc23]
        _ = (t₁ * t₃) * t₂ := (mul_assoc _ _ _).symm
        _ = (t₃ * t₁) * t₂ := by rw [hc13]
        _ = t₃ * (t₁ * t₂) := mul_assoc _ _ _

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
