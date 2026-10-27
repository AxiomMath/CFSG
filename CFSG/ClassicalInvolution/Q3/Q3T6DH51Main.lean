module

public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Conj
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Layer
public import CFSG.ClassicalInvolution.Q3.Q3T6DSOrb

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section Main


theorem res20_7Hyp51AtThree_proved (hD4 : D4InnerAlphaThree) : Res20_7Hyp51AtThree := by
  intro G _ _ _ K K' J S R R' W V z t d c4 a ha ha1 ha2
  have hΩ := d.hyp
  have hBelow : CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp d.below
  have hnab : ∃ x y : G, x * y ≠ y * x := d.branch.nonabelian
  have hKΩ : K ∈ CoreAssembly.conjClass K := d.late_mem_K
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := d.late_mem_K'
  have hzK : IsUniqueInvolution K z := d.viol.hzK
  have hzK' : IsUniqueInvolution K' z := d.late_hzK'
  have hcK : IsClassicalMember3 K z := d.branch.member.toQ3 (by norm_num)
  have hcK' : IsClassicalMember3 K' z := isClassicalMember3_of_unique hΩ hK'Ω hzK'
  have hΩ3 : InClass3 (CoreAssembly.conjClass K) :=
    { nonempty := ⟨K, hKΩ⟩
      conjInvariant := hΩ.conjInvariant
      generated := d.branch.gen
      classical := fun L hL => by
        obtain ⟨w, hw⟩ := hΩ.classical L hL
        exact ⟨w, hw.toQ3 (by norm_num)⟩ }
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzK.commute_of_mem hw).symm
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzK'.commute_of_mem hw).symm
  have hMz : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := sup_le hKz hK'z
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := d.late_K'_le
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := d.late_K_le
  have hz2 : z * z = 1 := hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have haz : a * z = z * a := d.s_comm_z ha.1.1
  have hat : a * t = t * a := d.s_comm_t ha
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have haK : a ∈ trivialOnQuot K := ⟨d.cent_le_normalizer ha.1, fun l hl => d.s_comm_K ha hl⟩
  have haK' : a ∈ trivialOnQuot K' :=
    ⟨d.cent_le_normalizer' ha.1, fun l hl => d.s_comm_K' ha hl⟩
  have hzK_tq : z ∈ trivialOnQuot K := ExactLayer.mem_trivialOnQuot_of_le_centralizer hKz
  have hzK'_tq : z ∈ trivialOnQuot K' := ExactLayer.mem_trivialOnQuot_of_le_centralizer hK'z
  have hza : z ≠ a := fun e => d.s_a_not_mem_closure c4 ha ha1 (by
    rw [← e]
    exact Subgroup.subset_closure (by simp))
  have ht1 : t ≠ 1 := d.viol.hzJ.ne_one
  have htz : t ≠ z := d.late_ne_inv
  obtain ⟨g, hgM, hga, hgt⟩ := exists_conj_mem_exactCore3_sup hcK hcK' hc2 haK haK' hKN' hK'N
    d.htKK ht2 hat
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp (hMz hgM)
  have hgzg : g * z * g⁻¹ = z := by rw [hgz]; group
  have hgag : g * a * g⁻¹ = a := by rw [← hga]; group
  set t' : G := g * t * g⁻¹ with ht'def
  have ht'2 : t' * t' = 1 := by
    calc t' * t' = g * (t * t) * g⁻¹ := by rw [ht'def]; group
      _ = 1 := by rw [ht2]; group
  have hzt' : z * t' = t' * z := by
    calc z * t' = (g * z * g⁻¹) * (g * t * g⁻¹) := by rw [hgzg]
      _ = g * (z * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hzt]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = t' * z := by rw [hgzg]
  have hat' : a * t' = t' * a := by
    calc a * t' = (g * a * g⁻¹) * (g * t * g⁻¹) := by rw [hgag]
      _ = g * (a * t) * g⁻¹ := by group
      _ = g * (t * a) * g⁻¹ := by rw [hat]
      _ = (g * t * g⁻¹) * (g * a * g⁻¹) := by group
      _ = t' * a := by rw [hgag]
  have ht'1 : t' ≠ 1 := fun e => ht1 (by
    have : t = g⁻¹ * t' * g := by rw [ht'def]; group
    rw [this, e]
    group)
  have ht'z : t' ≠ z := fun e => htz (by
    have : t = g⁻¹ * t' * g := by rw [ht'def]; group
    rw [this, e]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group)
  have hB'ab : IsElemAbelian 2 (Subgroup.closure ({z, t', a} : Set G)) :=
    isElemAbelian_closure_three hz2 ht'2 ha2 hzt' haz.symm hat'.symm
  have hB : conjSub g (Subgroup.closure ({z, t, a} : Set G)) =
      Subgroup.closure ({z, t', a} : Set G) := by
    rw [conjSub_closure_triple, hgzg, hgag]
  have hzB : z ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have ht'B : t' ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.subset_closure (by simp)
  have hlift : ∀ c : G, g * c * g⁻¹ = c →
      Hyp51At (Subgroup.closure ({z, t', a} : Set G)) c →
        Hyp51At (Subgroup.closure ({z, t, a} : Set G)) c := fun c hc h =>
    (ExactLayer.hyp51At_conj g c _).mp (by rw [hB, hc]; exact h)
  refine ⟨hlift a hgag ?_, hlift (a * z) ?_ ?_⟩
  · exact hyp51At_of_twin_layer3 hD4 hΩ3 hBelow hnab hcK hcK' hzK hzK' ⟨hKΩ, haK⟩
      ⟨hK'Ω, haK'⟩ hB'ab hzB ht'B haB rfl ha1 hza ht'1 ht'z hgt
  · calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a * z := by rw [hgag, hgzg]
  · have haz1 : a * z ≠ 1 := fun e => hza (by
      have h1 : a = z⁻¹ := eq_inv_of_mul_eq_one_left e
      rw [h1]
      exact (inv_eq_of_mul_eq_one_right hz2).symm)
    have hzaz : z ≠ a * z := fun e => ha1 (by
      have : a * z = 1 * z := by rw [← e, one_mul]
      exact mul_right_cancel this)
    have hazB : a * z ∈ Subgroup.closure ({z, t', a} : Set G) := Subgroup.mul_mem _ haB hzB
    have hdsup : t' ∈ exactCore3 (a * z) K ⊔ exactCore3 (a * z) K' := by
      rw [exactCore3_mul_eq hKz, exactCore3_mul_eq hK'z]
      exact hgt
    exact hyp51At_of_twin_layer3 hD4 hΩ3 hBelow hnab hcK hcK' hzK hzK'
      ⟨hKΩ, (trivialOnQuot K).mul_mem haK hzK_tq⟩
      ⟨hK'Ω, (trivialOnQuot K').mul_mem haK' hzK'_tq⟩ hB'ab hzB ht'B hazB
      (closure_triple_mul_right hz2).symm haz1 hzaz ht'1 ht'z hdsup

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6D
