module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingNormBasic

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {Y : Type*} [Group Y]

theorem closure_shifted_class_normal {y v : Y} (hv : v ∈ Subgroup.center Y) :
    (Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y)).Normal := by
  constructor
  intro n hn g
  have hmap := MonoidHom.map_closure (MulAut.conj g).toMonoidHom
    ((fun s => v⁻¹ * s) '' involutionPointClass y)
  have hsub : (MulAut.conj g).toMonoidHom '' ((fun s => v⁻¹ * s) '' involutionPointClass y) ⊆
      (fun s => v⁻¹ * s) '' involutionPointClass y := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨g * s * g⁻¹, by simpa only [inv_inv] using class_conj_mem hs g⁻¹, ?_⟩
    have hvc : g * v⁻¹ = v⁻¹ * g := (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hv) g)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← mul_assoc g v⁻¹ s, hvc]
    group
  have hmem : (MulAut.conj g).toMonoidHom n ∈
      (Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y)).map
        (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hmap] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using Subgroup.closure_mono hsub hmem

theorem commutator_le_closure_shifted_class {y v : Y} (hv : v ∈ Subgroup.center Y)
    (hhull : involutionPointHull y = ⊤) :
    commutator Y ≤ Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y) := by
  have := closure_shifted_class_normal (y := y) hv
  apply Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (H := Subgroup.zpowers v)
  · apply eq_top_iff.mpr
    rw [← hhull]
    refine (Subgroup.closure_le _).mpr fun s hs => ?_
    have h := Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers v) :
        v ∈ Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y) ⊔
          Subgroup.zpowers v)
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨s, hs, rfl⟩) :
        v⁻¹ * s ∈ Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y) ⊔
          Subgroup.zpowers v)
    rw [mul_inv_cancel_left] at h
    exact h
  · exact Subgroup.zpowers_isMulCommutative v

theorem mem_center_of_class_mem_center {y s : Y} (hs : s ∈ involutionPointClass y)
    (hsc : s ∈ Subgroup.center Y) : y ∈ Subgroup.center Y := by
  obtain ⟨g, rfl⟩ := hs
  change g⁻¹ * y * g ∈ Subgroup.center Y at hsc
  have hcg := Subgroup.mem_center_iff.mp hsc g
  have hyc : y = g⁻¹ * y * g := by
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = (g⁻¹ * y * g) * g * g⁻¹ := by rw [hcg]
      _ = g⁻¹ * y * g := by group
  rw [hyc]
  exact hsc

theorem bender_derived_of_split {Y : Type} [Group Y] [Finite Y] {M : Subgroup Y} {y v : Y}
    (hy : orderOf y = 2) (hO : CFSG.oddCore Y = ⊥) (hhull : involutionPointHull y = ⊤)
    (hycenter : y ∉ Subgroup.center Y)
    {t : Y} (ht : t ∈ involutionPointClass y) (hyt : Commute y t) (hne : t ≠ y)
    (hv : v ∈ Subgroup.center Y) (hv2 : v ^ 2 = 1)
    (hse : fusionStronglyEmbedded (M.subgroupOf (commutator Y)))
    (hcls : ∀ s ∈ involutionPointClass y, v⁻¹ * s ∈ commutator Y) :
    fusionIsBenderGroup (commutator Y) ∧ commutator (commutator Y) = ⊤ := by
  let K := commutator Y
  have hOK : CFSG.oddCore K = ⊥ := oddCore_eq_bot_of_normal hO K
  have hvc : ∀ g : Y, g * v = v * g := fun g => Subgroup.mem_center_iff.mp hv g
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hv2)
  have hsq : ∀ s ∈ involutionPointClass y, (v⁻¹ * s) ^ 2 = 1 := by
    intro s hs
    have hss := class_mul_self hy hs
    rw [hvinv, pow_two]
    calc v * s * (v * s) = v * (s * v) * s := by group
      _ = v * (v * s) * s := by rw [hvc s]
      _ = (v * v) * (s * s) := by group
      _ = 1 := by rw [← pow_two, hv2, hss, one_mul]
  have hne1 : ∀ s ∈ involutionPointClass y, v⁻¹ * s ≠ 1 := by
    intro s hs h
    have hsv : s = v := by
      calc s = v * (v⁻¹ * s) := by group
        _ = v := by rw [h, mul_one]
    exact hycenter (mem_center_of_class_mem_center hs (by rw [hsv]; exact hv))
  have hord : ∀ (s : Y) (hs : s ∈ involutionPointClass y),
      orderOf (⟨v⁻¹ * s, hcls s hs⟩ : K) = 2 := by
    intro s hs
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hsq s hs) (hne1 s hs)
  have hgen : ∀ N : Subgroup K, N.Normal → Odd N.index → N = ⊤ := by
    intro N hN hodd
    have : N.Normal := hN
    have hT : Subgroup.closure ((fun s => v⁻¹ * s) '' involutionPointClass y) ≤
        N.map K.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨v⁻¹ * s, hcls s hs⟩, mem_of_orderOf_two_of_odd_index hodd (hord s hs), rfl⟩
    have hKN : K ≤ N.map K.subtype := (commutator_le_closure_shifted_class hv hhull).trans hT
    apply eq_top_iff.mpr
    intro k _
    obtain ⟨n, hn, hnk⟩ := hKN k.property
    rw [show k = n from Subtype.ext hnk.symm]
    exact hn
  have hvi : ∀ g : Y, Commute v⁻¹ g := fun g =>
    (show Commute g v from hvc g).symm.inv_left
  have hcommY : Commute (v⁻¹ * y) (v⁻¹ * t) :=
    Commute.mul_left (hvi _) (Commute.mul_right (hvi y).symm hyt)
  have hcomm : Commute (⟨v⁻¹ * y, hcls y (distinguished_mem_pointClass y)⟩ : K)
      ⟨v⁻¹ * t, hcls t ht⟩ := Subtype.ext hcommY.eq
  have hne' : (⟨v⁻¹ * y, hcls y (distinguished_mem_pointClass y)⟩ : K) ≠
      ⟨v⁻¹ * t, hcls t ht⟩ := by
    intro h
    apply hne
    have h' := congrArg (fun w : K => v * (w : Y)) h
    simpa only [mul_inv_cancel_left] using h'.symm
  have hB := fusionIsBenderGroup_of_stronglyEmbedded hOK hgen hse
    (hord y (distinguished_mem_pointClass y)) (hord t ht) hcomm hne'
  exact ⟨hB, commutator_eq_top_of_bender hB (exists_noncommuting_of_stronglyEmbedded hse)⟩

end CFSG.ComponentClassification.AschbacherStrongEmbedding
