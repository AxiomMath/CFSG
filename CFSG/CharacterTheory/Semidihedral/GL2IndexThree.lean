module

public import CFSG.CharacterTheory.Semidihedral.GL2ThreeStructure

public section

namespace CFSG.Semidihedral.GL2IndexThree

universe u v

variable {Y : Type u} [Group Y] [Finite Y]

theorem coset_image_card_three_or_six (C : Subgroup Y) (hC : C.index = 3) :
    Nat.card (MulAction.toPermHom Y (Y ⧸ C)).range = 3 ∨
      Nat.card (MulAction.toPermHom Y (Y ⧸ C)).range = 6 := by
  have hdiv : C.normalCore.index ∣ 6 := by
    have h := C.index_normalCore_dvd_factorial_index
    rw [hC] at h
    change C.normalCore.index ∣ 6 at h
    exact h
  have hthree : 3 ∣ C.normalCore.index := by
    rw [← hC]
    exact Subgroup.index_dvd_of_le C.normalCore_le
  have hpos : 0 < C.normalCore.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : C.normalCore.index ≤ 6 := Nat.le_of_dvd (by decide) hdiv
  obtain ⟨k, hk⟩ := hthree
  have hcases : C.normalCore.index = 3 ∨ C.normalCore.index = 6 := by omega
  simpa only [Subgroup.normalCore_eq_ker, Subgroup.index_ker] using hcases

theorem normalCore_relIndex_one_or_two (C : Subgroup Y) (hC : C.index = 3) :
    C.normalCore.relIndex C = 1 ∨ C.normalCore.relIndex C = 2 := by
  have hcases := coset_image_card_three_or_six C hC
  rw [← Subgroup.index_ker, ← Subgroup.normalCore_eq_ker] at hcases
  have hmul := Subgroup.relIndex_mul_index C.normalCore_le
  rw [hC] at hmul
  rcases hcases with h | h <;> omega

omit [Finite Y] in
theorem normal_card_two_le_center (N : Subgroup Y) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center Y := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  by_cases hxone : x = 1
  · simp [hxone]
  have hxne : (⟨x, hx⟩ : N) ≠ 1 := by
    intro h
    exact hxone (congrArg Subtype.val h)
  let y : N := ⟨g * x * g⁻¹, (inferInstance : N.Normal).conj_mem x hx g⟩
  have hyne : y ≠ 1 := by
    intro h
    have hconj : g * x * g⁻¹ = 1 := congrArg Subtype.val h
    have hmul : g * x = g := by
      simpa using (mul_inv_eq_iff_eq_mul.mp hconj)
    exact hxone (mul_left_cancel (hmul.trans (mul_one g).symm))
  have hyx : y = (⟨x, hx⟩ : N) := (huniq y hyne).trans (huniq _ hxne).symm
  have hconj : g * x * g⁻¹ = x := congrArg Subtype.val hyx
  exact mul_inv_eq_iff_eq_mul.mp hconj

omit [Finite Y] in
theorem central_of_normal_center_eq_zpowers (D : Subgroup Y) [D.Normal]
    (t : Y) (ht : orderOf t = 2)
    (hcenter : (Subgroup.center D).map D.subtype = Subgroup.zpowers t) :
    t ∈ Subgroup.center Y := by
  let Z : Subgroup Y := (Subgroup.center D).map D.subtype
  have hcard : Nat.card Z = 2 := by
    change Nat.card ((Subgroup.center D).map D.subtype) = 2
    rw [hcenter, Nat.card_zpowers, ht]
  have htZ : t ∈ Z := by
    change t ∈ (Subgroup.center D).map D.subtype
    rw [hcenter]
    exact Subgroup.mem_zpowers t
  exact normal_card_two_le_center Z hcard htZ

theorem centralizer_index_ne_three_of_centers (t : Y) (ht : orderOf t = 2)
    (hcenter : (Subgroup.center (Subgroup.centralizer ({t} : Set Y))).map
      (Subgroup.centralizer ({t} : Set Y)).subtype = Subgroup.zpowers t)
    (htwo : ∀ D : Subgroup Y, D ≤ Subgroup.centralizer ({t} : Set Y) →
      D.relIndex (Subgroup.centralizer ({t} : Set Y)) = 2 →
      (Subgroup.center D).map D.subtype = Subgroup.zpowers t) :
    (Subgroup.centralizer ({t} : Set Y)).index ≠ 3 := by
  intro hindex
  let C : Subgroup Y := Subgroup.centralizer ({t} : Set Y)
  have hcorecenter : (Subgroup.center C.normalCore).map C.normalCore.subtype =
      Subgroup.zpowers t := by
    rcases normalCore_relIndex_one_or_two C hindex with hone | htwoindex
    · have heq : C.normalCore = C :=
        le_antisymm C.normalCore_le (Subgroup.relIndex_eq_one.mp hone)
      rw [heq]
      exact hcenter
    · exact htwo C.normalCore C.normalCore_le htwoindex
  have htcentral := central_of_normal_center_eq_zpowers C.normalCore t ht hcorecenter
  have htop : C = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp htcentral g)
  change C.index = 3 at hindex
  rw [htop, Subgroup.index_top] at hindex
  omega

omit [Finite Y] in
theorem map_subgroup_center {H : Type v} [Group H] (e : Y ≃* H)
    (D : Subgroup Y) :
    ((Subgroup.center D).map D.subtype).map e.toMonoidHom =
      (Subgroup.center (D.map e.toMonoidHom)).map (D.map e.toMonoidHom).subtype := by
  let f : D ≃* D.map e.toMonoidHom := e.subgroupMap D
  calc
    ((Subgroup.center D).map D.subtype).map e.toMonoidHom =
        (Subgroup.center D).map (e.toMonoidHom.comp D.subtype) :=
      Subgroup.map_map _ _ _
    _ = (Subgroup.center D).map
        ((D.map e.toMonoidHom).subtype.comp f.toMonoidHom) := rfl
    _ = ((Subgroup.center D).map f.toMonoidHom).map
        (D.map e.toMonoidHom).subtype := (Subgroup.map_map _ _ _).symm
    _ = (Subgroup.center (D.map e.toMonoidHom)).map
        (D.map e.toMonoidHom).subtype :=
      congrArg (fun S => S.map (D.map e.toMonoidHom).subtype)
        (Subgroup.map_center_eq f)

omit [Finite Y] in
theorem subgroupOf_center_map {D C : Subgroup Y} (hDC : D ≤ C) :
    ((Subgroup.center (D.subgroupOf C)).map (D.subgroupOf C).subtype).map C.subtype =
      (Subgroup.center D).map D.subtype := by
  let f : D.subgroupOf C ≃* D := Subgroup.subgroupOfEquivOfLe hDC
  calc
    ((Subgroup.center (D.subgroupOf C)).map (D.subgroupOf C).subtype).map C.subtype =
        (Subgroup.center (D.subgroupOf C)).map
          (C.subtype.comp (D.subgroupOf C).subtype) := Subgroup.map_map _ _ _
    _ = (Subgroup.center (D.subgroupOf C)).map
        (D.subtype.comp f.toMonoidHom) := rfl
    _ = ((Subgroup.center (D.subgroupOf C)).map f.toMonoidHom).map D.subtype :=
      (Subgroup.map_map _ _ _).symm
    _ = (Subgroup.center D).map D.subtype :=
      congrArg (fun S => S.map D.subtype) (Subgroup.map_center_eq f)

omit [Finite Y] in
theorem eq_generator_of_mem_zpowers_order_two (z x : Y) (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) (hxne : x ≠ 1) : x = z := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers z)).mp hcard
  have hzne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hxsub : (⟨x, hx⟩ : Subgroup.zpowers z) ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hzsub : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ≠ 1 := by
    intro h
    exact hzne (congrArg Subtype.val h)
  exact congrArg Subtype.val ((huniq _ hxsub).trans (huniq _ hzsub).symm)

theorem centralizer_index_ne_three_of_model_centers
    {H : Type v} [Group H] (z : H) (hz : orderOf z = 2)
    (hcenter : Subgroup.center H = Subgroup.zpowers z)
    (htwo : ∀ B : Subgroup H, B.index = 2 →
      (Subgroup.center B).map B.subtype = Subgroup.zpowers z)
    (t : Y) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set Y) ≃* H) :
    (Subgroup.centralizer ({t} : Set Y)).index ≠ 3 := by
  let C : Subgroup Y := Subgroup.centralizer ({t} : Set Y)
  let s : C := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hscentral : s ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.property
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hsne : e s ≠ 1 := by
    intro h
    have hseq : s = 1 := e.injective (h.trans e.map_one.symm)
    exact htne (congrArg Subtype.val hseq)
  have hsimage : e s ∈ Subgroup.zpowers z := by
    rw [← hcenter, ← Subgroup.map_center_eq e]
    exact ⟨s, hscentral, rfl⟩
  have hes : e s = z := eq_generator_of_mem_zpowers_order_two z (e s) hz hsimage hsne
  have hmappow : (Subgroup.zpowers s).map e.toMonoidHom = Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hes
  have hCcenter : Subgroup.center C = Subgroup.zpowers s := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact (Subgroup.map_center_eq e).trans (hcenter.trans hmappow.symm)
  have hCambient : (Subgroup.center C).map C.subtype = Subgroup.zpowers t := by
    rw [hCcenter, MonoidHom.map_zpowers]
    rfl
  apply centralizer_index_ne_three_of_centers t ht hCambient
  intro D hDC hrel
  let A : Subgroup C := D.subgroupOf C
  let B : Subgroup H := A.map e.toMonoidHom
  have hBindex : B.index = 2 := by
    exact (Subgroup.index_map_equiv A e).trans hrel
  have hAcenter : (Subgroup.center A).map A.subtype = Subgroup.zpowers s := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact (map_subgroup_center e A).trans ((htwo B hBindex).trans hmappow.symm)
  calc
    (Subgroup.center D).map D.subtype =
        ((Subgroup.center A).map A.subtype).map C.subtype :=
      (subgroupOf_center_map hDC).symm
    _ = (Subgroup.zpowers s).map C.subtype := by rw [hAcenter]
    _ = Subgroup.zpowers t := MonoidHom.map_zpowers _ _

theorem involution_centralizer_index_ne_three
    (t : Y) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set Y) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (Subgroup.centralizer ({t} : Set Y)).index ≠ 3 := by
  exact centralizer_index_ne_three_of_model_centers
    GL2ThreeStructure.z GL2ThreeStructure.z_order GL2ThreeStructure.centerH
    GL2ThreeStructure.center_index_two t ht e

end CFSG.Semidihedral.GL2IndexThree
