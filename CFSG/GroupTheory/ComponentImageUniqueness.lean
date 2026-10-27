module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.PerfectCentralizer

public section

namespace CFSG.ComponentImage

open Subgroup

variable {X Y : Type*} [Group X] [Group Y]

theorem exists_noncommuting_map_of_isSimpleGroup (ψ : X →* Y) {C : Subgroup X}
    (hC : CFSG.IsComponent C) {H : Subgroup Y} (hmap : C.map ψ = H)
    (hsimple : IsSimpleGroup ↥H) :
    ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a := by
  classical
  haveI : IsSimpleGroup ↥H := hsimple
  haveI : Group.IsPerfect ↥C := hC.1.1
  haveI : Group.IsPerfect ↥(C.map ψ) := Group.IsPerfect.map (H := C) ψ
  haveI : Group.IsPerfect ↥H := by
    have eH : ↥(C.map ψ) ≃* ↥H := MulEquiv.subgroupCongr hmap
    exact Group.IsPerfect.ofSurjective (f := eH.toMonoidHom) eH.surjective
  have hnc : ¬ IsMulCommutative ↥H := Group.IsPerfect.not_isMulCommutative (G := ↥H)
  rw [isMulCommutative_iff] at hnc
  push Not at hnc
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨a.1, ?_, b.1, ?_, fun h => hab (Subtype.ext h)⟩
  · rw [hmap]
    exact a.2
  · rw [hmap]
    exact b.2

theorem isComponent_eq_of_map_eq_of_noncommuting (ψ : X →* Y) [Finite X] {C C' : Subgroup X}
    (hC : CFSG.IsComponent C) (hC' : CFSG.IsComponent C') (hmap : C.map ψ = C'.map ψ)
    (hna : ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a) : C = C' := by
  by_contra hne
  have hcomm : ⁅C, C'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hC hC').resolve_left hne
  have hmapcomm : ⁅C.map ψ, C'.map ψ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  have hD : ⁅C.map ψ, C.map ψ⁆ = ⊥ := by
    have h := hmapcomm
    rwa [← hmap] at h
  have hle : C.map ψ ≤ Subgroup.centralizer (C.map ψ : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hD
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  exact hab ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm

theorem mem_normalizer_of_map_mem_normalizer (ψ : X →* Y) [Finite X] {C : Subgroup X}
    (hC : CFSG.IsComponent C)
    (hna : ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a) {x : X}
    (hx : ψ x ∈ Subgroup.normalizer (C.map ψ : Set Y)) :
    x ∈ Subgroup.normalizer (C : Set X) := by
  classical
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  let Cx : Subgroup X := C.map (MulAut.conj x).toMonoidHom
  have hCx : CFSG.IsComponent Cx :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hC
  have hcomp : ψ.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (ψ x)).toMonoidHom.comp ψ := by
    ext y
    simp [MulAut.conj_apply]
  have hmap : Cx.map ψ = C.map ψ := by
    show (C.map (MulAut.conj x).toMonoidHom).map ψ = C.map ψ
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact hx
  have hEq : C = Cx :=
    isComponent_eq_of_map_eq_of_noncommuting ψ hC hCx hmap.symm hna
  change Cx = C
  exact hEq.symm

theorem mem_centralizer_of_map_mem_centralizer (ψ : X →* Y) [Finite X] {C : Subgroup X}
    (hC : CFSG.IsComponent C)
    (hna : ∃ a ∈ C.map ψ, ∃ b ∈ C.map ψ, a * b ≠ b * a) {x : X}
    (hx : ψ x ∈ Subgroup.centralizer (C.map ψ : Set Y)) :
    x ∈ Subgroup.centralizer (C : Set X) := by
  classical
  have hxN : ψ x ∈ Subgroup.normalizer (C.map ψ : Set Y) :=
    Subgroup.centralizer_le_normalizer (C.map ψ : Set Y) hx
  have hxC : x ∈ Subgroup.normalizer (C : Set X) :=
    mem_normalizer_of_map_mem_normalizer ψ hC hna hxN
  let ρ : C →* Y := ψ.comp C.subtype
  have hker_le : ρ.ker ≤ Subgroup.center C := by
    have hN : (ρ.ker).Normal := MonoidHom.normal_ker ρ
    have hne : ρ.ker ≠ ⊤ := by
      intro htop
      have hbot : C.map ψ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
        intro c hc
        have hmem : (⟨c, hc⟩ : C) ∈ ρ.ker := by
          rw [htop]
          exact Subgroup.mem_top _
        exact MonoidHom.mem_ker.mp hmem)
      obtain ⟨a, ha, b, hb, hab⟩ := hna
      have ha1 : a = 1 := Subgroup.mem_bot.mp (hbot ▸ ha)
      have hb1 : b = 1 := Subgroup.mem_bot.mp (hbot ▸ hb)
      exact hab (by simp [ha1, hb1])
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.1 hN with h | h
    · exact absurd h hne
    · exact h
  let α : MulAut C := C.normalizerMonoidHom ⟨x, hxC⟩
  have hα : α = 1 := by
    refine CFSG.GroupTheory.MulAut.eq_one_of_mul_mem_center hC.1.1 α ?_
    intro c
    apply hker_le
    rw [MonoidHom.mem_ker]
    have hcentral : ψ (c : X) * ψ x = ψ x * ψ (c : X) :=
      Subgroup.mem_centralizer_iff.mp hx (ψ (c : X)) (Subgroup.mem_map_of_mem ψ c.2)
    have hαc : ((α c : C) : X) = x * (c : X) * x⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨x, hxC⟩ c
    have h1 : ρ (α c) = ρ c := by
      show ψ ((α c : C) : X) = ψ (c : X)
      rw [hαc, map_mul, map_mul, map_inv, ← hcentral]
      group
    show ρ (α c * c⁻¹) = 1
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hαc : α ⟨c, hc⟩ = ⟨c, hc⟩ := by
    rw [hα]
    rfl
  have hcoe : ((α ⟨c, hc⟩ : C) : X) = x * c * x⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨x, hxC⟩ ⟨c, hc⟩
  have hxc : x * c * x⁻¹ = c := by
    rw [← hcoe, hαc]
  calc
    c * x = (x * c * x⁻¹) * x := by rw [hxc]
    _ = x * c := by group

theorem ker_comp_subtype_eq_center (ψ : X →* Y) {C : Subgroup X}
    (hC : CFSG.IsComponent C) {H : Subgroup Y} (hmap : C.map ψ = H)
    (hsimple : IsSimpleGroup ↥H) :
    (ψ.comp C.subtype).ker = Subgroup.center C := by
  classical
  let ρ : C →* Y := ψ.comp C.subtype
  haveI : IsSimpleGroup ↥H := hsimple
  have hHne : H ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot H).mp inferInstance
  have hnot : ¬ C ≤ ψ.ker := by
    intro hle
    have hbot : C.map ψ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hle
    exact hHne (hmap ▸ hbot)
  have hqmap : CFSG.IsQuasisimple (C.map ψ) :=
    CFSG.LocalCores.isQuasisimple_map hC.1 ψ hnot
  have hnc : ¬ IsMulCommutative ↥H := by
    haveI : Group.IsPerfect ↥(C.map ψ) := hqmap.1
    haveI : Group.IsPerfect ↥H := by
      have eH : ↥(C.map ψ) ≃* ↥H := MulEquiv.subgroupCongr hmap
      exact Group.IsPerfect.ofSurjective (f := eH.toMonoidHom) eH.surjective
    exact Group.IsPerfect.not_isMulCommutative (G := ↥H)
  have hZ : Subgroup.center ↥H = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥H) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
  have hkerne : ρ.ker ≠ ⊤ := by
    intro htop
    apply hnot
    intro c hc
    have hmem : (⟨c, hc⟩ : C) ∈ ρ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mp hmem
  apply le_antisymm
  · intro c hc
    have hN : (ρ.ker).Normal := MonoidHom.normal_ker ρ
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.1 hN with h | h
    · exact absurd h hkerne
    · exact h hc
  · intro c hc
    rw [MonoidHom.mem_ker]
    have hmem_map : ψ (c : X) ∈ C.map ψ := Subgroup.mem_map_of_mem ψ c.2
    have hcH : (⟨ψ (c : X), hmap ▸ hmem_map⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      change (y : Y) * ψ (c : X) = ψ (c : X) * (y : Y)
      have hy : (y : Y) ∈ C.map ψ := by
        rw [hmap]
        exact y.2
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
      rw [← hay]
      have hcomm : a * (c : X) = (c : X) * a := by
        have hsub : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ :=
          Subgroup.mem_center_iff.mp hc ⟨a, ha⟩
        simpa using congrArg (fun z : C => (z : X)) hsub
      calc
        ψ a * ψ (c : X) = ψ (a * (c : X)) := by rw [map_mul]
        _ = ψ ((c : X) * a) := by rw [hcomm]
        _ = ψ (c : X) * ψ a := by rw [map_mul]
    have hmem : (⟨ψ (c : X), hmap ▸ hmem_map⟩ : ↥H) ∈ (⊥ : Subgroup ↥H) := by
      rw [← hZ]
      exact hcH
    simpa using Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)

end CFSG.ComponentImage
