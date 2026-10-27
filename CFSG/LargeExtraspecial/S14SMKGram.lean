module

public import CFSG.LargeExtraspecial.S14SMKLbar
public import CFSG.LargeExtraspecial.SMod20UaOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20 QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def rhoM (S : Setting G) : S.M →* S.Mbar :=
  S.ρ.codRestrict S.Mbar fun m => ⟨m, rfl⟩

theorem coe_rhoM (m : S.M) : (rhoM S m : S.O) = S.ρ m := rfl

theorem exists_rhoM_eq (m : S.Mbar) : ∃ x : S.M, rhoM S x = m := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp m.2
  exact ⟨x, Subtype.ext hx⟩

omit [Finite G] in
theorem mul_conj_mem (m : S.M) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG ∧
      ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ≠ S.z := by
  have e : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by
    group
  rw [e]
  refine ⟨S.conj_mem_QG m.2 haQ, fun h => hne ?_⟩
  have hz : (m : G)⁻¹ * S.z * (m : G) = S.z := by
    rw [mul_assoc, ← S.z_comm m.2, ← mul_assoc, inv_mul_cancel, one_mul]
  calc g * S.z * g⁻¹ = (m : G)⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * (m : G) := by group
    _ = S.z := by rw [h, hz]

section Planes

variable
  (ψ : Mbar0 S ≃* T46)

theorem map_conj_UA {π : Equiv.Perm (Fin 693)} (hπ : IsPolarAut π) {i j : ℕ}
    (hW : ⇑π '' wPlane i = wPlane j) : (UA i).map (MulAut.conj π).toMonoidHom = UA j := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact conj_mem_UA hπ hW hu
  · intro u hu
    refine ⟨π⁻¹ * u * π, ?_, ?_⟩
    · have := conj_mem_UA hπ.inv (image_wPlane_inv hW) hu
      rwa [inv_inv] at this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem map_Lbar_mul {g : G} (m : S.M) :
    ((S.Lbar ((m : G) * g)).subgroupOf S.Mbar).map (piM S ψ) =
      (((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ)).map
        (MulAut.conj (piM S ψ (rhoM S m))).toMonoidHom := by
  rw [S.Lbar_mul m.2, map_map]
  ext π
  simp only [mem_map, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := mem_subgroupOf.mp hx
    have hxe : x = rhoM S m * ⟨s, S.Lbar_le_Mbar g hs⟩ * (rhoM S m)⁻¹ := by
      apply Subtype.ext
      rw [← hsx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_rhoM]
    refine ⟨⟨s, S.Lbar_le_Mbar g hs⟩, mem_subgroupOf.mpr hs, ?_⟩
    subst hxe
    simp only [map_mul, map_inv]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨rhoM S m * y * (rhoM S m)⁻¹, mem_subgroupOf.mpr ⟨(y : S.O), mem_subgroupOf.mp hy, ?_⟩,
      ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_rhoM]
    · simp only [map_mul, map_inv]

theorem planeOf_mul (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M) :
    planeOf S ψ ((m : G) * g) = planeHom S ψ (rhoM S m) (planeOf S ψ g) := by
  obtain ⟨haQ', hne'⟩ := mul_conj_mem m haQ hne
  rw [planeOf_eq_iff ψ hw haQ' hne', map_Lbar_mul ψ m, planeOf_spec ψ hw haQ hne]
  exact map_conj_UA (isPolarAut_piM ψ _) (image_wPlane_piM ψ _ _)

theorem Lbar_eq_of_planeOf_eq (hw : S.width = 10) {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z)
    (he : planeOf S ψ h = planeOf S ψ g) : S.Lbar h = S.Lbar g := by
  have e : ((S.Lbar h).subgroupOf S.Mbar).map (piM S ψ) =
      ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) := by
    rw [planeOf_spec ψ hw hbQ hbne, planeOf_spec ψ hw haQ hne, he]
  have e2 := map_injective (piM_injective ψ) e
  rw [subgroupOf_inj, inf_eq_left.mpr (S.Lbar_le_Mbar h),
    inf_eq_left.mpr (S.Lbar_le_Mbar g)] at e2
  exact e2

theorem cl_eq_of_planeOf_eq [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10) {g h : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : h * S.z * h⁻¹ ∈ S.QG)
    (hbne : h * S.z * h⁻¹ ≠ S.z) (he : planeOf S ψ h = planeOf S ψ g) :
    S.cl (h * S.z * h⁻¹) = S.cl (g * S.z * g⁻¹) :=
  (Lbar_eq_iff_cl_eq_of_noA2 (by omega) haQ hne
    (noA2_of_insp5 I hw ⟨ψ.trans tpsuT46.symm⟩ haQ hne) hbQ hbne).mp
    (Lbar_eq_of_planeOf_eq ψ hw haQ hne hbQ hbne he)

theorem exists_piM_rhoM {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) :
    ∃ m : S.M, piM S ψ (rhoM S m) = t := by
  obtain ⟨m₀, hm₀⟩ := exists_piM_eq ψ ht
  obtain ⟨m, hm⟩ := exists_rhoM_eq (m₀ : S.Mbar)
  exact ⟨m, by rw [hm, hm₀]⟩

theorem exists_planeOf_eq (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (j : Fin 891) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧ planeOf S ψ h = j := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero (planeOf S ψ g).2
  obtain ⟨y, hy, hyW⟩ := exists_image_wPlane_zero j.2
  obtain ⟨m, hm⟩ := exists_piM_rhoM ψ (T46.mul_mem hy (T46.inv_mem hx))
  obtain ⟨haQ', hne'⟩ := mul_conj_mem m haQ hne
  refine ⟨(m : G) * g, haQ', hne', ?_⟩
  rw [planeOf_mul ψ hw haQ hne m, planeHom_eq_iff, hm, Equiv.Perm.coe_mul, Set.image_comp,
    image_wPlane_inv hxW, hyW]

end Planes

@[expose] noncomputable def xcl
    (S : Setting G) (ψ : Mbar0 S ≃* T46) (i : ℕ) : S.Qt :=
  Classical.epsilon fun v : S.Qt => ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧
    (planeOf S ψ h).val = i ∧ S.cl (h * S.z * h⁻¹) = v

section Classes

variable
  [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T46)

include I in
theorem cl_eq_xcl (hw : S.width = 10) {h : G} (hbQ : h * S.z * h⁻¹ ∈ S.QG)
    (hbne : h * S.z * h⁻¹ ≠ S.z) : S.cl (h * S.z * h⁻¹) = xcl S ψ (planeOf S ψ h) := by
  have hex : ∃ v : S.Qt, ∃ h' : G, h' * S.z * h'⁻¹ ∈ S.QG ∧ h' * S.z * h'⁻¹ ≠ S.z ∧
      (planeOf S ψ h').val = (planeOf S ψ h).val ∧ S.cl (h' * S.z * h'⁻¹) = v :=
    ⟨_, h, hbQ, hbne, rfl, rfl⟩
  obtain ⟨h', hQ', hne', hpl, hv⟩ := Classical.epsilon_spec hex
  rw [xcl, ← hv]
  exact cl_eq_of_planeOf_eq ψ I hw hQ' hne' hbQ hbne (Fin.ext hpl).symm

include I in
theorem ρ_xcl (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M) (i : Fin 891) :
    (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) (xcl S ψ i) = xcl S ψ (planeHom S ψ (rhoM S m) i) := by
  obtain ⟨h, hbQ, hbne, rfl⟩ := exists_planeOf_eq ψ hw haQ hne i
  obtain ⟨hQ', hne'⟩ := mul_conj_mem m hbQ hbne
  rw [← cl_eq_xcl I ψ hw hbQ hbne, ← planeOf_mul ψ hw hbQ hbne m,
    ← cl_eq_xcl I ψ hw hQ' hne']
  exact S.ρ_cl_conj_z m.2 hbQ

end Classes

end CFSG.LargeExtraspecial.S14.SMK
