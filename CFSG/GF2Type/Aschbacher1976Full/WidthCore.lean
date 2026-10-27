module

public import CFSG.GF2Type.Aschbacher1976Full.WidthStruct
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GF2Type.CenterFour.Setting
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCore_eq_gf {z : G} (hF2 : IsPGroup 2 (Fz z)) :
    pCore 2 ↥(Hz z) = generalizedFitting ↥(Hz z) := by
  apply le_antisymm
  · refine le_trans (pCore_le_fitting _ 2) ?_
    rw [generalizedFitting.eq_sup]
    exact le_sup_left
  · have hN := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).2
    refine le_sSup ⟨hN, ?_⟩
    exact IsPGroup.of_equiv hF2
      (Subgroup.equivMapOfInjective (generalizedFitting ↥(Hz z)) (Hz z).subtype
        (Hz z).subtype_injective).symm

theorem coreAt_eq_Fz {z : G} (hF2 : IsPGroup 2 (Fz z)) : coreAt z = Fz z := by
  show (pCore 2 ↥(Hz z)).map (Hz z).subtype = (generalizedFitting ↥(Hz z)).map (Hz z).subtype
  rw [pCore_eq_gf hF2]

theorem Fz_conj_mem {z g x : G} (hg : g ∈ Hz z) (hx : x ∈ Fz z) : g * x * g⁻¹ ∈ Fz z := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hN := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(Hz z))).2
  refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : Hz z) * y * (⟨g, hg⟩ : Hz z)⁻¹, ?_, ?_⟩
  · exact hN.conj_mem y hy _
  · simp

theorem selfCent_F {z : G} (hF2 : IsPGroup 2 (Fz z)) :
    ∀ h ∈ centralizer ({z} : Set G), (∀ q ∈ coreAt z, h * q = q * h) → h ∈ coreAt z := by
  intro h hh hcomm
  have key : pCore 2 ↥(Hz z) = generalizedFitting ↥(Hz z) := pCore_eq_gf hF2
  have hmem : (⟨h, hh⟩ : Hz z) ∈
      Subgroup.centralizer ((pCore 2 ↥(Hz z) : Subgroup ↥(Hz z)) : Set ↥(Hz z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have hxc : (x : G) ∈ coreAt z :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    simp only [Subgroup.coe_mul]
    exact (hcomm _ hxc).symm
  rw [key] at hmem
  have hP := CFSG.centralizer_generalizedFitting_le ↥(Hz z) hmem
  rw [← key] at hP
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩, hP, rfl⟩

section Centre

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem mem_centerAt_iff (hD : Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) {x : G} : x ∈ centerAt z ↔ x ∈ Z := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    apply mem_Z_of_comm hD hz
    · rw [← coreAt_eq_Fz hF2]
      exact y.2
    · intro b hb
      have hbF : b ∈ Fz z := by
        rw [← hD.sup_eq]
        exact Subgroup.mem_sup_right hb
      have hbc : b ∈ coreAt z := by
        rw [coreAt_eq_Fz hF2]
        exact hbF
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨b, hbc⟩)
      simp only [Subgroup.coe_mul] at h2
      exact h2.symm
  · intro hx
    have hxF : x ∈ coreAt z := by
      rw [coreAt_eq_Fz hF2, ← hD.sup_eq]
      exact Subgroup.mem_sup_left hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgF : (g : G) ∈ Fz z := by
      rw [← coreAt_eq_Fz hF2]
      exact g.2
    simp only [Subgroup.coe_mul]
    exact (Z_comm_F hD hx hgF).symm

theorem Z_conj_mem (hD : Z4Data z w Z A) (hz : orderOf z = 2) {g h : G} (hg : g ∈ Hz z)
    (hh : h ∈ Z) : g * h * g⁻¹ ∈ Z := by
  have hhF : h ∈ Fz z := by
    rw [← hD.sup_eq]
    exact Subgroup.mem_sup_left hh
  have hF : g * h * g⁻¹ ∈ Fz z := Fz_conj_mem hg hhF
  apply mem_Z_of_comm hD hz hF
  intro b hb
  have hbF : b ∈ Fz z := by
    rw [← hD.sup_eq]
    exact Subgroup.mem_sup_right hb
  have hb' : g⁻¹ * b * g ∈ Fz z := by
    have := Fz_conj_mem ((Hz z).inv_mem hg) hbF
    rwa [inv_inv] at this
  have hcomm := Z_comm_F hD hh hb'
  calc g * h * g⁻¹ * b = g * (h * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * h) * g⁻¹ := by rw [hcomm]
    _ = b * (g * h * g⁻¹) := by group

theorem normalizer_centerAt (hD : Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) :
    normalizer (centerAt z : Set G) = centralizer ({z} : Set G) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hzZ : z ∈ centerAt z := (mem_centerAt_iff hD hz hF2).mpr hD.mem_z
    have hgz : g * z * g⁻¹ ∈ Z := (mem_centerAt_iff hD hz hF2).mp ((h z).mp hzZ)
    have hsq : (g * z * g⁻¹) ^ 2 = 1 := by
      rw [conj_pow, z_sq hz, mul_one, mul_inv_cancel]
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    have hconj : g * z * g⁻¹ = z := involution_eq hD hz hgz hsq hne
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · intro hg h
    have hgH : g ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr hg
    constructor
    · intro hk
      exact (mem_centerAt_iff hD hz hF2).mpr
        (Z_conj_mem hD hz hgH ((mem_centerAt_iff hD hz hF2).mp hk))
    · intro hk
      have hg' : g⁻¹ ∈ Hz z := (Hz z).inv_mem hgH
      have h1 := Z_conj_mem hD hz hg' ((mem_centerAt_iff hD hz hF2).mp hk)
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact (mem_centerAt_iff hD hz hF2).mpr h1

end Centre

end CFSG.GF2Type.Aschbacher1976Full.Width
