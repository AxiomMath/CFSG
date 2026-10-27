module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem exists_basis_l1_of_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    ∃ (V₂ : Subgroup G) (z a b x y : G), A6.IsV2 T V V₂ ∧
      z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧ b ∈ V ∧ b ∉ V₂ ∧
      x ∈ L₁Of L (fsuV1 T V) ∧ y ∈ L₁Of L (fsuV1 T V) ∧ x * a * x⁻¹ = b ∧
      x * b * x⁻¹ = a * b ∧ y * a * y⁻¹ = z * a := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2_F4 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  have hUe := isElemAbelian_fsuU_of_F4 h hMod
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe (le_conjClosure V _ ha) (le_conjClosure V _ hb)
  have hV2' : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (le_conjClosure V _ ha)
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x₁, hx₁L, hx₁3, hx₁z, hx₁a, hx₁b⟩ := S14.exists_rot_F4 hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  obtain ⟨x₂, hx₂L, hx₂3, hx₂z, hx₂a, hx₂b⟩ := S14.exists_rot_F4 hzV haV' (mul_mem hzV hb)
    (fun h => haV (h ▸ one_mem _))
    (fun h => hbV (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem hzV₂))
    (fun h => haV (h ▸ hz0))
    (fun h => hbV (by
      have : b = 1 := by
        calc b = z⁻¹ * (z * b) := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      rw [this]
      exact one_mem _))
    (fun h => hbV (by
      have : b = z⁻¹ * a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * a := by rw [← h]
      rw [this]
      exact mul_mem (inv_mem hzV₂) ha))
    (fun h => hbV (by
      have : b = a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * (z * a) := by rw [h]
          _ = a := by group
      rw [this]
      exact ha))
  have hx₁L1 : x₁ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₁L, S14.mem_g1_F4 hz0 hz1 hx₁z⟩, 3, by decide, hx₁3⟩
  have hx₂L1 : x₂ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₂L, S14.mem_g1_F4 hz0 hz1 hx₂z⟩, 3, by decide, hx₂3⟩
  have hx₁z' : x₁⁻¹ * z * x₁ = z := by
    calc x₁⁻¹ * z * x₁ = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by rw [hx₁z]
      _ = z := by group
  have hx₁b' : x₁⁻¹ * b * x₁ = a := by
    calc x₁⁻¹ * b * x₁ = x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ := by rw [hx₁a]
      _ = a := by group
  have hya : (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = z * a := by
    calc (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = x₁⁻¹ * (x₂ * a * x₂⁻¹) * x₁ := by group
      _ = x₁⁻¹ * (z * b) * x₁ := by rw [hx₂a]
      _ = (x₁⁻¹ * z * x₁) * (x₁⁻¹ * b * x₁) := by group
      _ = z * a := by rw [hx₁z', hx₁b']
  exact ⟨V₂, z, a, b, x₁, x₁⁻¹ * x₂, hV2, hz0, hz1, ha, haV, hb, hbV, hx₁L1,
    mul_mem (inv_mem hx₁L1) hx₂L1, hx₁a, hx₁b, hya⟩

end CFSG.Quasithin.H13.L32A
