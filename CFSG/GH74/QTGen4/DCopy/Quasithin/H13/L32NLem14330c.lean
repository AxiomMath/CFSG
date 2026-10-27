module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14328d
public import CFSG.Quasithin.H13.L32NLem14330a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l)
include C

theorem exists_m_F4 : ∃ m ∈ L, m * z * m⁻¹ = z ∧ m * (g⁻¹ * z * g) * m⁻¹ = z * b := by
  have haV₂ := C.a_mem_F4
  have haV₁ := C.a_nmem_F4
  have haV := C.a_V_F4
  generalize g⁻¹ * z * g = a at haV₂ haV₁ haV ⊢
  have hzb : z * b ∈ V := V.mul_mem C.z_V_F4 C.b_mem
  have hzz := C.mul_self_V_F4 C.z_V_F4
  have hbz : b = z * (z * b) := by rw [← mul_assoc, hzz, one_mul]
  obtain ⟨m, hmL, -, hmz, hma, -⟩ := C.S.exists_rot_F4 C.z_V_F4 haV hzb (fun h => haV₁ (h ▸ one_mem _))
    (fun h => C.b_nmem (by rw [hbz, h, mul_one]; exact C.z_V₂_F4)) (fun h => haV₁ (h ▸ C.z_mem))
    (fun h => C.b_nmem (by rw [hbz, h, hzz]; exact one_mem _))
    (fun h => C.b_nmem (by rw [hbz, ← h]; exact V₂.mul_mem C.z_V₂_F4 haV₂))
    (fun h => C.b_nmem (by
      rw [hbz, h, ← mul_assoc, hzz, one_mul]
      exact haV₂))
  exact ⟨m, hmL, hmz, hma⟩

theorem mem_normalizer_V1_F4 {m : G} (hmz : m * z * m⁻¹ = z) :
    m ∈ Subgroup.normalizer (fsuV1 T V : Set G) := by
  refine mem_normalizer_of_maps fun w hw => ?_
  rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne hw with rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · rw [hmz]
    exact C.z_mem

theorem exists_second_F4 (h1222 : Stmt12_2_2_F4) : ∃ (T' V₂' : Subgroup G) (k : G),
    Setting1282One G T' L V 3 (fsuV1 T V) V₂' ∧
    (∀ v, v ∈ V₂' ↔ v = 1 ∨ v = z ∨ v = z * b ∨ v = b) ∧
    k⁻¹ ∈ p128 T' L V ∧ k⁻¹ ∉ Subgroup.normalizer (fsuV1 T V : Set G) ∧ k * z * k⁻¹ = z * b ∧
    k ∈ Subgroup.normalizer (V : Set G) := by
  obtain ⟨m, hmL, hmz, hma⟩ := C.exists_m_F4
  have hmN := C.mem_normalizer_V1_F4 hmz
  have hmV := C.L_le_F4 hmL
  have hV1' : CFSG.conjugate (fsuV1 T V) m⁻¹ = fsuV1 T V :=
    conjugate_eq_self ((Subgroup.normalizer _).inv_mem hmN)
  have hs' := setting1282One_conj C.setting C.S.TV_F4 hmL
  rw [hV1'] at hs'
  have hzz := C.mul_self_V_F4 C.z_V_F4
  have hza : m * (z * (g⁻¹ * z * g)) * m⁻¹ = b := by
    rw [show m * (z * (g⁻¹ * z * g)) * m⁻¹ = (m * z * m⁻¹) * (m * (g⁻¹ * z * g) * m⁻¹) by group,
      hmz, hma, ← mul_assoc, hzz, one_mul]
  have hmem : ∀ v, v ∈ CFSG.conjugate V₂ m⁻¹ ↔ v = 1 ∨ v = z ∨ v = z * b ∨ v = b := by
    intro v
    rw [conjugate_inv_mem_iff]
    have e : v = m * (m⁻¹ * v * m) * m⁻¹ := by group
    constructor
    · intro hv
      by_cases hv1 : m⁻¹ * v * m = 1
      · left
        rw [e, hv1]
        group
      · right
        rcases C.V2_cases_F4 hv hv1 with h | h | h <;> rw [e, h]
        · exact Or.inl hmz
        · exact Or.inr (Or.inl hma)
        · exact Or.inr (Or.inr hza)
    · rintro (h | h | h | h) <;> rw [h]
      · rw [mul_one, inv_mul_cancel]
        exact one_mem _
      · rw [show m⁻¹ * z * m = z by
          calc m⁻¹ * z * m = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmz]
            _ = z := by group]
        exact C.z_V₂_F4
      · rw [show m⁻¹ * (z * b) * m = g⁻¹ * z * g by
          calc m⁻¹ * (z * b) * m = m⁻¹ * (m * (g⁻¹ * z * g) * m⁻¹) * m := by rw [hma]
            _ = g⁻¹ * z * g := by group]
        exact C.a_mem_F4
      · rw [show m⁻¹ * b * m = z * (g⁻¹ * z * g) by
          calc m⁻¹ * b * m = m⁻¹ * (m * (z * (g⁻¹ * z * g)) * m⁻¹) * m := by rw [hza]
            _ = z * (g⁻¹ * z * g) := by group]
        exact V₂.mul_mem C.z_V₂_F4 C.a_mem_F4
  have hzb₂ : z * b ∈ CFSG.conjugate V₂ m⁻¹ := (hmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hzb₁ : z * b ∉ fsuV1 T V := fun h => C.b_nmem (by
    rw [show b = z * (z * b) by rw [← mul_assoc, hzz, one_mul]]
    exact V₂.mul_mem C.z_V₂_F4 (C.plane.2 h))
  obtain ⟨k, hk, hkz, -, -⟩ := L128P.exists_rotation_mem_F4 h1222 hs'.hyp hs'.v1 hs'.v2 hs'.le
    C.z_mem C.z_ne hzb₂ hzb₁
  have hkP := oTwoUpper_le _ hk
  have hT'V : CFSG.conjugate T m⁻¹ ≤ Subgroup.normalizer (V : Set G) :=
    conjugate_le_normalizer hmV C.S.TV_F4
  have hkV : k ∈ Subgroup.normalizer (V : Set G) :=
    L128P.p128_le_normalizer (i := 3) (by norm_num) ⟨le_rfl, C.S.card_V_F4, hT'V⟩ hkP
  refine ⟨CFSG.conjugate T m⁻¹, CFSG.conjugate V₂ m⁻¹, k, hs', hmem,
    (p128 _ L V).inv_mem hkP, fun hkN => hzb₁ ?_, hkz, hkV⟩
  have hkN' := (Subgroup.normalizer _).inv_mem hkN
  rw [inv_inv] at hkN'
  rw [← hkz]
  exact (Subgroup.mem_normalizer_iff.mp hkN' z).mp C.z_mem

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
