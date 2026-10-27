module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionD

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

section Mbar

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

@[expose] noncomputable def Mbar [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁)) : Subgroup G :=
  (Subgroup.comap (rhoGL b) U0).map (Subgroup.normalizer (M₁ : Set G)).subtype

theorem mem_Mbar [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁)) (x : G) :
    x ∈ Mbar b ↔ ∃ n : Subgroup.normalizer (M₁ : Set G), (n : G) = x ∧ rhoGL b n ∈ U0 := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨n, rfl, hn⟩
  · rintro ⟨n, rfl, hn⟩
    exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩

theorem Mbar_inf_norm [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (x : G) (hx : x ∈ Mbar b) (hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G)) :
    x ∈ M₁ := by
  obtain ⟨n, rfl, hn⟩ := (mem_Mbar b x).mp hx
  obtain ⟨a, c, hac⟩ := hn
  have hM : rhoMat b n = uMat a c := hac
  have e10 : rhoMat b n 1 0 = a := by rw [hM]; simp [uMat]
  have e20 : rhoMat b n 2 0 = c := by rw [hM]; simp [uMat]
  obtain ⟨h10, h20⟩ := col0_of_normalizes hv b hb0 n hxN
  rw [e10] at h10
  rw [e20] at h20
  have hone' : rhoGL b n = 1 := by
    apply Units.ext
    rw [Units.val_one, rhoGL_val, hM, h10, h20]
    exact uMat_zero
  exact mem_of_rho_eq_one hone hlet hv hst b n hone'

theorem Mbar_conj_mem [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hstab : ∀ g ∈ (rhoGL b).range, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0)
    (g : G) (hg : g ∈ Subgroup.normalizer (M₁ : Set G)) (x : G) (hx : x ∈ Mbar b) :
    g * x * g⁻¹ ∈ Mbar b := by
  obtain ⟨n, rfl, hn⟩ := (mem_Mbar b x).mp hx
  rw [mem_Mbar]
  let gN : Subgroup.normalizer (M₁ : Set G) := ⟨g, hg⟩
  have hg1 := hstab (rhoGL b gN) ⟨gN, rfl⟩
  have hg2 := hstab ((rhoGL b gN)⁻¹) ⟨gN⁻¹, by rw [map_inv]⟩
  have hconj := U0_conj_mem hn hg1.1 hg1.2 hg2.1 hg2.2
  refine ⟨gN * n * gN⁻¹, rfl, ?_⟩
  simp only [map_mul, map_inv]
  exact hconj

theorem card_ker_rhoGL [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hM1 : Nat.card M₁ = 27) : Nat.card (rhoGL b).ker = 27 := by
  have hle : M₁ ≤ Subgroup.normalizer (M₁ : Set G) := Subgroup.le_normalizer
  have hker : (rhoGL b).ker = M₁.subgroupOf (Subgroup.normalizer (M₁ : Set G)) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact mem_of_rho_eq_one hone hlet hv hst b n h
    · intro h
      rw [rhoGL_eq_one_iff b]
      intro x hx
      show (n : G) * x * (n : G)⁻¹ = x
      rw [comm_of_mem_M₁ h hx, mul_inv_cancel_right]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hM1]

theorem card_Mbar [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hM1 : Nat.card M₁ = 27) (hU0Y : U0 ≤ (rhoGL b).range) :
    Nat.card ↥(Mbar b) = 243 := by
  have hmap : Nat.card ↥(Mbar b) =
      Nat.card ↥(Subgroup.comap (rhoGL b) U0) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hC1 := Subgroup.card_mul_index (Subgroup.comap (rhoGL b) U0)
  rw [Subgroup.index_comap] at hC1
  have hN1 := Subgroup.card_mul_index (rhoGL b).ker
  rw [Subgroup.index_ker, card_ker_rhoGL hone hlet hv hst b hM1] at hN1
  have hR := Subgroup.relIndex_mul_card (H := U0) (K := (rhoGL b).range)
  rw [inf_eq_left.mpr hU0Y, card_U0] at hR
  have hpos : 0 < Nat.card ↥(rhoGL b).range := Nat.card_pos
  have hr0 : 0 < U0.relIndex (rhoGL b).range := by
    rcases Nat.eq_zero_or_pos (U0.relIndex (rhoGL b).range) with h | h
    · rw [h, zero_mul] at hR
      omega
    · exact h
  rw [hmap]
  apply Nat.eq_of_mul_eq_mul_right hr0
  rw [hC1, ← hN1, ← hR]
  ring

end Mbar

end CFSG.GH74.QTGen4.Recog.G23.P7
