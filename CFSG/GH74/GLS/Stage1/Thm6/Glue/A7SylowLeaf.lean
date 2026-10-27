module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Top

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

omit [Finite G] in
theorem four_normalized_of_abs {C T P Q Rd : Subgroup G} {ρ : G → S₇} {Tp : Subgroup S₇} {f : S₇}
    (h : Abs C T P Q Rd ρ Tp f) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V := by
  have hidx : (V.subgroupOf P).index = 2 := by
    have h1 := (V.subgroupOf P).index_mul_card
    rw [A7.card_subgroupOf hVP, hV.2] at h1
    have h2 : Nat.card ↥P = 8 := h.card_P
    omega
  have hN : (V.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx
  have hPV : ∀ g ∈ P, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have := hN.conj_mem ⟨v, hVP hv⟩ (by exact hv) ⟨g, hg⟩
    exact this
  intro t ht v hv
  have hvP : v ∈ P := hVP hv
  have htC : t ∈ C := h.T_le_C ht
  have hvC : v ∈ C := h.P_le_C hvP
  obtain ⟨p, hp, hcase⟩ := h.sp.mem_cases (h.rho_T t ht)
  obtain ⟨g, hgP, hgp⟩ := (h.rho_P p).1 hp
  have hgC : g ∈ C := h.P_le_C hgP
  have hρv : ρ v ∈ Tp ⊓ A₇ := h.rho_mem_Pbar hvP
  have hcomm : ρ v * f = f * ρ v := h.sp.comm _ hρv
  have key : ρ (t * v * t⁻¹) = ρ (g * v * g⁻¹) := by
    have e1 : ρ (t * v * t⁻¹) = ρ t * ρ v * (ρ t)⁻¹ := by
      rw [h.rho_mul (t * v) (mul_mem htC hvC) t⁻¹ (inv_mem htC), h.rho_mul t htC v hvC,
        h.rho_inv t htC]
    have e2 : ρ (g * v * g⁻¹) = ρ g * ρ v * (ρ g)⁻¹ := by
      rw [h.rho_mul (g * v) (mul_mem hgC hvC) g⁻¹ (inv_mem hgC), h.rho_mul g hgC v hvC,
        h.rho_inv g hgC]
    rw [e1, e2, hgp]
    rcases hcase with hc | hc
    · rw [hc]
    · rw [hc]
      have : f * ρ v = ρ v * f := hcomm.symm
      calc p * f * ρ v * (p * f)⁻¹ = p * (f * ρ v) * f⁻¹ * p⁻¹ := by group
        _ = p * (ρ v * f) * f⁻¹ * p⁻¹ := by rw [this]
        _ = p * ρ v * p⁻¹ := by group
  have hP1 : t * v * t⁻¹ ∈ P := h.P_normal t ht v hvP
  have hP2 : g * v * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hgP hvP) (P.inv_mem hgP)
  have := h.P_inj _ hP1 _ hP2 key
  rw [this]
  exact hPV g hgP v hv

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

variable {G : Type} [Group G] [Finite G]

theorem iv3SylowLeafA7_of (hIVK : IVKA7Facts) {x : G} (Kb : Subgroup (CentralizerBar x)) :
    IV3SylowLeafA7 x Kb := by
  intro c hm _ S hS hTsyl hrel V hVP hV hnn _
  exfalso
  obtain ⟨eK⟩ := hm
  obtain ⟨Tp, f, h⟩ := exists_abs hIVK eK hTsyl
  exact hnn (four_normalized_of_abs h hVP hV)

end CFSG.GH74.GLS.Stage1.Thm6.Glue
