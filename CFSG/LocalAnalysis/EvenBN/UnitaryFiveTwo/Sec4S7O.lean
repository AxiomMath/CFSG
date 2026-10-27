module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7L
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7M

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem Data.u_comm_z (d : Data G) : d.u * d.z = d.z * d.u := by
  show d.ι uSU * d.ι zSU = d.ι zSU * d.ι uSU
  rw [← map_mul, ← map_mul, show uSU * zSU = zSU * uSU from genSU_comm_zSU 0 (by decide)]

theorem Data.u_comm_ZX₄ {z : G} (hz : z ∈ d.ZX₄) : d.u * z = z * d.u := by
  rcases Data.Hyp.eq_one_or_eq_z hz with rfl | rfl
  · simp
  · exact Data.u_comm_z d

theorem Data.u_comm_e₁e₂ (d : Data G) : d.u * (d.e₁ * d.e₂) = (d.e₁ * d.e₂) * d.u := by
  show d.ι uSU * (d.ι e₁SU * d.ι e₂SU) = (d.ι e₁SU * d.ι e₂SU) * d.ι uSU
  rw [← map_mul, ← map_mul, ← map_mul, uSU_comm_e₁e₂]

section Final



variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h in
theorem Data.Hyp.u_mem_XW : d.u ∈ d.XW := by
  rw [h.sec4_11_1.1]
  refine mem_sup_left (Subgroup.mem_inf.2 ⟨?_, h.L_le_H (Data.u_mem_L d)⟩)
  exact Data.Hyp.ι_mem_normalizer_pull (mem_normalizer_fintype fun a ha => uSU_conj_mem_A₁sub ha)

include h in
theorem Data.Hyp.u_conj_mem_D₁ {y : G} (hy : y ∈ d.D₁) : d.u * y * d.u⁻¹ ∈ d.D₁ :=
  h.conj_mem_D₁ h.u_mem_XW hy

include h hKU in
theorem Data.Hyp.u_conj_ZQ {ζ : G} (hζ : ζ ∈ Data.ZQ h hKU hf) : d.u * ζ * d.u⁻¹ = ζ := by
  have huu := Data.u_mul_u d
  have hutc : d.u * d.t = d.t * d.u := h.t_comm_of_mem_L (Data.u_mem_L d)
  obtain ⟨hζN, hζz⟩ := (h.mem_ZQ_iff hKU hf).1 hζ
  have hζW : ζ ∈ d.W := by
    rw [h.W_eq_ZQ_sup hKU hf]
    exact Subgroup.mem_sup_left hζ
  have hζK : ζ ∈ K₀ := by
    have hmem : ζ ∈ Data.Nn h hKU hf ⊓ d.Y := ⟨hζN, d.W_le_Y hζW⟩
    rw [h.Nn_inf_Y hKU hf] at hmem
    exact hmem.2
  have hK₃ : d.u ∈ d.K₃ :=
    d.ι_mem_pull_iff.2 ((le_sup_right.trans le_sup_left : zpowers uSU ≤ K₃sub) (mem_zpowers uSU))
  obtain ⟨u₀, hu₀⟩ := Data.exists_theta_eq h hKU hf hK₃
  rw [Data.theta_apply] at hu₀
  have htu₀ : d.t * (u₀ : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact u₀.2)
  have hc : ζ * (d.t * (u₀ : G) * d.t) = (d.t * (u₀ : G) * d.t) * ζ :=
    hf.comm_elem ζ hζK _ htu₀
  have hconj : d.u * ζ * d.u⁻¹ = (u₀ : G) * ζ * (u₀ : G)⁻¹ := by
    rw [← hu₀]
    calc (u₀ : G) * (d.t * (u₀ : G) * d.t) * ζ * ((u₀ : G) * (d.t * (u₀ : G) * d.t))⁻¹
        = (u₀ : G) * ((d.t * (u₀ : G) * d.t) * ζ) * (d.t * (u₀ : G) * d.t)⁻¹ * (u₀ : G)⁻¹ := by
          group
      _ = (u₀ : G) * (ζ * (d.t * (u₀ : G) * d.t)) * (d.t * (u₀ : G) * d.t)⁻¹ * (u₀ : G)⁻¹ := by
          rw [hc]
      _ = (u₀ : G) * ζ * (u₀ : G)⁻¹ := by group
  have hζ'K : d.u * ζ * d.u⁻¹ ∈ K₀ := by
    rw [hconj]
    exact K₀.mul_mem (K₀.mul_mem u₀.2 hζK) (K₀.inv_mem u₀.2)
  have hinj := Data.theta_injective h hf (a₁ := ⟨d.u * ζ * d.u⁻¹, hζ'K⟩) (a₂ := ⟨ζ, hζK⟩) (by
    rw [Data.theta_apply, Data.theta_apply]
    show d.u * ζ * d.u⁻¹ * (d.t * (d.u * ζ * d.u⁻¹) * d.t) = ζ * (d.t * ζ * d.t)
    have hui : d.u⁻¹ * d.t = d.t * d.u⁻¹ := (Commute.inv_left (show Commute d.u d.t from hutc)).eq
    have e1 : d.t * (d.u * ζ * d.u⁻¹) * d.t = d.u * (d.t * ζ * d.t) * d.u⁻¹ := by
      calc d.t * (d.u * ζ * d.u⁻¹) * d.t = (d.t * d.u) * ζ * (d.u⁻¹ * d.t) := by group
        _ = (d.u * d.t) * ζ * (d.t * d.u⁻¹) := by rw [← hutc, hui]
        _ = d.u * (d.t * ζ * d.t) * d.u⁻¹ := by group
    have hcz : d.u * (ζ * (d.t * ζ * d.t)) = (ζ * (d.t * ζ * d.t)) * d.u := Data.u_comm_ZX₄ hζz
    rw [e1]
    calc d.u * ζ * d.u⁻¹ * (d.u * (d.t * ζ * d.t) * d.u⁻¹)
        = d.u * (ζ * (d.t * ζ * d.t)) * d.u⁻¹ := by group
      _ = (ζ * (d.t * ζ * d.t)) * d.u * d.u⁻¹ := by rw [hcz]
      _ = ζ * (d.t * ζ * d.t) := by group)
  exact congrArg Subtype.val hinj

include h hKU in
theorem Data.Hyp.u_conj_mem_B₁_sup_W {x : G} (hx : x ∈ Data.B₁ h hKU hf ⊔ d.W) :
    d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf ⊔ d.W := by
  have huu := Data.u_mul_u d
  have hu' : d.u⁻¹ = d.u := inv_eq_of_mul_eq_one_right huu
  have hxD : x ∈ d.D₁ := (sup_le (h.B₁_le_D₁ hKU hf) h.W_le_D₁) hx
  have hxc := (h.mem_B₁_sup_W_iff hKU hf hxD).2 hx
  refine (h.mem_B₁_sup_W_iff hKU hf (h.u_conj_mem_D₁ hxD)).1 fun y hy => ?_
  have hy₁ : d.u⁻¹ * y * d.u ∈ d.D₁ := by
    have e : d.u⁻¹ * y * d.u = d.u * y * d.u⁻¹ := by rw [hu']
    rw [e]
    exact h.u_conj_mem_D₁ hy
  have h1 := hxc _ hy₁
  have h3 := h.u_conj_ZQ hKU hf h1
  have e2 : (d.u * x * d.u⁻¹) * y * (d.u * x * d.u⁻¹)⁻¹ * y⁻¹ =
      d.u * (x * (d.u⁻¹ * y * d.u) * x⁻¹ * (d.u⁻¹ * y * d.u)⁻¹) * d.u⁻¹ := by group
  rw [e2, h3]
  exact h1

include h hKU in
theorem Data.Hyp.hBu_of_eq
    (hB : Data.B₁ h hKU hf = ⁅Data.B₁ h hKU hf ⊔ d.W, zpowers (d.e₁ * d.e₂)⁆) :
    ∀ x ∈ Data.B₁ h hKU hf, d.u * x * d.u⁻¹ ∈ Data.B₁ h hKU hf := by
  have hgu := Data.u_comm_e₁e₂ d
  have hle : ∀ x ∈ ⁅Data.B₁ h hKU hf ⊔ d.W, zpowers (d.e₁ * d.e₂)⁆,
      d.u * x * d.u⁻¹ ∈ ⁅Data.B₁ h hKU hf ⊔ d.W, zpowers (d.e₁ * d.e₂)⁆ := by
    intro x hx
    have hmem : d.u * x * d.u⁻¹ ∈ (⁅Data.B₁ h hKU hf ⊔ d.W, zpowers (d.e₁ * d.e₂)⁆).map
        (MulAut.conj d.u).toMonoidHom := ⟨x, hx, rfl⟩
    rw [Subgroup.map_commutator] at hmem
    refine (Subgroup.commutator_mono ?_ ?_) hmem
    · rintro _ ⟨y, hy, rfl⟩
      exact h.u_conj_mem_B₁_sup_W hKU hf hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      show d.u * (d.e₁ * d.e₂) ^ k * d.u⁻¹ ∈ zpowers (d.e₁ * d.e₂)
      have : d.u * (d.e₁ * d.e₂) ^ k * d.u⁻¹ = (d.e₁ * d.e₂) ^ k := by
        rw [(Commute.zpow_right (show Commute d.u (d.e₁ * d.e₂) from hgu) k).eq, mul_assoc,
          mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem _ (mem_zpowers _) k
  intro x hx
  exact hB.ge (hle x (hB.le hx))

end Final

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
