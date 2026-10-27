module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Left

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_commuting_left (z : G) {w₁ w₂ : G}
    (h₁ : w₁ ∈ Subgroup.centralizer ({z} : Set G)) (h₂ : w₂ ∈ Subgroup.centralizer ({z} : Set G))
    (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1)
    (hcomm : oddQuotMk z ⟨w₁, h₁⟩ * oddQuotMk z ⟨w₂, h₂⟩ =
      oddQuotMk z ⟨w₂, h₂⟩ * oddQuotMk z ⟨w₁, h₁⟩) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      w₁ * (o * w₂ * o⁻¹) = (o * w₂ * o⁻¹) * w₁ := by
  obtain ⟨o₁, ho₁, o₂, ho₂, hc⟩ := exists_conj_commuting z h₁ h₂ hs₁ hs₂ hcomm
  refine ⟨o₁⁻¹ * o₂, mul_mem (inv_mem ho₁) ho₂, ?_⟩
  have e1 : w₁ * (o₁⁻¹ * o₂ * w₂ * (o₁⁻¹ * o₂)⁻¹) =
      o₁⁻¹ * ((o₁ * w₁ * o₁⁻¹) * (o₂ * w₂ * o₂⁻¹)) * o₁ := by group
  have e2 : (o₁⁻¹ * o₂ * w₂ * (o₁⁻¹ * o₂)⁻¹) * w₁ =
      o₁⁻¹ * ((o₂ * w₂ * o₂⁻¹) * (o₁ * w₁ * o₁⁻¹)) * o₁ := by group
  rw [e1, e2, hc]

end Left

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainCtx.exists_lift_of_member (C : ChainCtx p f Ω z) {M : Subgroup G} {w : G}
    (hM : M ∈ tqMembers Ω z) (hw : IsClassicalMember p f M w)
    {R₁ : Subgroup (compModel C.D C.i₁).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D)
    (hmod : R₁.map (C.psi C.i₁) = modOdd z (exactCore z M)) :
    ∃ L : ChainLift C, L.J = M ∧ L.t = w := by
  obtain ⟨R₁₀, hR₁₀, R₂₀, hR₂₀, τ₁₀, τ₂₀, ν₁₀, ν₂₀, hd₀⟩ := C.pair
  obtain ⟨k, hk⟩ := C.single C.i₁ C.tag₁ R₁₀ hR₁₀ R₁ hR₁
  have he : ∀ R : Subgroup (compModel C.D C.i₁).K,
      R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D ↔
        R.map (MulAut.conj k).toMonoidHom ∈
          fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D := fun R =>
    ⟨fun h => conjSub_mem_fundamentalSubgroups h k, fun h => by
      have h1 := conjSub_mem_fundamentalSubgroups h k⁻¹
      have h2 : conjSub k⁻¹ (R.map (MulAut.conj k).toMonoidHom) = R := conjSub_inv_conjSub k R
      rwa [h2] at h1⟩
  have hd := hd₀.map (MulAut.conj k) he
  have hk' : R₁ = R₁₀.map (MulAut.conj k).toMonoidHom := hk
  rw [← hk'] at hd
  have hR₂ : R₂₀.map (MulAut.conj k).toMonoidHom ∈
      fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D := (he R₂₀).mp hR₂₀
  obtain ⟨N₂, hN₂, hN₂img⟩ := C.exists_member_of_fund C.i₁ C.tag₁ hR₂
  obtain ⟨w₂, hw₂⟩ := C.hΩ.classical N₂ hN₂.1
  have hwC := C.involution_mem_centralizer hM hw
  have hw₂C := C.involution_mem_centralizer hN₂ hw₂
  have hwbar : oddQuotMk z ⟨w, hwC⟩ = C.psi C.i₁ ((MulAut.conj k) τ₁₀) :=
    C.oddQuotMk_involution hM hw C.i₁ C.tag₁ hR₁ hd.center₁ hmod.symm
  have hw₂bar : oddQuotMk z ⟨w₂, hw₂C⟩ = C.psi C.i₁ ((MulAut.conj k) τ₂₀) :=
    C.oddQuotMk_involution hN₂ hw₂ C.i₁ C.tag₁ hR₂ hd.center₂ hN₂img
  have hcomm : oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨w₂, hw₂C⟩ =
      oddQuotMk z ⟨w₂, hw₂C⟩ * oddQuotMk z ⟨w, hwC⟩ := by
    rw [hwbar, hw₂bar, ← map_mul (C.psi C.i₁), ← map_mul (C.psi C.i₁), hd.comm]
  obtain ⟨o, ho, hc⟩ := exists_conj_commuting_left z hwC hw₂C
    (isCentralInvolution_of_isClassicalMember hw).sq
    (isCentralInvolution_of_isClassicalMember hw₂).sq hcomm
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho
  have hz'C : o * w₂ * o⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hoC hw₂C) (inv_mem hoC)
  have hbar : oddQuotMk z ⟨o * w₂ * o⁻¹, hz'C⟩ = oddQuotMk z ⟨w₂, hw₂C⟩ := by
    have h1 : oddQuotMk z ⟨o, hoC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn ho hoC
    have : (⟨o * w₂ * o⁻¹, hz'C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨o, hoC⟩ * ⟨w₂, hw₂C⟩ * ⟨o, hoC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, h1]
    simp
  have himg : modOdd z (exactCore z (conjSub o N₂)) = modOdd z (exactCore z N₂) := by
    have : exactCore z (conjSub o N₂) = conjSub o (exactCore z N₂) :=
      triangleResidual_conjSub N₂ hoC
    rw [this]
    exact modOdd_conjSub_of_mem_oddCoreIn ho
  exact ⟨{
    R₁ := R₁
    R₂ := R₂₀.map (MulAut.conj k).toMonoidHom
    τ₁ := (MulAut.conj k) τ₁₀
    τ₂ := (MulAut.conj k) τ₂₀
    ν₁ := (MulAut.conj k) ν₁₀
    ν₂ := (MulAut.conj k) ν₂₀
    hR₁ := hR₁
    hR₂ := hR₂
    hd := hd
    J := M
    K' := conjSub o N₂
    t := w
    z' := o * w₂ * o⁻¹
    ht := hwC
    hz' := hz'C
    hJ := hM
    hK' := conjSub_mem_tqMembers C.hΩ.conjInvariant hoC hN₂
    hJt := hw
    hK'z' := hw₂.conj o
    hJimg := hmod.symm
    hK'img := himg.trans hN₂img
    htbar := hwbar
    hz'bar := hbar.trans hw₂bar
    htz' := hc }, rfl, rfl⟩

end Lift

end CFSG.ClassicalInvolution.Asc77
