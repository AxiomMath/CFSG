module

public import CFSG.GF2Type.SmithTypeE.E8.Delta28
public import CFSG.GF2Type.SmithTypeE.E7.TrLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (z_not_mem_Dl)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_isConj_mem_Dl_of_socle
    (hrank : ∀ E : Subgroup S.O, E ≤ S.Mbar → CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 27)
    (hw : S.width = 28) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (φ : S.Qt ≃ₗ[ZMod 2] V) (Wt : Set V)
    (hWt0 : ∀ w ∈ Wt, w ≠ 0)
    (hWt : ∀ w ∈ Wt, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = w)
    (R : Set S.O)
    (hRc : ∀ r ∈ R, r ∈ S.Mbar ∧
      r * S.ρ ⟨g * S.z * g⁻¹, hxM⟩ = S.ρ ⟨g * S.z * g⁻¹, hxM⟩ * r)
    (hM1 : ∀ N : Submodule (ZMod 2) V, N ≠ ⊥ →
      N ≤ (S.commQt (g * S.z * g⁻¹)).map (φ : S.Qt →ₗ[ZMod 2] V) →
      (∀ r ∈ R, ∀ n ∈ N, φ (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm n)) ∈ N) →
        ∃ w ∈ Wt, w ∈ N) :
    ∃ v, IsConj S.z v ∧ v ∈ S.QG ⊓ S.Qa g := by
  have hD := QG_inf_Qa_ne_bot hrank hw hxM hxQ (E7.not_exists_conj_mul_z S hxz)
  have hW0 : S.clSub (S.QG ⊓ S.Qa g) ≠ ⊥ := by
    intro h
    apply hD
    rw [eq_bot_iff]
    intro d hd
    have hcl : S.cl d ∈ S.clSub (S.QG ⊓ S.Qa g) := S.cl_mem_clSub hd hd.1
    rw [h, Submodule.mem_bot, S.cl_eq_zero_iff hd.1] at hcl
    rcases hcl with h1 | h1
    · exact (mem_bot).mpr h1
    · exact absurd (h1 ▸ hd) (z_not_mem_Dl S hxQ)
  have hNne : (S.clSub (S.QG ⊓ S.Qa g)).map (φ : S.Qt →ₗ[ZMod 2] V) ≠ ⊥ := by
    intro h
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have h1 : (φ : S.Qt →ₗ[ZMod 2] V) w ∈ (S.clSub (S.QG ⊓ S.Qa g)).map (φ : S.Qt →ₗ[ZMod 2] V) :=
      Submodule.mem_map_of_mem hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact φ.injective (h1.trans φ.map_zero.symm)
  have hNle : (S.clSub (S.QG ⊓ S.Qa g)).map (φ : S.Qt →ₗ[ZMod 2] V) ≤
      (S.commQt (g * S.z * g⁻¹)).map (φ : S.Qt →ₗ[ZMod 2] V) :=
    Submodule.map_mono (E7.clSub_Dl_le_commQt S hxM hxQ hxz)
  have hNinv : ∀ r ∈ R, ∀ n ∈ (S.clSub (S.QG ⊓ S.Qa g)).map (φ : S.Qt →ₗ[ZMod 2] V),
      φ (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm n)) ∈
        (S.clSub (S.QG ⊓ S.Qa g)).map (φ : S.Qt →ₗ[ZMod 2] V) := by
    intro r hr n hn
    obtain ⟨hrM, hrc⟩ := hRc r hr
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hrM
    obtain ⟨m', hm'x, hm'⟩ := E7.exists_commute_rho_eq_of_not_isConj S hxM hxz m hrc
    obtain ⟨w, hw', rfl⟩ := hn
    obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hw'
    refine ⟨S.cl ((m' : G) * d * (m' : G)⁻¹), ?_, ?_⟩
    · exact S.cl_mem_clSub (E7.conj_mem_Dl S m'.2 hm'x hd) (E7.conj_mem_Dl S m'.2 hm'x hd).1
    · show φ (S.cl ((m' : G) * d * (m' : G)⁻¹)) = _
      rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ← hm', S.ρ_cl m' hdQ]
  obtain ⟨w, hwW, hwN⟩ := hM1 _ hNne hNle hNinv
  obtain ⟨w₀, hw₀, rfl⟩ := hwN
  obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hw₀
  obtain ⟨c, hc, hcQ, hcw⟩ := hWt _ hwW
  have hcl : S.cl c = S.cl d := φ.injective hcw
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hWt0 _ hwW
    rw [S.cl_one, map_zero]
  exact ⟨d, SME.isConj_of_cl_eq S hc hcQ hdQ hd1 hcl, hd⟩

end CFSG.GF2Type.SmithTypeE.E8
