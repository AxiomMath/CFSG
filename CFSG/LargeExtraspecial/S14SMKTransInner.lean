module

public import CFSG.LargeExtraspecial.S14SMKTransLift
public import CFSG.LargeExtraspecial.S14SMKDeltaRank
public import CFSG.LargeExtraspecial.S14SMKGramPhi
public import CFSG.LargeExtraspecial.S14SMKModCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable
  [IsSimpleGroup G] (I : Inputs10) {ψ : Mbar0 S ≃* T46}
  {φ : S.Qt ≃ₗ[ZMod 2] V}

omit
  [IsSimpleGroup G] in
theorem isPGroup_preUA (ψ : Mbar0 S ≃* T46) {i : ℕ} (hi : i < 891) :
    IsPGroup 2 (((UA i).comap (piM S ψ)).map S.Mbar.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (UA i) := IsPGroup.of_card (card_UA hi)
  exact (h1.comap_of_injective _ (piM_injective ψ)).map _

include I in
theorem exists_isConj_mem_Dl_of_mem_UA (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g₀ : G}
    (haQ : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hane : g₀ * S.z * g₀⁻¹ ≠ S.z) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) {i : ℕ} (hi : i < 891)
    (hUi : piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) ∈ UA i) :
    ∃ v, IsConj S.z v ∧ v ∈ S.QG ⊓ S.Qa g := by
  have hD := QG_inf_Qa_ne_bot ψ hw hxM hxQ (not_exists_conj_mul_z S hxz)
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
  have hPp := isPGroup_preUA ψ hi
  have hPW : ∀ p ∈ ((UA i).comap (piM S ψ)).map S.Mbar.subtype,
      ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g),
      (p : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rintro _ ⟨m, hm, rfl⟩ w hw'
    obtain ⟨m₁, hm₁⟩ := exists_rhoM_eq m
    have hm1 : piM S ψ (rhoM S m₁) ∈ UA i := by rw [hm₁]; exact hm
    have hcomm : rhoM S m₁ * rhoM S ⟨_, hxM⟩ = rhoM S ⟨_, hxM⟩ * rhoM S m₁ := by
      apply piM_injective ψ
      rw [map_mul, map_mul]
      exact (commute_of_mem_UA hi hm1 hUi).eq
    obtain ⟨m', hm'x, hm'⟩ := exists_commute_rhoM_eq_of_not_isConj S hxM hxz m₁ hcomm
    obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hw'
    have e : (((m : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = (S.ρ m' : S.O) := by
      rw [← coe_rhoM, hm', hm₁]
    show ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl d) ∈ _
    rw [e, S.ρ_cl m' hdQ]
    exact S.cl_mem_clSub (conj_mem_Dl S m'.2 hm'x hd) (conj_mem_Dl S m'.2 hm'x hd).1
  obtain ⟨w, hwW, hw0, hwfix⟩ := exists_fixed_ne_zero_of_le S hPp hW0 hPW
  have hφw : φ w = wtV i := by
    have hfix : ∀ q ∈ planeSet i, tvEquiv q.val (φ w) = φ w := by
      intro q hq
      have hqW : q ∈ wPlane i := by rw [wPlane_eq_planeSet hi]; exact hq
      obtain ⟨m₁, h0, hm₁⟩ := exists_rhoM_mem_Mbar0 ψ ⟨tvP q, tvP_mem q⟩
      have hmP : (S.ρ m₁ : S.O) ∈ ((UA i).comap (piM S ψ)).map S.Mbar.subtype := by
        refine ⟨rhoM S m₁, ?_, rfl⟩
        show piM S ψ (rhoM S m₁) ∈ UA i
        have := piM_of_mem ψ ⟨rhoM S m₁, h0⟩
        rw [hm₁] at this
        rw [this]
        exact tvP_mem_UA hqW
      have h1 := hwfix _ hmP
      have h2 := hφ.Phi_eq_rhoMod I hw haQ hane m₁ h0
      rw [hm₁, rhoMod_tvP] at h2
      rw [← h2, Phi_apply, LinearEquiv.symm_apply_apply, h1]
    rcases (fixed_iff hi (φ w)).mp hfix with h | h
    · exact absurd (φ.injective (h.trans φ.map_zero.symm)) hw0
    · exact h
  obtain ⟨h, hbQ, hbne, hplane⟩ := exists_planeOf_eq ψ hw haQ hane ⟨i, hi⟩
  have hcl : S.cl (h * S.z * h⁻¹) = w := by
    rw [cl_eq_xcl I ψ hw hbQ hbne, hplane, ← hφ.symm_wtV ⟨i, hi⟩, ← hφw,
      LinearEquiv.symm_apply_apply]
  obtain ⟨d, hd, hdQ, rfl⟩ := S.mem_clSub_iff.mp hwW
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hw0 S.cl_one
  exact ⟨d, SME.isConj_of_cl_eq S (isConj_iff.mpr ⟨h, rfl⟩) hbQ hdQ hd1 hcl, hd⟩

end CFSG.LargeExtraspecial.S14.SMK
