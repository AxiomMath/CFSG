module

public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.GF2Type.Smith1979.GammaU.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module
open CFSG.LargeExtraspecial

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def trEquiv (φ : W ≃ₗ[ZMod 2] V12) : (W ≃ₗ[ZMod 2] W) ≃* (V12 ≃ₗ[ZMod 2] V12) where
  toFun m := φ.symm.trans (m.trans φ)
  invFun l := φ.trans (l.trans φ.symm)
  left_inv m := LinearEquiv.ext fun v => by simp
  right_inv l := LinearEquiv.ext fun v => by simp
  map_mul' m₁ m₂ := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

theorem trEquiv_apply (φ : W ≃ₗ[ZMod 2] V12) (m : W ≃ₗ[ZMod 2] W) (v : V12) :
    trEquiv φ m v = φ (m (φ.symm v)) := rfl

theorem trEquiv_apply_φ (φ : W ≃ₗ[ZMod 2] V12) (m : W ≃ₗ[ZMod 2] W) (w : W) :
    trEquiv φ m (φ w) = φ (m w) := by
  rw [trEquiv_apply, LinearEquiv.symm_apply_apply]

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def Mtr (φ : S.Qt ≃ₗ[ZMod 2] V12) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  (S.Mbar.map S.O.subtype).map (trEquiv φ).toMonoidHom

variable {S}

theorem mem_Mtr {φ : S.Qt ≃ₗ[ZMod 2] V12} {l : V12 ≃ₗ[ZMod 2] V12} :
    l ∈ Mtr S φ ↔ ∃ m ∈ S.Mbar, trEquiv φ (m : S.Qt ≃ₗ[ZMod 2] S.Qt) = l := by
  simp only [Mtr, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, ⟨m, hm, rfl⟩, rfl⟩

theorem tr_mem_Mtr {φ : S.Qt ≃ₗ[ZMod 2] V12} {m : S.O} (hm : m ∈ S.Mbar) :
    trEquiv φ (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Mtr S φ :=
  mem_Mtr.2 ⟨m, hm, rfl⟩

theorem isom_of_mem_Mtr {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : ∀ v, q0 (φ v) = S.q v)
    {l : V12 ≃ₗ[ZMod 2] V12} (hl : l ∈ Mtr S φ) (v : V12) : q0 (l v) = q0 v := by
  obtain ⟨m, -, rfl⟩ := mem_Mtr.1 hl
  rw [trEquiv_apply, hφ, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 m.2, ← hφ,
    LinearEquiv.apply_symm_apply]

theorem irred_Mtr (hirr : ¬ S.IsReducible) (φ : S.Qt ≃ₗ[ZMod 2] V12)
    (U : Submodule (ZMod 2) V12) (hU : ∀ m ∈ Mtr S φ, ∀ w ∈ U, m w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_contra hne
  push Not at hne
  apply hirr
  refine ⟨U.comap (φ : S.Qt →ₗ[ZMod 2] V12), fun h => hne.1 ?_, fun h => hne.2 ?_, ?_⟩
  · rw [eq_bot_iff]
    intro w hw
    have : φ.symm w ∈ U.comap (φ : S.Qt →ₗ[ZMod 2] V12) := by
      rw [Submodule.mem_comap]
      simpa using hw
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    simpa using congrArg φ this
  · rw [eq_top_iff]
    intro w _
    have : φ.symm w ∈ U.comap (φ : S.Qt →ₗ[ZMod 2] V12) := by rw [h]; trivial
    rw [Submodule.mem_comap] at this
    simpa using this
  · intro m v hv
    rw [Submodule.mem_comap] at hv ⊢
    simp only [LinearEquiv.coe_coe] at hv ⊢
    have := hU _ (tr_mem_Mtr (φ := φ) (MonoidHom.mem_range.2 ⟨m, rfl⟩)) _ hv
    rwa [trEquiv_apply_φ] at this

@[expose] def ThetaCompat (φ : S.Qt ≃ₗ[ZMod 2] V12) (θ : S.O) : Prop :=
  (∀ v, φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = theta0 (φ v)) ∨
    ∀ v, φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = theta0 (theta0 (φ v))

theorem tr_theta {φ : S.Qt ≃ₗ[ZMod 2] V12} {θ : S.O} (h : ThetaCompat φ θ) :
    trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) = thetaU ∨
      trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) = thetaU⁻¹ := by
  rcases h with h | h
  · left
    refine LinearEquiv.ext fun v => ?_
    rw [trEquiv_apply, h, LinearEquiv.apply_symm_apply, thetaU_apply]
  · right
    refine LinearEquiv.ext fun v => ?_
    rw [trEquiv_apply, h, LinearEquiv.apply_symm_apply, thetaU_inv_apply]

theorem thetaU_mem_Mtr {φ : S.Qt ≃ₗ[ZMod 2] V12} {θ : S.O} (h : ThetaCompat φ θ)
    (hθ : θ ∈ S.Mbar) : thetaU ∈ Mtr S φ := by
  have hm := tr_mem_Mtr (φ := φ) hθ
  rcases tr_theta h with h' | h'
  · rwa [h'] at hm
  · rw [h'] at hm
    simpa using inv_mem hm

end CFSG.GF2Type.Smith1979.GammaU.Dict
