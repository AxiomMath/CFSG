module

public import CFSG.LargeExtraspecial.GLRFormSigma

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

@[expose] noncomputable def formOf (s : S.O) : LinearMap.BilinForm (ZMod 2) C.At :=
  S.q.polarBilin.compl₁₂ C.At.subtype
    (((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ∘ₗ C.At.subtype)

theorem formOf_apply (s : S.O) (a a' : C.At) :
    C.formOf s a a' = polar S.q a ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) a') := rfl

theorem formOf_mul_apply (s : S.O) {x : S.O} (hx : x ∈ C.Xbar) (a a' : C.At) :
    C.formOf (s * x) a a' = C.formOf s a (C.resAt ⟨x, hx⟩ a') := rfl

variable {C}

theorem formOf_left {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) {a : C.At}
    (h : ∀ a', C.formOf s a a' = 0) : a = 0 := by
  refine Subtype.ext (C.eq_zero_of_mem_At_of_forall_polar a.2 fun w hw => ?_)
  rw [← C.map_At s hs hsX] at hw
  obtain ⟨a', ha', rfl⟩ := hw
  rw [polar_comm]
  exact h ⟨a', ha'⟩

theorem formOf_right {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) {a' : C.At}
    (h : ∀ a, C.formOf s a a' = 0) : a' = 0 := by
  have h1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a' = 0 :=
    C.eq_zero_of_mem_Bt_of_forall_polar (C.apply_mem_Bt_of_not_mem hs hsX a'.2)
      fun v hv => h ⟨v, hv⟩
  exact Subtype.ext ((map_eq_zero_iff _ (s : S.Qt ≃ₗ[ZMod 2] S.Qt).injective).mp h1)

theorem mul_self_eq_one_of_formOf_symm {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar)
    (hsymm : ∀ a a', C.formOf s a a' = C.formOf s a' a) : s * s = 1 := by
  have hss := C.mul_mem_Xbar_of_not_mem hs hs hsX hsX
  refine C.eq_one_of_forall_At hss fun a ha => ?_
  have key : ∀ a' : C.At, C.formOf s (C.resAt ⟨s * s, hss⟩ ⟨a, ha⟩ - ⟨a, ha⟩) a' = 0 := by
    intro a'
    rw [map_sub, LinearMap.sub_apply, hsymm ⟨a, ha⟩ a', sub_eq_zero]
    simp only [formOf_apply, resAt_apply]
    conv_rhs => rw [← polar_apply_apply s, polar_comm]
    rfl
  have := formOf_left hs hsX key
  rw [sub_eq_zero] at this
  exact congrArg Subtype.val this

variable (C)

theorem exists_formOf_mul_eq {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar)
    (β : LinearMap.BilinForm (ZMod 2) C.At) (hβ : ∀ a', (∀ a, β a a' = 0) → a' = 0) :
    ∃ x : C.Xbar, C.formOf (s * x) = β := by
  let Ψ : C.At →ₗ[ZMod 2] Module.Dual (ZMod 2) C.At := (C.formOf s).flip
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a' ha'
    exact formOf_right hs hsX fun a => LinearMap.congr_fun ha' a
  have hrank : finrank (ZMod 2) C.At = finrank (ZMod 2) (Module.Dual (ZMod 2) C.At) :=
    (Subspace.dual_finrank_eq).symm
  have hΨs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hΨ
  let e := LinearEquiv.ofBijective Ψ ⟨hΨ, hΨs⟩
  let φ : C.At →ₗ[ZMod 2] C.At := (e.symm : _ →ₗ[ZMod 2] C.At) ∘ₗ β.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a' ha'
    rw [LinearMap.mem_ker] at ha'
    have h1 : β.flip a' = 0 := by
      have := congrArg e ha'
      simpa [φ] using this
    exact hβ a' fun a => LinearMap.congr_fun h1 a
  let φe : C.At ≃ₗ[ZMod 2] C.At := LinearEquiv.ofInjectiveEndo φ hφ
  obtain ⟨x, hx⟩ := C.resAt_bijective.2 φe
  refine ⟨x, LinearMap.ext₂ fun a a' => ?_⟩
  rw [formOf_mul_apply C s x.2]
  have h1 : C.resAt ⟨x, x.2⟩ a' = φ a' := by
    rw [show (⟨x, x.2⟩ : C.Xbar) = x from rfl, hx]
    rfl
  rw [h1]
  have h2 : Ψ (φ a') = β.flip a' := by
    change e (e.symm (β.flip a')) = β.flip a'
    exact e.apply_symm_apply _
  exact LinearMap.congr_fun h2 a

end Config

namespace Levi

variable {C} (Λ : Levi C)

theorem exists_sigma_formOf_eq (β : LinearMap.BilinForm (ZMod 2) C.At)
    (hβs : ∀ a a', β a a' = β a' a) (hβ : ∀ a', (∀ a, β a a' = 0) → a' = 0) :
    ∃ σ, ∃ hσ : σ ∈ S.M, σ ∉ C.X ∧ Λ.Normalizes σ ∧ (σ * σ = 1 ∨ σ * σ = S.z) ∧
      C.formOf (S.ρ ⟨σ, hσ⟩) = β := by
  obtain ⟨σ₀, hσ₀M, hσ₀X, hσ₀L⟩ := Λ.exists_sigma
  have hsM : S.ρ ⟨σ₀, hσ₀M⟩ ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX : S.ρ ⟨σ₀, hσ₀M⟩ ∉ C.Xbar := fun h => hσ₀X (C.mem_X_iff.mpr ⟨hσ₀M, h⟩)
  obtain ⟨x, hx⟩ := C.exists_formOf_mul_eq hsM hsX β hβ
  obtain ⟨l, hl⟩ := Λ.toXbar_bijective.2 x
  have hlM := Λ.L_le_M l.2
  have hσM : σ₀ * l ∈ S.M := S.M.mul_mem hσ₀M hlM
  have hρσ : S.ρ ⟨σ₀ * l, hσM⟩ = S.ρ ⟨σ₀, hσ₀M⟩ * (x : S.O) := by
    rw [← hl, toXbar_coe, ← map_mul]
    rfl
  have hσX : σ₀ * l ∉ C.X := fun h => hσ₀X (by
    have := C.X.mul_mem h (C.X.inv_mem (Λ.L_le_X l.2))
    rwa [mul_inv_cancel_right] at this)
  have hform : C.formOf (S.ρ ⟨σ₀ * l, hσM⟩) = β := by rw [hρσ, hx]
  refine ⟨σ₀ * l, hσM, hσX, hσ₀L.mul (Λ.normalizes_of_mem l.2), ?_, hform⟩
  have hsM' : S.ρ ⟨σ₀ * l, hσM⟩ ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX' : S.ρ ⟨σ₀ * l, hσM⟩ ∉ C.Xbar := fun h => hσX (C.mem_X_iff.mpr ⟨hσM, h⟩)
  have hsq := Config.mul_self_eq_one_of_formOf_symm hsM' hsX'
    (fun a a' => by rw [hform]; exact hβs a a')
  have hσσQ : (σ₀ * l) * (σ₀ * l) ∈ S.QG := by
    rw [← S.ρ_eq_one_iff ⟨_, S.M.mul_mem hσM hσM⟩, show
      (⟨(σ₀ * l) * (σ₀ * l), S.M.mul_mem hσM hσM⟩ : S.M) = ⟨σ₀ * l, hσM⟩ * ⟨σ₀ * l, hσM⟩ from rfl,
      map_mul, hsq]
  have hσσX := C.mul_mem_X_of_not_mem hσM hσM hσX hσX
  obtain ⟨l₀, hl₀, h₀⟩ := Λ.exists_eq_of_normalizes hσσX
    ((hσ₀L.mul (Λ.normalizes_of_mem l.2)).mul (hσ₀L.mul (Λ.normalizes_of_mem l.2)))
  rcases h₀ with h₀ | h₀
  · left
    rw [h₀]
    exact Λ.eq_one_of_mem_QG _ hl₀ (h₀ ▸ hσσQ)
  · right
    have : l₀ ∈ S.QG := by
      have := S.QG.mul_mem (S.QG.inv_mem S.z_mem_QG) hσσQ
      rwa [h₀, inv_mul_cancel_left] at this
    rw [h₀, Λ.eq_one_of_mem_QG _ hl₀ this, mul_one]

end Levi

end CFSG.LargeExtraspecial.GLR
