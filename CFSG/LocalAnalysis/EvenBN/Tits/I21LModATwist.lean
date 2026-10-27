module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModAHeart
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModARestr
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6Aut

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {G : Type*} [Group G]

theorem modA_cent_trivial (e : G ≃* alternatingGroup (Fin 6))
    (r : G →* (W ≃ₗ[ZMod 2] W)) (hW : finrank (ZMod 2) W = 4)
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, r g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (n : W ≃ₗ[ZMod 2] W) (hn : ∀ g, n * r g = r g * n) : n = 1 := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  let φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W) := r.comp e.symm.toMonoidHom
  have hirr' : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U fun g u hu => by simpa [φ] using hU (e g) u hu
  have hf : ∀ g w, (n : W →ₗ[ZMod 2] W) (φ g w) = φ g ((n : W →ₗ[ZMod 2] W) w) := by
    intro g w
    have := congrArg (fun m : W ≃ₗ[ZMod 2] W => m w) (hn (e.symm g))
    simpa [φ] using this
  rcases modA_end_scalar φ hirr' hW (n : W →ₗ[ZMod 2] W) hf with h | h
  · exfalso
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    apply n.injective
    have := congrArg (fun m : W →ₗ[ZMod 2] W => m w) h
    simpa using this
  · refine LinearEquiv.ext fun w => ?_
    have := congrArg (fun m : W →ₗ[ZMod 2] W => m w) h
    simpa using this

variable [Module.Finite (ZMod 2) W]

theorem modA_no_twist [Finite G] (e : G ≃* alternatingGroup (Fin 6))
    (hW : finrank (ZMod 2) W = 4) (r : G →* (W ≃ₗ[ZMod 2] W)) (hr : Function.Injective r)
    (hcent : ∀ n : W ≃ₗ[ZMod 2] W, (∀ g, n * r g = r g * n) → n = 1)
    (c : MulAut G) (hc2 : c * c = 1) (hc1 : c ≠ 1) (hy : ∃ y : G, orderOf y = 5 ∧ c y = y)
    (ψ : W ≃ₗ[ZMod 2] W) (hψ : ∀ g, r (c g) = ψ * r g * ψ⁻¹) : False := by
  obtain ⟨σ, hσ8, hσ⟩ := exists_aut_order_eight e hc2 hc1 hy
  let A : Subgroup (MulAut G) :=
    { carrier := {σ | ∃ n : W ≃ₗ[ZMod 2] W, ∀ g, r (σ g) = n * r g * n⁻¹}
      mul_mem' := fun {σ₁ σ₂} h₁ h₂ => by
        obtain ⟨n₁, hn₁⟩ := h₁
        obtain ⟨n₂, hn₂⟩ := h₂
        refine ⟨n₁ * n₂, fun g => ?_⟩
        rw [MulAut.mul_apply, hn₁, hn₂]
        group
      one_mem' := ⟨1, fun g => by simp⟩
      inv_mem' := fun {σ₁} h₁ => by
        obtain ⟨n₁, hn₁⟩ := h₁
        refine ⟨n₁⁻¹, fun g => ?_⟩
        have h2 := hn₁ (σ₁⁻¹ g)
        rw [MulAut.apply_inv_self] at h2
        rw [inv_inv]
        calc r (σ₁⁻¹ g) = n₁⁻¹ * (n₁ * r (σ₁⁻¹ g) * n₁⁻¹) * n₁ := by group
          _ = n₁⁻¹ * r g * n₁ := by rw [← h2] }
  have hA : σ ∈ A := by
    have hle : Subgroup.closure
        (((MulAut.conj : G →* MulAut G).range : Set (MulAut G)) ∪ {c}) ≤ A := by
      rw [Subgroup.closure_le]
      rintro _ (⟨j, rfl⟩ | rfl)
      · exact ⟨r j, fun g => by simp [MulAut.conj_apply, map_mul]⟩
      · exact ⟨ψ, hψ⟩
    exact hle hσ
  obtain ⟨n, hn⟩ := hA
  have hnk : ∀ (m : ℕ) (g : G), r ((σ ^ m) g) = n ^ m * r g * (n ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro g; simp
    | succ m ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hn, ih, pow_succ']
      group
  have h8 : n ^ 8 = 1 := by
    apply hcent
    intro g
    have h1 := hnk 8 g
    have hs8 : σ ^ 8 = 1 := by rw [← hσ8]; exact pow_orderOf_eq_one σ
    rw [hs8, MulAut.one_apply] at h1
    calc n ^ 8 * r g = (n ^ 8 * r g * (n ^ 8)⁻¹) * n ^ 8 := by group
      _ = r g * n ^ 8 := by rw [← h1]
  have h4 : n ^ 4 = 1 := by
    have := pow_eq_one_of_two_pow n (k := 3) (m := 2) (by simpa using h8) (by rw [hW]; norm_num)
    simpa using this
  have hs4 : σ ^ 4 = 1 := by
    refine MulEquiv.ext fun g => hr ?_
    rw [hnk 4 g, h4]
    simp
  have := orderOf_dvd_of_pow_eq_one hs4
  rw [hσ8] at this
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
