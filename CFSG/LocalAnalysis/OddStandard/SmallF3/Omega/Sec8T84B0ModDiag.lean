module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModH1
public import Certificates.Certificate442267

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

variable {G : Type} [Group G] {E B : Subgroup G} {hBE : B ≤ E} {u : MulAut ↥E}
  {hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B} {A : Subgroup (MulAut ↥E)}
  {hAu : ∀ a ∈ A, a * u = u * a}

theorem rel_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x y : M} (h : Rel x y) :
    Rel (f x) (f y) := by
  unfold Certificates.Asc82NormA6.Rel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg f h1
  · simpa only [map_pow, map_one] using congrArg f h2
  · simpa only [map_mul, map_pow, map_one] using congrArg f h3
  · simpa only [map_mul, map_pow, map_one] using congrArg f h4
  · simpa only [map_mul, map_pow, map_one] using congrArg f h5
  · simpa only [map_mul, map_pow, map_one] using congrArg f h6

theorem rel_of_injective {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (hf : Function.Injective f) {x y : M} (h : Rel (f x) (f y)) : Rel x y := by
  unfold Certificates.Asc82NormA6.Rel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf (by simpa only [map_pow, map_one] using h1)
  · exact hf (by simpa only [map_pow, map_one] using h2)
  · exact hf (by simpa only [map_mul, map_pow, map_one] using h3)
  · exact hf (by simpa only [map_mul, map_pow, map_one] using h4)
  · exact hf (by simpa only [map_mul, map_pow, map_one] using h5)
  · exact hf (by simpa only [map_mul, map_pow, map_one] using h6)

theorem Frame.exists_frame
    (F : Frame E B hBE u hfix A hAu) :
    ∃ m : Mat4, ∀ a : ↥A, Acts F.θ (a : MulAut ↥E)
      (Dm m (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))) := by
  let hF := Certificates.certificate442267
  let σA : alternatingGroup (Fin 6) :=
    ⟨sigma, Equiv.Perm.mem_alternatingGroup.mpr hF.sigma_even⟩
  let τA : alternatingGroup (Fin 6) :=
    ⟨tau, Equiv.Perm.mem_alternatingGroup.mpr hF.tau_even⟩
  let aσ : ↥A := F.ψ.symm σA
  let aτ : ↥A := F.ψ.symm τA
  have hσψ : F.ψ aσ = σA := F.ψ.apply_symm_apply σA
  have hτψ : F.ψ aτ = τA := F.ψ.apply_symm_apply τA
  have hψσ : ((F.ψ aσ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = sigma := by
    rw [hσψ]
  have hψτ : ((F.ψ aτ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = tau := by
    rw [hτψ]
  have block : ∀ a : ↥A, ∃ U : Mat4, matHom F.θ (a : MulAut ↥E) =
      blk (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) U := by
    intro a
    obtain ⟨α, U, hActs, hres⟩ := Frame.exists_blk F (a : MulAut ↥E) (hAu a a.2)
    have hα : α = rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) :=
      Frame.matrix_unique F (a : MulAut ↥E) (hAu a a.2) α _ hres (F.res_acts a)
    exact ⟨U, by rw [matHom_eq hActs, hα]⟩
  let Ufun : ↥A → Mat4 := fun a => Classical.choose (block a)
  have hUfun : ∀ a : ↥A, matHom F.θ (a : MulAut ↥E) =
      blk (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) (Ufun a) :=
    fun a => Classical.choose_spec (block a)
  have hUσ : matHom F.θ (aσ : MulAut ↥E) = blk (rho sigma) (Ufun aσ) := by
    rw [hUfun aσ, hψσ]
  have hUτ : matHom F.θ (aτ : MulAut ↥E) = blk (rho tau) (Ufun aτ) := by
    rw [hUfun aτ, hψτ]
  have hAlt : Rel σA τA :=
    rel_of_injective (alternatingGroup (Fin 6)).subtype Subtype.val_injective
      (x := σA) (y := τA) hF.rel
  have hRelA : Rel aσ aτ := by
    apply rel_of_injective F.ψ.toMonoidHom F.ψ.injective
    change Rel (F.ψ aσ) (F.ψ aτ)
    rw [hσψ, hτψ]
    exact hAlt
  have hRelMat : Rel (blk (rho sigma) (Ufun aσ)) (blk (rho tau) (Ufun aτ)) := by
    have h := rel_map ((matHom F.θ).comp A.subtype) hRelA
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hUσ, hUτ] using h
  obtain ⟨m, hmσ, hmτ⟩ := h1_vanish hRelMat
  have hσ_acts : Acts F.θ (aσ : MulAut ↥E) (Dm m (rho sigma)) := by
    have h := matHom_acts F.θ (aσ : MulAut ↥E)
    have hmat : blk (rho sigma) (m * rho sigma + rho sigma * m) = Dm m (rho sigma) := by
      rw [Dm, add_comm]
    rw [hUσ, hmσ, hmat] at h
    exact h
  have hτ_acts : Acts F.θ (aτ : MulAut ↥E) (Dm m (rho tau)) := by
    have h := matHom_acts F.θ (aτ : MulAut ↥E)
    have hmat : blk (rho tau) (m * rho tau + rho tau * m) = Dm m (rho tau) := by
      rw [Dm, add_comm]
    rw [hUτ, hmτ, hmat] at h
    exact h
  let W : ↥A → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) := fun a =>
    Dm m (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
  have hWmul : ∀ a b : ↥A, W (a * b) = W a * W b := by
    intro a b
    change Dm m (rho ((F.ψ (a * b) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
      = Dm m (rho ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
        * Dm m (rho ((F.ψ b : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
    rw [map_mul F.ψ a b, Subgroup.coe_mul, hF.rho_mul, Dm_mul]
  have hWone : W 1 = 1 := by
    change Dm m (rho ((F.ψ (1 : ↥A) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) = 1
    rw [map_one F.ψ, Subgroup.coe_one, hF.rho_one, Dm_one]
  have hWaσ : W aσ = Dm m (rho sigma) := by
    change Dm m (rho ((F.ψ aσ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
      = Dm m (rho sigma)
    rw [hψσ]
  have hWaτ : W aτ = Dm m (rho tau) := by
    change Dm m (rho ((F.ψ aτ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)))
      = Dm m (rho tau)
    rw [hψτ]
  let Good : Subgroup ↥A :=
    { carrier := {a | Acts F.θ (a : MulAut ↥E) (W a)}
      one_mem' := by
        show Acts F.θ ((1 : ↥A) : MulAut ↥E) (W 1)
        rw [hWone, Subgroup.coe_one]
        exact acts_one F.θ
      mul_mem' := by
        intro a b ha hb
        show Acts F.θ ((a * b : ↥A) : MulAut ↥E) (W (a * b))
        rw [hWmul, Subgroup.coe_mul]
        exact ha.mul hb
      inv_mem' := by
        intro a ha
        show Acts F.θ ((a⁻¹ : ↥A) : MulAut ↥E) (W a⁻¹)
        obtain ⟨N, hN⟩ := exists_acts F.θ ((a⁻¹ : ↥A) : MulAut ↥E)
        obtain ⟨N₀, hMN₀, hN₀M⟩ := Acts.exists_inv ha
        have hMN : W a * N = 1 := by
          have h := Acts.mul ha hN
          have h1 : (a : MulAut ↥E) * ((a⁻¹ : ↥A) : MulAut ↥E) = 1 := by
            rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
          rw [h1] at h
          exact Acts.matrix_eq h (acts_one F.θ)
        have hMW : W a * W a⁻¹ = 1 := by
          rw [← hWmul a a⁻¹, mul_inv_cancel, hWone]
        have hN₀ : N₀ = W a⁻¹ := by
          calc N₀ = N₀ * 1 := (mul_one N₀).symm
            _ = N₀ * (W a * W a⁻¹) := by rw [hMW]
            _ = (N₀ * W a) * W a⁻¹ := by rw [mul_assoc]
            _ = 1 * W a⁻¹ := by rw [hN₀M]
            _ = W a⁻¹ := one_mul _
        have hNN₀ : N = N₀ := by
          calc N = 1 * N := (one_mul N).symm
            _ = (N₀ * W a) * N := by rw [hN₀M]
            _ = N₀ * (W a * N) := by rw [mul_assoc]
            _ = N₀ * 1 := by rw [hMN]
            _ = N₀ := mul_one _
        rw [hNN₀, hN₀] at hN
        exact hN }
  have hσ_good : aσ ∈ Good := by
    show Acts F.θ (aσ : MulAut ↥E) (W aσ)
    rw [hWaσ]
    exact hσ_acts
  have hτ_good : aτ ∈ Good := by
    show Acts F.θ (aτ : MulAut ↥E) (W aτ)
    rw [hWaτ]
    exact hτ_acts
  let K' : Subgroup (Equiv.Perm (Fin 6)) :=
    (Good.map F.ψ.toMonoidHom).map (alternatingGroup (Fin 6)).subtype
  have hσK : sigma ∈ K' :=
    Subgroup.mem_map.mpr ⟨σA, Subgroup.mem_map.mpr ⟨aσ, hσ_good, hσψ⟩, rfl⟩
  have hτK : tau ∈ K' :=
    Subgroup.mem_map.mpr ⟨τA, Subgroup.mem_map.mpr ⟨aτ, hτ_good, hτψ⟩, rfl⟩
  have hle : Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) ≤ K' :=
    (Subgroup.closure_le K').mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hσK
      · exact hτK)
  have hgood : ∀ a : ↥A, a ∈ Good := by
    intro a
    have haK : ((F.ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ∈ K' :=
      hle (hF.gen _ (F.ψ a).2)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp haK
    obtain ⟨a', ha'good, ha'y⟩ := Subgroup.mem_map.mp hy
    have hψa' : F.ψ a' = F.ψ a := by
      change F.ψ.toMonoidHom a' = F.ψ.toMonoidHom a
      rw [ha'y]
      exact Subtype.ext hyx
    have haa : a' = a := F.ψ.injective hψa'
    rw [haa] at ha'good
    exact ha'good
  exact ⟨m, fun a => hgood a⟩

end T84Mod

end CFSG.OddStandard.SmallF3.Omega
