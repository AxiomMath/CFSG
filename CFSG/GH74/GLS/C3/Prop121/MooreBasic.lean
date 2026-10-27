module

public import CFSG.GH74.GLS.C3.Prop121.MooreCS
public import CFSG.GH74.GLS.C3.Layer2.InvolutionExt
public import CFSG.GH74.GLS.C3.Prop121.Defs

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2

variable {G : Type} [Group G]

theorem sq_eq_one_inv {g : G} (hg : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rwa [← sq])

theorem conj_conj_invol {g : G} (hg : g ^ 2 = 1) (z : G) : g * (g * z * g⁻¹) * g⁻¹ = z := by
  have h2 : g * g = 1 := by rwa [← sq]
  have h3 : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, h2, inv_one]
  calc g * (g * z * g⁻¹) * g⁻¹ = (g * g) * z * (g⁻¹ * g⁻¹) := by group
    _ = z := by rw [h2, h3]; simp

@[expose] def phiOf {n : ℕ} {L : Subgroup G} {u : G}
    (Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1))) : Perm (Fin (n + 1)) →* G :=
  (L ⊔ zpowers u).subtype.comp Θ.symm.toMonoidHom

theorem phiOf_apply {n : ℕ} {L : Subgroup G} {u : G}
    (Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1))) (p : Perm (Fin (n + 1))) :
    phiOf Θ p = ((Θ.symm p : ↥(L ⊔ zpowers u)) : G) := rfl

theorem phiOf_injective {n : ℕ} {L : Subgroup G} {u : G}
    (Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1))) : Function.Injective (phiOf Θ) :=
  Subtype.val_injective.comp Θ.symm.injective

theorem sign_conj_perm {α : Type*} [Fintype α] [DecidableEq α] (μ p : Perm α) :
    sign (μ⁻¹ * p * μ) = sign p := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
  rcases Int.units_eq_one_or (sign μ) with h | h <;> simp [h]

theorem exists_phi {n : ℕ} (hn : 3 ≤ n) {x : G} {K Q : Subgroup G} {t u g : G} {L : Subgroup G}
    {Θ : ↥(L ⊔ zpowers u) ≃* Perm (Fin (n + 1))} (hS : Stage3Loc n x K Q t u g)
    (hL : ThreeLocal n K t u g L Θ) :
    ∃ φ : Perm (Fin (n + 1)) →* G, PhiData K L u φ ∧ φ (cEnd n) = g * t * g⁻¹ := by
  obtain ⟨hmem, h3⟩ := hL.threeCycle
  set π : Perm (Fin (n + 1)) := Θ ⟨g * t * g⁻¹, hmem⟩ with hπ
  have hπ0 : π 0 = 0 := (hL.stab ⟨g * t * g⁻¹, hmem⟩).1 (mem_sup_left hS.gt_K)
  have hcc := isThreeCycle_cEnd hn
  obtain ⟨μ, hμ⟩ := isConj_iff.1
    (isConj_iff_cycleType_eq.2 (h3.cycleType.trans hcc.cycleType.symm))
  have hc0 : cEnd n 0 = 0 := cEnd_apply_zero hn
  have hcμ : cEnd n (μ 0) = μ 0 := by
    rw [← hμ]
    simp [hπ0]
  set μ' : Perm (Fin (n + 1)) := swap (μ 0) 0 * μ with hμ'
  have hμ'0 : μ' 0 = 0 := by simp [hμ']
  have hcomm : cEnd n * swap (μ 0) 0 = swap (μ 0) 0 * cEnd n := by
    rw [mul_swap_eq_swap_mul, hcμ, hc0]
  have hμπ : μ' * π * μ'⁻¹ = cEnd n := by
    have : μ' * π * μ'⁻¹ = swap (μ 0) 0 * (μ * π * μ⁻¹) * (swap (μ 0) 0)⁻¹ := by
      simp [hμ', mul_assoc]
    rw [this, hμ, ← hcomm]
    simp [mul_assoc]
  have hπeq : π = μ'⁻¹ * cEnd n * μ' := by
    rw [← hμπ]; group
  refine ⟨(phiOf Θ).comp (MulAut.conj μ'⁻¹).toMonoidHom, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (phiOf_injective Θ).comp (MulAut.conj μ'⁻¹).injective
  · intro p; exact (Θ.symm _).2
  · intro y hy
    refine ⟨μ' * Θ ⟨y, hy⟩ * μ'⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have : μ'⁻¹ * (μ' * Θ ⟨y, hy⟩ * μ'⁻¹) * μ' = Θ ⟨y, hy⟩ := by group
    rw [this, phiOf_apply]
    simp
  · intro p
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h := hL.alt (Θ.symm (μ'⁻¹ * p * μ'))
    rw [MulEquiv.apply_symm_apply, sign_conj_perm] at h
    rw [phiOf_apply]
    exact h
  · intro p
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h := hL.stab (Θ.symm (μ'⁻¹ * p * μ'))
    rw [MulEquiv.apply_symm_apply] at h
    rw [phiOf_apply, h]
    simp only [Perm.mul_apply, hμ'0]
    rw [Equiv.Perm.inv_eq_iff_eq, hμ'0]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hπeq, hπ, phiOf_apply]
    simp

end CFSG.GH74.GLS.C3.Prop121
