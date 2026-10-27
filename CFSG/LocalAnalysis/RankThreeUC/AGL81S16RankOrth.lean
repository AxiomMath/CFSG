module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix

variable {F : Type} [Field F] [Finite F]

@[expose] def horth (σ : F ≃+* F) (W : Submodule F (Fin 4 → F)) : Submodule F (Fin 4 → F) where
  carrier := {y | ∀ x ∈ W, herm σ x y = 0}
  add_mem' := fun {y y'} hy hy' x hx => by rw [herm_add_right, hy x hx, hy' x hx, add_zero]
  zero_mem' := fun x _ => herm_zero_right σ x
  smul_mem' := fun c y hy x hx => by rw [herm_smul_right, hy x hx, mul_zero]

theorem mem_horth {σ : F ≃+* F} {W : Submodule F (Fin 4 → F)} {y : Fin 4 → F} :
    y ∈ horth σ W ↔ ∀ x ∈ W, herm σ x y = 0 := Iff.rfl

private theorem horth_herm_sum_left {ι : Type*} [Fintype ι] (σ : F ≃+* F) (s : ι → F)
    (v : ι → Fin 4 → F) (y : Fin 4 → F) :
    herm σ (∑ j, s j • v j) y = ∑ j, σ (s j) * herm σ (v j) y := by
  simp only [herm_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem card_mul_card_horth {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ)
    (W : Submodule F (Fin 4 → F)) :
    Nat.card ↥W * Nat.card ↥(horth σ W) = Nat.card (Fin 4 → F) := by
  let b : Module.Basis (Fin (Module.finrank F ↥W)) F ↥W := Module.finBasis F ↥W
  let u : Fin (Module.finrank F ↥W) → Fin 4 → F := fun j => (b j : Fin 4 → F)
  have hu : LinearIndependent F u :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  let ψ : (Fin 4 → F) →ₗ[F] (Fin (Module.finrank F ↥W) → F) :=
    { toFun := fun y j => herm σ (u j) y
      map_add' := fun y y' => by
        funext j
        exact herm_add_right σ (u j) y y'
      map_smul' := fun c y => by
        funext j
        exact herm_smul_right σ c (u j) y }
  have hψ : ∀ y j, ψ y j = herm σ (u j) y := fun y j => rfl
  have hker : LinearMap.ker ψ = horth σ W := by
    ext y
    rw [LinearMap.mem_ker, mem_horth]
    constructor
    · intro hy x hx
      have hy' : ∀ j, herm σ (u j) y = 0 := fun j => by
        have h := congrFun hy j
        rwa [hψ] at h
      have hxc : x = ∑ j, (b.repr ⟨x, hx⟩ j) • u j := by
        have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h
        simp only [Submodule.coe_smul] at h
        exact h.symm
      rw [hxc, horth_herm_sum_left]
      exact Finset.sum_eq_zero fun j _ => by simp [hy' j]
    · intro hy
      funext j
      rw [hψ]
      exact hy (u j) (b j).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfr⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range ψ)
      (lt_top_iff_ne_top.mpr hne)
    have hfy : ∀ y, f (ψ y) = 0 := fun y =>
      LinearMap.mem_ker.mp (hfr (LinearMap.mem_range_self ψ y))
    obtain ⟨c, hfc⟩ : ∃ c : Fin (Module.finrank F ↥W) → F, ∀ v, f v = ∑ i, v i * c i :=
      ⟨fun i => f (fun j => if i = j then 1 else 0), fun v =>
        (LinearMap.pi_apply_eq_sum_univ f v).trans
          (Finset.sum_congr rfl fun i _ => smul_eq_mul _ _)⟩
    have hz : ∀ y, herm σ (∑ i, σ.symm (c i) • u i) y = 0 := by
      intro y
      have hfy' : ∑ i, ψ y i * c i = 0 := by
        rw [← hfc (ψ y)]
        exact hfy y
      rw [horth_herm_sum_left]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hfy'
      rw [RingEquiv.apply_symm_apply, hψ]
      ring
    have hz0 : ∑ i, σ.symm (c i) • u i = 0 := eq_zero_of_herm σ hz
    have hd : ∀ i, σ.symm (c i) = 0 :=
      Fintype.linearIndependent_iff.mp hu (fun i => σ.symm (c i)) hz0
    have hc0 : ∀ i, c i = 0 := fun i => by
      have h := σ.apply_symm_apply (c i)
      rw [hd i, map_zero] at h
      exact h.symm
    exact hf0 (LinearMap.ext fun v => by rw [hfc v, LinearMap.zero_apply]; simp [hc0])
  rw [← hker]
  have hrank := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrank
  have hW : Nat.card ↥W = Nat.card F ^ Module.finrank F ↥W := Module.natCard_eq_pow_finrank
  have hK : Nat.card ↥(LinearMap.ker ψ) = Nat.card F ^ Module.finrank F ↥(LinearMap.ker ψ) :=
    Module.natCard_eq_pow_finrank
  have hV : Nat.card (Fin 4 → F) = Nat.card F ^ 4 := by
    have h : Nat.card (Fin 4 → F) = Nat.card F ^ Module.finrank F (Fin 4 → F) :=
      Module.natCard_eq_pow_finrank
    rwa [Module.finrank_fin_fun] at h
  rw [hW, hK, hV, ← pow_add, hrank]

end CFSG.LocalAnalysis.RankThreeUC
