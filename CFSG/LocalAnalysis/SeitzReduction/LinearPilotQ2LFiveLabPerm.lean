module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveLabSign

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial


section Seitz

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def permElt (e : L ≃* LinearFlag.projectiveSL n K) (σ : Equiv.Perm (Fin n)) : G :=
  ((e.symm (LinearFlag.proj n K (permSL σ)) : L) : G)

theorem permElt_mem (e : L ≃* LinearFlag.projectiveSL n K) (σ : Equiv.Perm (Fin n)) :
    permElt e σ ∈ L :=
  (e.symm (LinearFlag.proj n K (permSL σ))).2

theorem permElt_conj_linTv (e : L ≃* LinearFlag.projectiveSL n K) (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    permElt e σ * linTv e hij * (permElt e σ)⁻¹ = linTv e (σ.symm.injective.ne hij) := by
  rw [permElt, linTv, linTv, ← permSL_mul_transvection_mul_inv σ hij (1 : K)]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem permElt_conj_linTv_dual (e : L ≃* LinearFlag.projectiveSL n K) (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    permElt e σ * linTv (e.trans (LinearFlag.dualAut n K)) hij * (permElt e σ)⁻¹ =
      linTv (e.trans (LinearFlag.dualAut n K)) (σ.symm.injective.ne hij) := by
  rw [linTv_trans_dualAut, linTv_trans_dualAut, permElt_conj_linTv]

theorem permElt_commute (e : L ≃* LinearFlag.projectiveSL n K) {σ τ : Equiv.Perm (Fin n)}
    (h : σ * τ = τ * σ) : permElt e σ * permElt e τ = permElt e τ * permElt e σ := by
  have hmul : ∀ a b : Equiv.Perm (Fin n), permSL (K := K) a * permSL b = permSL (b * a) :=
    fun a b => Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, coe_permSL,
        Matrix.permMatrix_mul])
  rw [permElt, permElt, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, hmul, hmul, h]

end Seitz

section Parabolic

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem mem_pointParabolic_of_conj (hK : Nat.card K = 2) (hn : 2 ≤ n)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) {w : G} (hwL : w ∈ L)
    (hw : ∀ j (hcj : c ≠ j), w * linTv e hcj * w⁻¹ ∈ modelToG e (pointRadical (K := K) c)) :
    w ∈ pointParabolic e c := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hle : modelToG e (pointRadical (K := K) c) ≤
      (modelToG e (pointRadical (K := K) c)).comap (MulAut.conj w).toMonoidHom :=
    modelToG_pointRadical_le hK e c fun j hcj => by
      rw [mem_comap]
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hw j hcj
  set p := e ⟨w, hwL⟩ with hp
  have hpw : ((e.symm p : L) : G) = w := by rw [hp, MulEquiv.symm_apply_apply]
  have hmaps : Set.MapsTo (fun x => p * x * p⁻¹) (pointRadical (K := K) c : Set _)
      (pointRadical (K := K) c : Set _) := by
    intro x hx
    apply mem_of_symm_mem_modelToG e
    have h1 := hle (symm_mem_modelToG e hx)
    rw [mem_comap] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hpw]
    exact h1
  have hinj : Set.InjOn (fun x => p * x * p⁻¹) (pointRadical (K := K) c : Set _) :=
    fun x _ y _ hxy => by simpa using hxy
  have hfin : (pointRadical (K := K) c : Set (LinearFlag.projectiveSL n K)).Finite :=
    Set.toFinite _
  have hpN : p ∈ normalizer (pointRadical (K := K) c : Set (LinearFlag.projectiveSL n K)) := by
    rw [mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact hmaps hv
    · intro hv
      obtain ⟨x, hx, hxv⟩ := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hv
      have hxv' : x = v := by simpa using hxv
      rw [← hxv']
      exact hx
  have hpS := mem_sup_blockSL_of_mem_normalizer_pointRadical hK hn hpN
  rw [← hpw, pointParabolic, ← modelToG_sup_eq_sup]
  exact symm_mem_modelToG e hpS

theorem permElt_mem_pointParabolic (hK : Nat.card K = 2) (hn : 2 ≤ n)
    (e : L ≃* LinearFlag.projectiveSL n K) {σ : Equiv.Perm (Fin n)} {c : Fin n} (hσ : σ c = c) :
    permElt e σ ∈ pointParabolic e c ∧
      permElt e σ ∈ pointParabolic (e.trans (LinearFlag.dualAut n K)) c := by
  have hσ' : σ.symm c = c := by rw [Equiv.symm_apply_eq, hσ]
  refine ⟨mem_pointParabolic_of_conj hK hn e c (permElt_mem e σ) fun j hcj => ?_,
    mem_pointParabolic_of_conj hK hn _ c (permElt_mem e σ) fun j hcj => ?_⟩
  · rw [permElt_conj_linTv]
    have h : σ.symm c ≠ σ.symm j := σ.symm.injective.ne hcj
    rw [hσ'] at h
    have := linTv_mem_pointRadical e h
    convert this using 2
  · rw [permElt_conj_linTv_dual]
    have h : σ.symm c ≠ σ.symm j := σ.symm.injective.ne hcj
    rw [hσ'] at h
    have := linTv_mem_pointRadical (e.trans (LinearFlag.dualAut n K)) h
    convert this using 2

end Parabolic

end CFSG.SeitzReduction.LinearPilot
