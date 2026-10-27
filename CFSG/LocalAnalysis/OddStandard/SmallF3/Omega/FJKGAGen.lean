module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXDef
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCov
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def FJKGAAt (Y : Type) [Group Y] : Prop :=
  ∀ (y : Y) (B : Subgroup Y), orderOf y = 2 → Sl23PocketIn ⊤ y B →
    ∀ σ : MulAut Y, σ * σ = 1 → σ ≠ 1 → (∀ b ∈ B, σ b = b) → σ ≠ MulAut.conj y →
      ∃ J : Subgroup Y, IsComponentIn J (L34GFix σ) ∧ InFStar J ∧ B ≤ J

theorem fjKGAAt_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : FJKGAAt Y) : FJKGAAt Y' := by
  intro y' B' hy' hB' σ' hσ' hσ'1 hfix' hσ'y
  obtain ⟨σ, hσapply⟩ : ∃ σ : MulAut Y, ∀ p : Y, e (σ p) = σ' (e p) :=
    ⟨(e.trans σ').trans e.symm, fun p => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]⟩
  have hσσ : σ * σ = 1 := by
    ext x
    have hxx : σ (σ x) = x := by
      apply e.injective
      rw [hσapply (σ x), hσapply x]
      have hh := congrArg (fun f : MulAut Y' => f (e x)) hσ'
      simpa only [MulAut.mul_apply, MulAut.one_apply] using hh
    simpa only [MulAut.mul_apply, MulAut.one_apply] using hxx
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hσ'1
    ext x
    have h2 := hσapply (e.symm x)
    rw [h1, MulAut.one_apply, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  have hy : orderOf (e.symm y') = 2 := by
    rw [MulEquiv.orderOf_eq e.symm y', hy']
  have hB : Sl23PocketIn ⊤ (e.symm y') (B'.comap e.toMonoidHom) := by
    have h1 := Sl23PocketIn.map_mulEquiv e.symm hB'
    rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
      ← Subgroup.comap_equiv_eq_map_symm'] at h1
  have hfixB : ∀ b ∈ B'.comap e.toMonoidHom, σ b = b := by
    intro b hb
    apply e.injective
    rw [hσapply b]
    exact hfix' (e b) (Subgroup.mem_comap.mp hb)
  have hσy : σ ≠ MulAut.conj (e.symm y') := by
    intro hc
    apply hσ'y
    ext x
    have h2 := hσapply (e.symm x)
    rw [hc, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply] at h2
    rw [MulAut.conj_apply]
    exact h2.symm
  obtain ⟨J, hJ, hJF, hBJ⟩ := h (e.symm y') (B'.comap e.toMonoidHom) hy hB σ hσσ hσ1 hfixB hσy
  have hFix : (L34GFix σ).map e.toMonoidHom = L34GFix σ' := by
    have h1 : L34GFix σ = (L34GFix σ').comap e.toMonoidHom := by
      ext p
      rw [l34g_mem_fix, Subgroup.mem_comap, l34g_mem_fix]
      change σ p = p ↔ σ' (e p) = e p
      constructor
      · intro hp
        rw [← hσapply p, hp]
      · intro hp
        exact e.injective (by rw [hσapply p, hp])
    rw [h1, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  refine ⟨J.map e.toMonoidHom, ?_, l34g_x_inFStar_map_inj e.toMonoidHom e.injective hJF, ?_⟩
  · rw [← hFix]
    exact (sec63PT_isComponentIn_map_iff e.toMonoidHom e.injective).mpr hJ
  · intro b hb
    have hb' : b ∈ (B'.comap e.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
      exact hb
    exact Subgroup.map_mono hBJ hb'

end CFSG.OddStandard.SmallF3.Omega
