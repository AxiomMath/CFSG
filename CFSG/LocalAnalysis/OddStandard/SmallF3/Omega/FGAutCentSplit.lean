module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

structure FGSplit (Q : QuadraticForm (ZMod 3) V) where
  W : Submodule (ZMod 3) V
  P : Submodule (ZMod 3) V
  isCompl : IsCompl W P
  polar_zero : ∀ w ∈ W, ∀ p ∈ P, QuadraticMap.polar Q w p = 0
  nondegW : (Q.restrict W).Nondegenerate
  nondegP : (Q.restrict P).Nondegenerate
  extW : OGroup (Q.restrict W) →* OGroup Q
  extP : OGroup (Q.restrict P) →* OGroup Q
  extW_W : ∀ (a : OGroup (Q.restrict W)) (w : W),
    ((extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) =
      (((a : OGroup (Q.restrict W)) : W ≃ₗ[ZMod 3] W) w : V)
  extW_P : ∀ (a : OGroup (Q.restrict W)) (p : P),
    ((extW a : OGroup Q) : V ≃ₗ[ZMod 3] V) (p : V) = (p : V)
  extP_P : ∀ (b : OGroup (Q.restrict P)) (p : P),
    ((extP b : OGroup Q) : V ≃ₗ[ZMod 3] V) (p : V) =
      (((b : OGroup (Q.restrict P)) : P ≃ₗ[ZMod 3] P) p : V)
  extP_W : ∀ (b : OGroup (Q.restrict P)) (w : W),
    ((extP b : OGroup Q) : V ≃ₗ[ZMod 3] V) (w : V) = (w : V)
  det_extP : ∀ b : OGroup (Q.restrict P),
    QuadraticMap.orthogonalDet Q (extP b) = QuadraticMap.orthogonalDet (Q.restrict P) b
  ext_surj : ∀ g : OGroup Q, (∀ w : W, (g : V ≃ₗ[ZMod 3] V) (w : V) = (w : V)) →
    (∀ p : P, (g : V ≃ₗ[ZMod 3] V) (p : V) ∈ P) → ∃ b, extP b = g

variable {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def FGSplit.fix (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    FGSplit Q where
  W := fixSp s
  P := commSp s
  isCompl := isCompl_fixSp_commSp hs
  polar_zero := fun _ hv _ hw => polar_fixSp_commSp hs hv hw
  nondegW := nondegenerate_restrict_fixSp hQ hs
  nondegP := nondegenerate_restrict_commSp hQ hs
  extW := (blockHom hs).comp (MonoidHom.inl _ _)
  extP := (blockHom hs).comp (MonoidHom.inr _ _)
  extW_W := fun a w => by
    have h := blockHom_apply hs (a, 1) w 0
    simpa using h
  extW_P := fun a p => by
    have h := blockHom_apply hs (a, 1) 0 p
    simpa using h
  extP_P := fun b p => by
    have h := blockHom_apply hs (1, b) 0 p
    simpa using h
  extP_W := fun b w => by
    have h := blockHom_apply hs (1, b) w 0
    simpa using h
  det_extP := fun b => by
    have h := orthogonalDet_blockHom hs (1, b)
    simpa using h
  ext_surj := fun g hgW hgP => by
    have hmap : (commSp s).map (g : V →ₗ[ZMod 3] V) = commSp s := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro x ⟨c, hc, rfl⟩
        exact hgP ⟨c, hc⟩
      · rw [LinearEquiv.finrank_map_eq]
    have hgc : g ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) :=
      (mem_centralizer_iff_map_commSp hQ hs g).mpr hmap
    rw [← range_blockHom hQ hs] at hgc
    obtain ⟨p, hp⟩ := hgc
    have hp1 : p.1 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      have h := blockHom_apply hs p w 0
      rw [hp] at h
      have hw := hgW w
      simp only [Submodule.coe_zero, add_zero, map_zero] at h
      apply Subtype.ext
      exact (h.symm.trans hw)
    refine ⟨p.2, ?_⟩
    show blockHom hs (1, p.2) = g
    rw [← hp1, Prod.mk.eta]
    exact hp

@[expose] noncomputable def FGSplit.comm (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    FGSplit Q where
  W := commSp s
  P := fixSp s
  isCompl := (isCompl_fixSp_commSp hs).symm
  polar_zero := fun _ hw _ hv => by
    rw [QuadraticMap.polar_comm]
    exact polar_fixSp_commSp hs hv hw
  nondegW := nondegenerate_restrict_commSp hQ hs
  nondegP := nondegenerate_restrict_fixSp hQ hs
  extW := (blockHom hs).comp (MonoidHom.inr _ _)
  extP := (blockHom hs).comp (MonoidHom.inl _ _)
  extW_W := fun a w => by
    have h := blockHom_apply hs (1, a) 0 w
    simpa using h
  extW_P := fun a p => by
    have h := blockHom_apply hs (1, a) p 0
    simpa using h
  extP_P := fun b p => by
    have h := blockHom_apply hs (b, 1) p 0
    simpa using h
  extP_W := fun b w => by
    have h := blockHom_apply hs (b, 1) 0 w
    simpa using h
  det_extP := fun b => by
    have h := orthogonalDet_blockHom hs (b, 1)
    simpa using h
  ext_surj := fun g hgW _ => by
    have hmap : (commSp s).map (g : V →ₗ[ZMod 3] V) = commSp s := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro x ⟨c, hc, rfl⟩
        show (g : V ≃ₗ[ZMod 3] V) c ∈ commSp s
        rw [show (g : V ≃ₗ[ZMod 3] V) c = c from hgW ⟨c, hc⟩]
        exact hc
      · rw [LinearEquiv.finrank_map_eq]
    have hgc : g ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) :=
      (mem_centralizer_iff_map_commSp hQ hs g).mpr hmap
    rw [← range_blockHom hQ hs] at hgc
    obtain ⟨p, hp⟩ := hgc
    have hp2 : p.2 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      have h := blockHom_apply hs p 0 w
      rw [hp] at h
      have hw := hgW w
      simp only [Submodule.coe_zero, zero_add, map_zero] at h
      apply Subtype.ext
      exact (h.symm.trans hw)
    refine ⟨p.1, ?_⟩
    show blockHom hs (p.1, 1) = g
    rw [← hp2, Prod.mk.eta]
    exact hp

end CFSG.OddStandard.SmallF3.Omega
