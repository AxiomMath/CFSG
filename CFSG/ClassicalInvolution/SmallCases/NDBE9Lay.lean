module

public import CFSG.ClassicalInvolution.Asc77.AscT7OC

public section

namespace CFSG.ClassicalInvolution.NDB.SpinOuter

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.ModelFacts.Orth15.T7O
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {X : Type} [Group X] {S T : Submodule F V} {w : V ≃ₗ[F] V}

theorem join_le_centralizer (hw : SplitInv Q S T w) :
    elemOn Q S ⊔ elemOn Q T ≤ Subgroup.centralizer ({w} : Set (V ≃ₗ[F] V)) := by
  refine sup_le (fun y hy => ?_) (fun y hy => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hw.commute_of_mem_elemOn_left hy).symm
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hw.commute_of_mem_elemOn_right hy).symm

theorem eq_one_of_scalar_left (hw : SplitInv Q S T w) (hT : T ≠ ⊥) {g : V ≃ₗ[F] V}
    (hg : g ∈ elemOn Q S) (hs : g ∈ scalars F V) : g = 1 := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 : g z = z := (support_of_mem_elemOn hg).2 z fun x hx => by
    rw [polar_comm]
    exact hw.orth x hx z hz
  have hc1 : c = 1 := by
    rw [hc z] at h1
    have : (c - 1) • z = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  refine LinearEquiv.ext fun v => ?_
  rw [hc v, hc1, one_smul]
  rfl

theorem eq_one_of_scalar_right (hw : SplitInv Q S T w) (hS : S ≠ ⊥) {g : V ≃ₗ[F] V}
    (hg : g ∈ elemOn Q T) (hs : g ∈ scalars F V) : g = 1 := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have h1 : g z = z := (support_of_mem_elemOn hg).2 z fun x hx => hw.orth z hz x hx
  have hc1 : c = 1 := by
    rw [hc z] at h1
    have : (c - 1) • z = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
  refine LinearEquiv.ext fun v => ?_
  rw [hc v, hc1, one_smul]
  rfl

theorem exists_layers_img (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e)
    (hw : SplitInv Q S T w) (hS : S ≠ ⊥) (hT : T ≠ ⊥) (layS : LayerGenOn Q S)
    (layT : LayerGenOn Q T) :
    ∃ 𝓗 : Set (Subgroup X),
      (∀ H ∈ 𝓗, H ≤ img e (elemOn Q S ⊔ elemOn Q T) ∧ CFSG.Open.IsQuasisimple ↥H ∧
        ∀ p ∈ img e (elemOn Q S ⊔ elemOn Q T), ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧
      img e (elemOn Q S ⊔ elemOn Q T) ≤ ⨆ H ∈ 𝓗, H := by
  obtain ⟨𝓗S, hS', hSc⟩ := layS
  obtain ⟨𝓗T, hT', hTc⟩ := layT
  have horth : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0 := fun x hx y hy => hw.orth x hx y hy
  have horth' : ∀ x ∈ T, ∀ y ∈ S, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]; exact horth y hy x hx
  refine ⟨(fun H => img e H) '' (𝓗S ∪ 𝓗T), ?_, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    rcases hH with hH | hH
    · obtain ⟨hHle, hHq, hHn⟩ := hS' H hH
      have hHE : H ≤ elementaryGroup Q := hHle.trans elemOn_le_elementaryGroup
      refine ⟨img_mono e (hHle.trans le_sup_left), isQuasisimple_img hker hHE hHq
        (fun g hg hs => eq_one_of_scalar_left hw hT (hHle hg) hs), ?_⟩
      intro p hp k hk
      obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hp
      obtain ⟨k', hk', rfl⟩ := (mem_img_iff e).mp hk
      refine (mem_img_iff e).mpr ⟨g * k' * g⁻¹, ?_, by simp⟩
      simpa using conj_mem_join_of_normalized horth hHle hHn hg hk'
    · obtain ⟨hHle, hHq, hHn⟩ := hT' H hH
      have hHE : H ≤ elementaryGroup Q := hHle.trans elemOn_le_elementaryGroup
      refine ⟨img_mono e (hHle.trans le_sup_right), isQuasisimple_img hker hHE hHq
        (fun g hg hs => eq_one_of_scalar_right hw hS (hHle hg) hs), ?_⟩
      intro p hp k hk
      obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hp
      obtain ⟨k', hk', rfl⟩ := (mem_img_iff e).mp hk
      refine (mem_img_iff e).mpr ⟨g * k' * g⁻¹, ?_, by simp⟩
      rw [sup_comm] at hg
      simpa using conj_mem_join_of_normalized horth' hHle hHn hg hk'
  · set M : Subgroup X := ⨆ Hb ∈ (fun H => img e H) '' (𝓗S ∪ 𝓗T), Hb with hM
    set K : Subgroup (V ≃ₗ[F] V) := (M.comap e).map (elementaryGroup Q).subtype with hK
    have hlay : ∀ H ∈ 𝓗S ∪ 𝓗T, H ≤ elementaryGroup Q → H ≤ K := by
      intro H hH hHE h hh
      refine ⟨⟨h, hHE hh⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      exact (le_iSup₂ (f := fun (Hb : Subgroup X) (_ : Hb ∈ (fun H => img e H) '' (𝓗S ∪ 𝓗T)) => Hb)
        (img e H) ⟨H, hH, rfl⟩) ((mem_img_iff e).mpr ⟨⟨h, hHE hh⟩, hh, rfl⟩)
    have hSK : elemOn Q S ≤ K := by
      refine hSc.trans (iSup₂_le fun H hH => hlay H (Or.inl hH) ?_)
      exact (hS' H hH).1.trans elemOn_le_elementaryGroup
    have hTK : elemOn Q T ≤ K := by
      refine hTc.trans (iSup₂_le fun H hH => hlay H (Or.inr hH) ?_)
      exact (hT' H hH).1.trans elemOn_le_elementaryGroup
    intro x hx
    obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hx
    obtain ⟨g', hg', hg'g⟩ := sup_le hSK hTK hg
    have : g' = g := Subtype.ext hg'g
    subst this
    exact hg'

theorem img_join_perfect (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e)
    (hw : SplitInv Q S T w) (hS : S ≠ ⊥) (hT : T ≠ ⊥) (layS : LayerGenOn Q S)
    (layT : LayerGenOn Q T) :
    img e (elemOn Q S ⊔ elemOn Q T) ≤
      ⁅img e (elemOn Q S ⊔ elemOn Q T), img e (elemOn Q S ⊔ elemOn Q T)⁆ := by
  obtain ⟨𝓗, hH, hP⟩ := exists_layers_img e hker hw hS hT layS layT
  refine hP.trans (iSup₂_le fun H hH' => ?_)
  obtain ⟨hHle, hHq, -⟩ := hH H hH'
  rw [← CFSG.ClassicalInvolution.ModelFacts.Orth15.commutator_self_of_perfect hHq.1]
  exact Subgroup.commutator_mono hHle hHle

theorem layerData_of_split (h2 : (2 : F) ≠ 0) (e : ↥(elementaryGroup Q) →* X)
    (hker : KerScalar Q e) {y : X} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hw : SplitInv Q S T w) (hS : S ≠ ⊥) (hT : T ≠ ⊥) (hy : ActsAs e y w)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) (B : Subgroup X)
    (hcover : B ≤ Subgroup.zpowers y ⊔ img e (elemOn Q S ⊔ elemOn Q T)) :
    LayerData e.range B y (img e (elemOn Q S ⊔ elemOn Q T)) := by
  have : Nontrivial V := by
    obtain ⟨x, -, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    exact ⟨⟨x, 0, hx0⟩⟩
  refine ⟨?_, ?_, img_join_perfect e hker hw hS hT layS layT,
    exists_layers_img e hker hw hS hT layS layT, hcover⟩
  · intro p hp
    obtain ⟨g, hg, rfl⟩ := (mem_img_iff e).mp hp
    refine ⟨img_le_range e _ hp, ?_⟩
    have hgw : (g : V ≃ₗ[F] V) = w * g * w⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mp (join_le_centralizer hw hg)
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact mul_inv_eq_iff_eq_mul.mp (hy g g hgw)
  · rintro x ⟨hxr, hxc⟩ p hp
    obtain ⟨g, rfl⟩ := hxr
    obtain ⟨s, hsS, rfl⟩ := (mem_img_iff e).mp hp
    have hyc : y * e g = e g * y := Subgroup.mem_centralizer_iff.mp hxc y rfl
    set h : ↥(elementaryGroup Q) := ⟨w * (g : V ≃ₗ[F] V) * w⁻¹,
      conj_mem_elementaryGroup hwO g.2⟩ with hh
    have h1 : y * e g * y⁻¹ = e h := hy g h rfl
    have h2' : e h = e g := by rw [← h1, hyc]; group
    have h3 : e (h * g⁻¹) = 1 := by rw [map_mul, map_inv, h2', mul_inv_cancel]
    obtain ⟨c, hc⟩ := mem_scalars.mp (hker _ h3)
    have hstar : ∀ t, w ((g : V ≃ₗ[F] V) t) = c • (g : V ≃ₗ[F] V) (w t) := by
      intro t
      have h7 := hc ((g : V ≃ₗ[F] V) (w t))
      have hcoe : ((h * g⁻¹ : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) =
          w * (g : V ≃ₗ[F] V) * w⁻¹ * (g : V ≃ₗ[F] V)⁻¹ := rfl
      rw [hcoe] at h7
      simp only [LinearEquiv.mul_apply] at h7
      rw [show ((g : V ≃ₗ[F] V)⁻¹ : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) (w t)) = w t from
        LinearEquiv.symm_apply_apply _ (w t)] at h7
      rw [show ((w⁻¹ : V ≃ₗ[F] V)) (w t) = t from LinearEquiv.symm_apply_apply w t] at h7
      exact h7
    have h4 : ∀ x, (g : V ≃ₗ[F] V) (w x) = c • w ((g : V ≃ₗ[F] V) x) := by
      intro x
      have h8 := hstar (w x)
      rw [hw.aa x] at h8
      calc (g : V ≃ₗ[F] V) (w x) = w (w ((g : V ≃ₗ[F] V) (w x))) := (hw.aa _).symm
        _ = w (c • (g : V ≃ₗ[F] V) x) := by rw [h8]
        _ = c • w ((g : V ≃ₗ[F] V) x) := map_smul w c _
    have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q g.2
    have h5 := hw.conj_mem_join h2 hgO h4 hsS
    refine (mem_img_iff e).mpr ⟨g * s * g⁻¹, ?_, ?_⟩
    · simpa using h5
    · simp [map_mul, map_inv]

end CFSG.ClassicalInvolution.NDB.SpinOuter
