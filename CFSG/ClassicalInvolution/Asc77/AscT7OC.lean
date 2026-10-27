module

public import CFSG.ClassicalInvolution.Asc77.AscT7OB
public import CFSG.ClassicalInvolution.Asc77.AscT7MK
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Local

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

set_option linter.unusedSectionVars false

open CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare QuadraticMap
open scoped commutatorElement

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Cent

variable (Q) in
@[expose] def cplxD (A : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) :=
  (orthogonalOperatorCentralizer Q A.toLinearMap).map
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

variable (Q) in
@[expose] def cplxS (A : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) := ⁅cplxD Q A, cplxD Q A⁆

theorem mem_cplxD {A g : V ≃ₗ[F] V} :
    g ∈ cplxD Q A ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ∀ x, g (A x) = A (g x) := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, hc, rfl⟩

theorem cplxD_le_orthogonalGroup (A : V ≃ₗ[F] V) :
    cplxD Q A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun _ hg => (mem_cplxD.mp hg).1

theorem cplxS_le_cplxD (A : V ≃ₗ[F] V) : cplxS Q A ≤ cplxD Q A := by
  rw [cplxS, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have e : (⁅g₁, g₂⁆ : V ≃ₗ[F] V) = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := commutatorElement_def g₁ g₂
  rw [e]
  exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)

theorem conj_mem_cplxS {A g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∃ c : F, ∀ x, A (g x) = c • g (A x)) {s : V ≃ₗ[F] V} (hs : s ∈ cplxS Q A) :
    g * s * g⁻¹ ∈ cplxS Q A := by
  obtain ⟨c, hc⟩ := hc
  have hD : (cplxD Q A).map (MulAut.conj g).toMonoidHom ≤ cplxD Q A := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdO, hdA⟩ := mem_cplxD.mp hd
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_cplxD.mpr ⟨mul_mem (mul_mem hg hdO) (inv_mem hg), fun x => ?_⟩
    set u : V := (g⁻¹ : V ≃ₗ[F] V) x with hu
    have hxu : g u = x := by rw [hu]; exact LinearEquiv.apply_symm_apply g x
    have h1 : (g⁻¹ : V ≃ₗ[F] V) (A x) = c • A u := by
      have := hc u
      rw [hxu] at this
      rw [this, map_smul]
      exact congrArg (c • ·) (LinearEquiv.symm_apply_apply g (A u))
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change g (d ((g⁻¹ : V ≃ₗ[F] V) (A x))) = A (g (d ((g⁻¹ : V ≃ₗ[F] V) x)))
    rw [h1, ← hu, map_smul, map_smul, hdA u, hc (d u)]
  have hmap : ⁅cplxD Q A, cplxD Q A⁆.map (MulAut.conj g).toMonoidHom ≤ cplxS Q A := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hD hD
  exact hmap ⟨s, hs, by simp [MulAut.conj_apply]⟩

theorem le_cplxS_of_perfect {A : V ≃ₗ[F] V} {P : Subgroup (V ≃ₗ[F] V)}
    (hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hPA : ∀ g ∈ P, ∀ x, g (A x) = A (g x))
    (hP : P ≤ ⁅P, P⁆) : P ≤ cplxS Q A := by
  have hPD : P ≤ cplxD Q A := fun g hg => mem_cplxD.mpr ⟨hPO hg, hPA g hg⟩
  exact hP.trans (Subgroup.commutator_mono hPD hPD)

theorem cplxS_eq (A : V ≃ₗ[F] V) :
    cplxS Q A = (commutator ↥(orthogonalOperatorCentralizer Q A.toLinearMap)).map
      ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
        (orthogonalOperatorCentralizer Q A.toLinearMap).subtype) := by
  rw [map_commutator_eq, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

end Cent

structure CplxLayer (Q : QuadraticForm F V) (A : V ≃ₗ[F] V) (S : Subgroup (V ≃ₗ[F] V)) : Prop where
  le_D : ∀ s ∈ S, s ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ∀ x, s (A x) = A (s x)
  le_E : S ≤ elementaryGroup Q
  quasi : CFSG.Open.IsQuasisimple ↥S
  norm : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∃ c : F, ∀ x, A (g x) = c • g (A x)) →
    ∀ s ∈ S, g * s * g⁻¹ ∈ S
  perf : ∀ P : Subgroup (V ≃ₗ[F] V), P ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
    (∀ g ∈ P, ∀ x, g (A x) = A (g x)) → P ≤ ⁅P, P⁆ → P ≤ S

variable [Finite F] [FiniteDimensional F V]

theorem cplxLayer (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    {A : V ≃ₗ[F] V} (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hA2 : ∀ x, A (A x) = -x)
    (hdim : 6 ≤ Module.finrank F V)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) :
    CplxLayer Q A (cplxS Q A) := by
  have hqs := isQuasisimple_commutator_cplx hodd Q hQ A hAO hA2 hdim
  have hqS : CFSG.IsQuasisimple ↥(cplxS Q A) := by
    rw [cplxS_eq]
    have hinj : Function.Injective
        ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
          (orthogonalOperatorCentralizer Q A.toLinearMap).subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    exact isQuasisimple_of_equiv (Subgroup.equivMapOfInjective _ _ hinj) hqs
  refine ⟨fun s hs => mem_cplxD.mp (cplxS_le_cplxD A hs), ?_, ⟨Group.isPerfect_def.mp hqS.1,
    hqS.2.1⟩, fun g hg hc s hs => conj_mem_cplxS hg hc hs, fun P hPO hPA hP =>
      le_cplxS_of_perfect hPO hPA hP⟩
  calc cplxS Q A ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
        Subgroup.commutator_mono (cplxD_le_orthogonalGroup A) (cplxD_le_orthogonalGroup A)
    _ ≤ elementaryGroup Q := hE

section Outer

variable {X : Type} [Group X]

@[expose] def ActsAs (e : ↥(elementaryGroup Q) →* X) (y : X) (A : V ≃ₗ[F] V) : Prop :=
  ∀ g h : ↥(elementaryGroup Q), (h : V ≃ₗ[F] V) = A * g * A⁻¹ → y * e g * y⁻¹ = e h

theorem ker_le_center_of_kerScalar {e : ↥(elementaryGroup Q) →* X} (hker : KerScalar Q e) :
    e.ker ≤ Subgroup.center ↥(elementaryGroup Q) := by
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  exact Subtype.ext (commute_of_mem_scalars (hker g hg) (h : V ≃ₗ[F] V)).symm

theorem img_eq_map (e : ↥(elementaryGroup Q) →* X) (H : Subgroup (V ≃ₗ[F] V)) :
    img e H = (H.subgroupOf (elementaryGroup Q)).map e := by
  ext x
  rw [mem_img_iff, Subgroup.mem_map]
  exact ⟨fun ⟨g, hg, hx⟩ => ⟨g, Subgroup.mem_subgroupOf.mpr hg, hx⟩,
    fun ⟨g, hg, hx⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg, hx⟩⟩

theorem layerData_of_outer (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) {y : X}
    {A : V ≃ₗ[F] V} (hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hA : ActsAs e y A)
    {S : Subgroup (V ≃ₗ[F] V)} (hS : CplxLayer Q A S) (B : Subgroup X)
    (hcover : B ≤ Subgroup.zpowers y ⊔ img e S) : LayerData e.range B y (img e S) := by
  have hAmem : ∀ g : ↥(elementaryGroup Q), A * (g : V ≃ₗ[F] V) * A⁻¹ ∈ elementaryGroup Q :=
    fun g => conj_mem_elementaryGroup hAO g.2
  have hSq : CFSG.Open.IsQuasisimple ↥(S.subgroupOf (elementaryGroup Q)) :=
    openQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS.le_E).symm hS.quasi
  have hq : CFSG.Open.IsQuasisimple ↥(img e S) := by
    rw [img_eq_map]
    exact CFSG.ClassicalInvolution.Balance.Bootstrap.isQuasisimple_map_of_ker_le_center e
      (ker_le_center_of_kerScalar hker) hSq
  have hPperf : ⁅img e S, img e S⁆ = img e S :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hq.1)
  refine ⟨?_, ?_, hPperf.symm.le, ⟨{img e S}, ?_, ?_⟩, hcover⟩
  · intro p hp
    obtain ⟨g, hgS, rfl⟩ := (mem_img_iff e).mp hp
    refine ⟨img_le_range e S hp, ?_⟩
    have hgA : (g : V ≃ₗ[F] V) = A * g * A⁻¹ := by
      have : (g : V ≃ₗ[F] V) * A = A * g := LinearEquiv.ext fun x => (hS.le_D _ hgS).2 x
      symm
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact mul_inv_eq_iff_eq_mul.mp (hA g g hgA)
  · rintro x ⟨hxr, hxc⟩ p hp
    obtain ⟨g, rfl⟩ := hxr
    obtain ⟨s, hsS, rfl⟩ := (mem_img_iff e).mp hp
    have hyc : y * e g = e g * y := Subgroup.mem_centralizer_iff.mp hxc y rfl
    set h : ↥(elementaryGroup Q) := ⟨A * (g : V ≃ₗ[F] V) * A⁻¹, hAmem g⟩ with hh
    have h1 : y * e g * y⁻¹ = e h := hA g h rfl
    have h2 : e h = e g := by rw [← h1, hyc]; group
    have h3 : e (h * g⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    obtain ⟨c, hc⟩ := mem_scalars.mp (hker _ h3)
    have h4 : ∀ z, A ((g : V ≃ₗ[F] V) z) = c • (g : V ≃ₗ[F] V) (A z) := by
      intro z
      have h7 := hc ((g : V ≃ₗ[F] V) (A z))
      have hcoe : ((h * g⁻¹ : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) =
          A * (g : V ≃ₗ[F] V) * A⁻¹ * (g : V ≃ₗ[F] V)⁻¹ := rfl
      rw [hcoe] at h7
      simp only [LinearEquiv.mul_apply] at h7
      rw [show ((g : V ≃ₗ[F] V)⁻¹ : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) (A z)) = A z from
        LinearEquiv.symm_apply_apply _ (A z)] at h7
      rw [show ((A⁻¹ : V ≃ₗ[F] V)) (A z) = z from LinearEquiv.symm_apply_apply A z] at h7
      exact h7
    have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q g.2
    have h5 := hS.norm _ hgO ⟨c, h4⟩ s hsS
    have h6 : (g : V ≃ₗ[F] V) * s * (g : V ≃ₗ[F] V)⁻¹ ∈ S := h5
    refine (mem_img_iff e).mpr ⟨g * s * g⁻¹, ?_, ?_⟩
    · simpa using h6
    · simp [map_mul, map_inv]
  · intro H hH
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact ⟨le_rfl, hq, fun p hp k hk => mul_mem (mul_mem hp hk) (inv_mem hp)⟩
  · exact le_iSup₂_of_le (img e S) (Set.mem_singleton _) le_rfl

end Outer

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
