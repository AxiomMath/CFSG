module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdInv
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjointY

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg MinData

variable {τ : Tag} {D : MinData τ} (R : Type*) [CommRing R]

@[expose] def adjNormalizer (S : AdjSigns τ) (D : MinData τ) :
    Subgroup (Module.End R (Fin D.d →₀ R))ˣ where
  carrier := {g | (∀ v, ∃ w, (g : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
      ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) = adjMap R S D w) ∧
    ∀ v, ∃ w, ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) *
      adjMap R S D v * (g : Module.End R (Fin D.d →₀ R)) = adjMap R S D w}
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨w, hw⟩ := hh₁ v
      obtain ⟨w', hw'⟩ := hg₁ w
      refine ⟨w', ?_⟩
      rw [mul_inv_rev, Units.val_mul, Units.val_mul, ← hw', ← hw]
      simp only [mul_assoc]
    · obtain ⟨w, hw⟩ := hg₂ v
      obtain ⟨w', hw'⟩ := hh₂ w
      refine ⟨w', ?_⟩
      rw [mul_inv_rev, Units.val_mul, Units.val_mul, ← hw', ← hw]
      simp only [mul_assoc]
  one_mem' := ⟨fun v => ⟨v, by simp⟩, fun v => ⟨v, by simp⟩⟩
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    exact ⟨hg₂, fun v => by simpa only [inv_inv] using hg₁ v⟩

variable {R}

theorem mem_adjNormalizer {S : AdjSigns τ} {g : (Module.End R (Fin D.d →₀ R))ˣ} :
    g ∈ adjNormalizer R S D ↔
      (∀ v, ∃ w, (g : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
        ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) =
          adjMap R S D w) ∧
      ∀ v, ∃ w, ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) *
        adjMap R S D v * (g : Module.End R (Fin D.d →₀ R)) = adjMap R S D w :=
  Iff.rfl

@[expose] def adEnd
    (S : AdjSigns τ) (g : (Module.End R (Fin D.d →₀ R))ˣ) :
    Module.End R (RootModule τ R) :=
  adjInv R S D ∘ₗ (LinearMap.mulLeft R (g : Module.End R (Fin D.d →₀ R)) ∘ₗ
    LinearMap.mulRight R ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
      Module.End R (Fin D.d →₀ R))) ∘ₗ adjMap R S D

theorem adEnd_apply
    (S : AdjSigns τ) (g : (Module.End R (Fin D.d →₀ R))ˣ) (v : RootModule τ R) :
    adEnd S g v = adjInv R S D ((g : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
      ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R))) := by
  simp only [adEnd, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
    mul_assoc]

variable (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)

include hV hpd in
theorem adjMap_adEnd
    {S : AdjSigns τ} {g : (Module.End R (Fin D.d →₀ R))ˣ}
    (hg : g ∈ adjNormalizer R S D) (v : RootModule τ R) :
    adjMap R S D (adEnd S g v) = (g : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
      ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) := by
  obtain ⟨w, hw⟩ := hg.1 v
  rw [adEnd_apply, hw, adjInv_adjMap R hV hpd S]

@[expose] def adHom
    (S : AdjSigns τ) :
    adjNormalizer R S D →* Module.End R (RootModule τ R) where
  toFun g := adEnd S (g : (Module.End R (Fin D.d →₀ R))ˣ)
  map_one' := LinearMap.ext fun v => by
    rw [adEnd_apply, OneMemClass.coe_one, inv_one, Units.val_one, one_mul, mul_one,
      adjInv_adjMap R hV hpd S, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun v => adjMap_injective R hV hpd S (by
    rw [Module.End.mul_apply, adjMap_adEnd hV hpd (g * h).2, adjMap_adEnd hV hpd g.2,
      adjMap_adEnd hV hpd h.2, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Units.val_mul]
    simp only [mul_assoc])

@[expose] def ad
    (S : AdjSigns τ) : adjNormalizer R S D →* (Module.End R (RootModule τ R))ˣ :=
  (adHom hV hpd S).toHomUnits

theorem coe_ad
    (S : AdjSigns τ) (g : adjNormalizer R S D) :
    ((ad hV hpd S g : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) =
      adEnd S (g : (Module.End R (Fin D.d →₀ R))ˣ) :=
  rfl

theorem adjMap_ad
    (S : AdjSigns τ) (g : adjNormalizer R S D) (v : RootModule τ R) :
    adjMap R S D (((ad hV hpd S g : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) v) =
      ((g : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
        (((g : (Module.End R (Fin D.d →₀ R))ˣ)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
          Module.End R (Fin D.d →₀ R)) :=
  adjMap_adEnd hV hpd g.2 v

theorem ad_apply_eq_iff
    (S : AdjSigns τ) (g : adjNormalizer R S D) (v w : RootModule τ R) :
    ((ad hV hpd S g : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) v = w ↔
      ((g : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
        (((g : (Module.End R (Fin D.d →₀ R))ˣ)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
          Module.End R (Fin D.d →₀ R)) = adjMap R S D w := by
  rw [← adjMap_ad hV hpd S g v]
  exact (adjMap_injective R hV hpd S).eq_iff.symm

variable (R) in
theorem rootUnit_inv
    (γ : Fin τ.rank → ℤ) (c : R) :
    (rootUnit hV R γ c)⁻¹ = rootUnit hV R γ (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← rootUnit_add, neg_add_cancel, rootUnit_zero]

variable {S : AdjSigns τ} (hS : S.check D = true)

include hpd hS in
theorem rootUnit_single_mem
    (i : Fin τ.rank) (c : R) :
    rootUnit hV R (Pi.single i 1) c ∈ adjNormalizer R S D :=
  ⟨fun v => ⟨_, rootUnit_conj_adjMap R hpd hV hS i c v⟩, fun v => ⟨xOp τ R i (-c) v, by
    rw [rootUnit_inv R hV, ← rootUnit_conj_adjMap R hpd hV hS i (-c) v, rootUnit_inv R hV,
      neg_neg]⟩⟩

include hpd hS in
theorem rootUnit_neg_single_mem
    (i : Fin τ.rank) (c : R) :
    rootUnit hV R (-Pi.single i 1) c ∈ adjNormalizer R S D :=
  ⟨fun v => ⟨_, rootUnit_neg_conj_adjMap R hpd hV hS i c v⟩, fun v => ⟨yOp τ R i (-c) v, by
    rw [rootUnit_inv R hV, ← rootUnit_neg_conj_adjMap R hpd hV hS i (-c) v, rootUnit_inv R hV,
      neg_neg]⟩⟩

theorem ad_rootUnit_single
    (i : Fin τ.rank) (c : R) :
    ad hV hpd S ⟨rootUnit hV R (Pi.single i 1) c, rootUnit_single_mem hV hpd hS i c⟩ =
      xUnit τ R i c := by
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [coe_ad, adEnd_apply, rootUnit_conj_adjMap R hpd hV hS i c v, adjInv_adjMap R hV hpd S,
    coe_xUnit]

theorem ad_rootUnit_neg_single
    (i : Fin τ.rank) (c : R) :
    ad hV hpd S ⟨rootUnit hV R (-Pi.single i 1) c, rootUnit_neg_single_mem hV hpd hS i c⟩ =
      yUnit τ R i c := by
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [coe_ad, adEnd_apply, rootUnit_neg_conj_adjMap R hpd hV hS i c v, adjInv_adjMap R hV hpd S,
    coe_yUnit]

section Field

variable (K : Type*) [Field K]

include hpd hS in
theorem minGroup_le_adjNormalizer :
    hV.minGroup K ≤ adjNormalizer K S D :=
  minGroup_le_of_simple hV K fun i c =>
    ⟨rootUnit_single_mem hV hpd hS i c, rootUnit_neg_single_mem hV hpd hS i c⟩

@[expose] def adMin :
    hV.minGroup K →* ModGL τ K :=
  (ad hV hpd S).comp (Subgroup.inclusion (minGroup_le_adjNormalizer hV hpd hS K))

theorem adMin_apply
    (g : hV.minGroup K) :
    adMin hV hpd hS K g = ad hV hpd S ⟨g, minGroup_le_adjNormalizer hV hpd hS K g.2⟩ :=
  rfl

theorem adMin_xm_single
    (i : Fin τ.rank) (c : K) :
    adMin hV hpd hS K (hV.xm K (Pi.single i 1) c) = xUnit τ K i c :=
  ad_rootUnit_single hV hpd hS i c

theorem adMin_xm_neg_single
    (i : Fin τ.rank) (c : K) :
    adMin hV hpd hS K (hV.xm K (-Pi.single i 1) c) = yUnit τ K i c :=
  ad_rootUnit_neg_single hV hpd hS i c

theorem range_adMin
    : (adMin hV hpd hS K).range = adjointGroup τ K := by
  rw [MonoidHom.range_eq_map, ← Isogeny.closure_xm_simple_eq_top hV K, MonoidHom.map_closure,
    adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨i, c, rfl | rfl⟩, rfl⟩
    · exact ⟨i, c, Or.inl (by rw [adMin_xm_single, coe_xUnit])⟩
    · exact ⟨i, c, Or.inr (by rw [adMin_xm_neg_single, coe_yUnit])⟩
  · rintro ⟨i, c, h | h⟩
    · exact ⟨hV.xm K (Pi.single i 1) c, ⟨i, c, Or.inl rfl⟩,
        by rw [adMin_xm_single]; exact Units.ext h.symm⟩
    · exact ⟨hV.xm K (-Pi.single i 1) c, ⟨i, c, Or.inr rfl⟩,
        by rw [adMin_xm_neg_single]; exact Units.ext h.symm⟩

end Field

end CFSG.TauCetiBridge.Minuscule
