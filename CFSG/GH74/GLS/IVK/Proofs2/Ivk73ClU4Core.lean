module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Ext
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Lin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Anti
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU

public noncomputable section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module Matrix CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry
open CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

section Core

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient (onQuotient)

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

noncomputable abbrev liftY (X₂ : Subgroup (sesqProjUnitary h B)) : Subgroup (sesqUnitaryGroup B) :=
  ⁅X₂.comap (QuotientGroup.mk' (sesqNormOneScalars h B)),
    X₂.comap (QuotientGroup.mk' (sesqNormOneScalars h B))⁆

theorem liftY_data [Finite (sesqUnitaryGroup B)] {X₂ : Subgroup (sesqProjUnitary h B)}
    (φ : MulAut (sesqUnitaryGroup B))
    (hφZ : (sesqNormOneScalars h B).map φ.toMonoidHom = sesqNormOneScalars h B)
    (hφφ : ∀ g, φ (φ g) = g)
    (hX : CFSG.Assembly.IsComponentOf X₂
      (fixedSubgroup (onQuotient (sesqNormOneScalars h B) φ hφZ))) :
    CFSG.Assembly.IsComponentOf (liftY X₂) (fixedSubgroup φ) ∧
      (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) = X₂ ∧
      ∀ x ∈ liftY X₂, φ x = x := by
  obtain ⟨-, hYm, hYmap, hYfix⟩ := LocalAnalysis.ComponentInitial.lift_isComponentOf_fixed
    (π := QuotientGroup.mk' (sesqNormOneScalars h B)) (a := φ)
    (α := onQuotient (sesqNormOneScalars h B) φ hφZ) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact sesqNormOneScalars_le_center h B) hφφ
    (fun x => (CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk _ φ hφZ x).symm) hX
  exact ⟨hYm, hYmap, hYfix⟩

@[expose] noncomputable def liftHom (X₂ : Subgroup (sesqProjUnitary h B))
    (hYm : (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) = X₂) :
    liftY X₂ →* X₂ :=
  ((QuotientGroup.mk' (sesqNormOneScalars h B)).comp (liftY X₂).subtype).codRestrict X₂
    (fun y => by
      have h1 := mem_map_of_mem (QuotientGroup.mk' (sesqNormOneScalars h B)) y.2
      rwa [hYm] at h1)

theorem liftHom_surjective (X₂ : Subgroup (sesqProjUnitary h B))
    (hYm : (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) = X₂) :
    Function.Surjective (liftHom X₂ hYm) := by
  intro x
  have hx : (x : sesqProjUnitary h B) ∈
      (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) := by
    rw [hYm]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

theorem liftHom_ker_le_scalars (X₂ : Subgroup (sesqProjUnitary h B))
    (hYm : (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) = X₂)
    (y : liftY X₂) (hy : liftHom X₂ hYm y = 1) :
    (y : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B := by
  have h1 : QuotientGroup.mk' (sesqNormOneScalars h B) (y : sesqUnitaryGroup B) = 1 :=
    congrArg Subtype.val hy
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem liftHom_ker_le_center (X₂ : Subgroup (sesqProjUnitary h B))
    (hYm : (liftY X₂).map (QuotientGroup.mk' (sesqNormOneScalars h B)) = X₂) :
    (liftHom X₂ hYm).ker ≤ center (liftY X₂) := by
  intro y hy
  have h1 := liftHom_ker_le_scalars X₂ hYm y hy
  have h2 := sesqNormOneScalars_le_center h B h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro z
  exact Subtype.ext (h2 z)

end Core

section CoreLinear

open CFSG.ComponentClassification.OddClassSelector (map_conj_eq_of_le_center onQuotient_conj)

theorem su4_core_linear [FiniteDimensional E V] (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hn : finrank E V = 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} [Finite (sesqUnitaryGroup B)] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {X₂ : Subgroup (sesqProjUnitary h B)} (hs : SmallSource X₂)
    {T S : sesqUnitaryGroup B}
    (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    (hS : orderOf (QuotientGroup.mk S : sesqProjUnitary h B) = 2)
    (hXT : CFSG.Assembly.IsComponentOf X₂
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h B) T))))
    (hXS : CFSG.Assembly.IsComponentOf X₂
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h B) S))))
    (d : E) (hST : ∀ v, unitaryOp S (unitaryOp T v) = d • unitaryOp T (unitaryOp S v))
    (hne : (QuotientGroup.mk S : sesqProjUnitary h B) ≠ QuotientGroup.mk T) : False := by
  classical
  have hZc := sesqNormOneScalars_le_center h B
  have hsq : ∀ R : sesqUnitaryGroup B,
      orderOf (QuotientGroup.mk R : sesqProjUnitary h B) = 2 → R * R ∈ sesqNormOneScalars h B := by
    intro R hR
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hR, pow_orderOf_eq_one]
  have hφφ : ∀ R : sesqUnitaryGroup B, R * R ∈ center (sesqUnitaryGroup B) →
      ∀ g, MulAut.conj R (MulAut.conj R g) = g := by
    intro R hRR g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp hRR g
    calc R * (R * g * R⁻¹) * R⁻¹ = (R * R) * g * (R * R)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  have hφZT := map_conj_eq_of_le_center hZc T
  have hφZS := map_conj_eq_of_le_center hZc S
  rw [← onQuotient_conj T hφZT] at hXT
  rw [← onQuotient_conj S hφZS] at hXS
  obtain ⟨hYT, hYm, hYfixT⟩ := liftY_data (MulAut.conj T) hφZT
    (hφφ T (hZc (hsq T hT))) hXT
  obtain ⟨-, -, hYfixS⟩ := liftY_data (MulAut.conj S) hφZS (hφφ S (hZc (hsq S hS))) hXS
  rw [fixedSubgroup_conj] at hYT
  obtain ⟨P, hPT⟩ := su4_linear_paired h hp hn hB hBl hT hYT (liftHom X₂ hYm)
    (liftHom_surjective X₂ hYm) (liftHom_ker_le_center X₂ hYm) (liftHom_ker_le_scalars X₂ hYm) hs
  have h2 := two_ne_zero_of_odd h hp
  have hSY : ∀ y ∈ liftY X₂, ∀ v, unitaryOp S (unitaryOp y v) = unitaryOp y (unitaryOp S v) := by
    intro y hy v
    have h1 := hYfixS y hy
    have h2' : S * y = y * S := by
      have : S * y * S⁻¹ = y := h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h3 := congrArg (fun g : sesqUnitaryGroup B => unitaryOp g v) h2'
    exact h3
  rcases P.linear_cases h2 hSY d (by rw [hPT]; exact hST) (hsq S hS) with hS1 | hS2
  · have : (QuotientGroup.mk S : sesqProjUnitary h B) = 1 := (QuotientGroup.eq_one_iff S).mpr hS1
    rw [this, orderOf_one] at hS
    exact absurd hS (by norm_num)
  · rw [hPT] at hS2
    apply hne
    have h3 : (QuotientGroup.mk (S * T⁻¹) : sesqProjUnitary h B) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hS2
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h3
    exact h3

end CoreLinear

section CoreAnti

open CFSG.ComponentClassification.OddClassSelector (map_conj_eq_of_le_center onQuotient_conj)

theorem su4_core_anti [FiniteDimensional E V] (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    (hn : finrank E V = 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} [Finite (sesqUnitaryGroup B)]
    (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {X₂ : Subgroup (sesqProjUnitary h B)} (hs : SmallSource X₂)
    {T : sesqUnitaryGroup B}
    (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v)
    (hXT : CFSG.Assembly.IsComponentOf X₂
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h B) T))))
    (hXτ : CFSG.Assembly.IsComponentOf X₂ (fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B)))
    (d : E) (hTτ : ∀ v, unitaryOp T (τ₀ v) = d • τ₀ (unitaryOp T v)) : False := by
  classical
  have hZc := sesqNormOneScalars_le_center h B
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp (hZc hTT) g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  have hφZT := map_conj_eq_of_le_center hZc T
  rw [← onQuotient_conj T hφZT] at hXT
  obtain ⟨hYT, hYm, -⟩ := liftY_data (MulAut.conj T) hφZT hφφ hXT
  obtain ⟨hYτ, -, hYfixτ⟩ := liftY_data (antiConj h τ₀ hτ₀ hτ₀B)
    (map_scalars_unitaryConj h _ _ hτ₀B) (unitaryConj_unitaryConj h _ _ hτ₀B μ hμ) hXτ
  rw [fixedSubgroup_conj] at hYT
  obtain ⟨P, hPT⟩ := su4_linear_paired h hp hn hB hBl hT hYT (liftHom X₂ hYm)
    (liftHom_surjective X₂ hYm) (liftHom_ker_le_center X₂ hYm) (liftHom_ker_le_scalars X₂ hYm) hs
  have h2 := two_ne_zero_of_odd h hp
  have hτY : ∀ y ∈ liftY X₂, ∀ v, unitaryOp y (τ₀ v) = τ₀ (unitaryOp y v) := by
    intro y hy v
    exact (mem_fixed_unitaryConj h (antiEquiv h τ₀ hτ₀) _ hτ₀B y).mp (hYfixτ y hy) v
  have hμ' := P.antiunitary_neg h2 hB τ₀ hτ₀ hτ₀B (μ : E) hμ hτY d (by rw [hPT]; exact hTτ)
  have hμ1 : μ = -1 := Units.ext (by rw [hμ', Units.val_neg, Units.val_one])
  exact su_field_neg_false h hp (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ hμ1 hYτ (liftHom X₂ hYm)
    (liftHom_ker_le_center X₂ hYm) hs

end CoreAnti

end CFSG.GH74.GLS.IVK
