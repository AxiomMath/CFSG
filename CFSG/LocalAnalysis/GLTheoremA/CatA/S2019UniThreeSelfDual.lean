module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniThreeBlocks
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

private theorem eq_one_of_pow_three_eq_one {E : Type*} [Field E] [CharP E 3] {y : Eˣ} (hy : y ^ 3 = 1) :
    y = 1 := by
  have h3 : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  have hy' : (y : E) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have h : ((y : E) - 1) ^ 3 = 0 := by linear_combination hy' + (-(y : E) ^ 2 + (y : E)) * h3
  exact Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h))

section Heis

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}

@[expose] noncomputable def heis (Hf : W →ₛₗ[σ] W →ₗ[E] E) (f₁ u : W) (β : E) : W →ₗ[E] W :=
  LinearMap.id + (Hf f₁).smulRight u - (Hf u).smulRight f₁ + (β • Hf f₁).smulRight f₁

variable {Hf : W →ₛₗ[σ] W →ₗ[E] E} {f₁ : W}

theorem heis_apply (u : W) (β : E) (w : W) :
    heis Hf f₁ u β w = w + Hf f₁ w • u - Hf u w • f₁ + (β * Hf f₁ w) • f₁ := by
  simp only [heis, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]

theorem heis_zero_zero : heis Hf f₁ 0 0 = LinearMap.id := by
  refine LinearMap.ext fun w => ?_
  simp [heis_apply]

theorem heis_comp (h11 : Hf f₁ f₁ = 0) {u u' : W} (hu : Hf u f₁ = 0) (hu' : Hf f₁ u' = 0)
    (β β' : E) :
    heis Hf f₁ u β ∘ₗ heis Hf f₁ u' β' = heis Hf f₁ (u + u') (β + β' - Hf u u') := by
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.comp_apply, heis_apply, map_add, map_sub, map_smul, smul_eq_mul,
    LinearMap.add_apply, h11, hu, hu', mul_zero, add_zero, sub_zero]
  module

theorem heis_isometry (hHf : ∀ v w, σ (Hf v w) = Hf w v) (h11 : Hf f₁ f₁ = 0) {u : W}
    (hu : Hf f₁ u = 0) {β : E} (hβ : β + σ β + Hf u u = 0) (v w : W) :
    Hf (heis Hf f₁ u β v) (heis Hf f₁ u β w) = Hf v w := by
  have hu1 : Hf u f₁ = 0 := by rw [← hHf f₁ u, hu, map_zero]
  have e1 : Hf v u = σ (Hf u v) := (hHf u v).symm
  have e2 : Hf v f₁ = σ (Hf f₁ v) := (hHf f₁ v).symm
  simp only [heis_apply, map_add, map_sub, LinearMap.map_smulₛₗ₂, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h11, hu, hu1, map_mul, mul_zero,
    add_zero, sub_zero, e1, e2]
  linear_combination (σ (Hf f₁ v) * Hf f₁ w) * hβ

theorem heis_comp_heis_neg (hHf : ∀ v w, σ (Hf v w) = Hf w v) (h11 : Hf f₁ f₁ = 0) {u : W}
    (hu : Hf f₁ u = 0) {β : E} (hβ : β + σ β + Hf u u = 0) :
    heis Hf f₁ u β ∘ₗ heis Hf f₁ (-u) (σ β) = LinearMap.id := by
  have hu1 : Hf u f₁ = 0 := by rw [← hHf f₁ u, hu, map_zero]
  rw [heis_comp h11 hu1 (by rw [map_neg, hu, neg_zero]), add_neg_cancel, map_neg, sub_neg_eq_add,
    hβ, heis_zero_zero]

theorem heis_neg_comp_heis (hHf : ∀ v w, σ (Hf v w) = Hf w v) (h11 : Hf f₁ f₁ = 0) {u : W}
    (hu : Hf f₁ u = 0) {β : E} (hβ : β + σ β + Hf u u = 0) :
    heis Hf f₁ (-u) (σ β) ∘ₗ heis Hf f₁ u β = LinearMap.id := by
  have hu1 : Hf u f₁ = 0 := by rw [← hHf f₁ u, hu, map_zero]
  rw [heis_comp h11 (by rw [map_neg, LinearMap.neg_apply, hu1, neg_zero]) hu, neg_add_cancel,
    map_neg, LinearMap.neg_apply, sub_neg_eq_add, add_comm (σ β) β, hβ, heis_zero_zero]

theorem heis_pow_three [CharP E 3] (h11 : Hf f₁ f₁ = 0) {u : W} (hu : Hf u f₁ = 0)
    (hu' : Hf f₁ u = 0) (β : E) :
    heis Hf f₁ u β ∘ₗ (heis Hf f₁ u β ∘ₗ heis Hf f₁ u β) = LinearMap.id := by
  have h3 : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  rw [heis_comp h11 hu hu', heis_comp h11 hu (by rw [map_add, hu', add_zero])]
  have e1 : u + (u + u) = 0 := by
    rw [show u + (u + u) = (3 : E) • u by module, h3, zero_smul]
  have e2 : β + (β + β - Hf u u) - Hf u (u + u) = 0 := by
    rw [map_add]
    linear_combination (β - Hf u u) * h3
  rw [e1, e2, heis_zero_zero]

theorem heis_inj_right {z : W} (hz : Hf f₁ z ≠ 0) (hf₁ : f₁ ≠ 0) {u : W} {γ γ' : E}
    (h : heis Hf f₁ u γ = heis Hf f₁ u γ') : γ = γ' := by
  have e := LinearMap.congr_fun h z
  rw [heis_apply, heis_apply] at e
  exact mul_right_cancel₀ hz (smul_left_injective E hf₁ (add_left_cancel e))

theorem heis_inj_left (hHf : ∀ v w, σ (Hf v w) = Hf w v) {u₀ z : W} (hu₀ : Hf f₁ u₀ = 0)
    (hz1 : Hf f₁ z = 1) (hz0 : Hf u₀ z = 0) (hc₀ : Hf u₀ u₀ ≠ 0) {α α' β β' : E}
    (h : heis Hf f₁ (α • u₀) β = heis Hf f₁ (α' • u₀) β') : α = α' := by
  have hu₀1 : Hf u₀ f₁ = 0 := by rw [← hHf f₁ u₀, hu₀, map_zero]
  have e := congrArg (Hf u₀) (LinearMap.congr_fun h z)
  simp only [heis_apply, map_add, map_sub, map_smul, smul_eq_mul, LinearMap.map_smulₛₗ₂,
    LinearMap.sub_apply, LinearMap.smul_apply, hz1, hz0, hu₀1, mul_zero, zero_mul, one_mul,
    add_zero, zero_add, sub_zero] at e
  exact mul_right_cancel₀ hc₀ (by linear_combination e)

theorem heis_orth_smul {u₀ : W} (hu₀ : Hf f₁ u₀ = 0) (α : E) : Hf f₁ (α • u₀) = 0 := by
  rw [map_smul, hu₀, smul_zero]

theorem heis_orth_smul' (hHf : ∀ v w, σ (Hf v w) = Hf w v) {u₀ : W} (hu₀ : Hf f₁ u₀ = 0)
    (α : E) : Hf (α • u₀) f₁ = 0 := by
  rw [LinearMap.map_smulₛₗ₂, ← hHf f₁ u₀, hu₀, map_zero, smul_zero]

theorem heis_cond_smul {u₀ : W} {α β : E} (hc : β + σ β + σ α * α * Hf u₀ u₀ = 0) :
    β + σ β + Hf (α • u₀) (α • u₀) = 0 := by
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul]
  linear_combination hc

variable (Hf f₁) in
@[expose] def heisGroup (hHf : ∀ v w, σ (Hf v w) = Hf w v) (hσ : ∀ c, σ (σ c) = c)
    (h11 : Hf f₁ f₁ = 0) (u₀ : W) (hu₀ : Hf f₁ u₀ = 0) :
    Subgroup (LinearMap.GeneralLinearGroup E W) where
  carrier := {g | ∃ α β : E, β + σ β + σ α * α * Hf u₀ u₀ = 0 ∧
    (g : W →ₗ[E] W) = heis Hf f₁ (α • u₀) β}
  one_mem' := ⟨0, 0, by simp, by rw [zero_smul, heis_zero_zero]; rfl⟩
  mul_mem' {g g'} hg hg' := by
    obtain ⟨α, β, hc, hge⟩ := hg
    obtain ⟨α', β', hc', hge'⟩ := hg'
    refine ⟨α + α', β + β' - σ α * α' * Hf u₀ u₀, ?_, ?_⟩
    · have hc0 : σ (Hf u₀ u₀) = Hf u₀ u₀ := hHf u₀ u₀
      simp only [map_sub, map_add, map_mul, hσ, hc0]
      linear_combination hc + hc'
    · rw [Units.val_mul, hge, hge', Module.End.mul_eq_comp,
        heis_comp h11 (heis_orth_smul' hHf hu₀ α) (heis_orth_smul hu₀ α'), add_smul,
        LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
  inv_mem' {g} hg := by
    obtain ⟨α, β, hc, hge⟩ := hg
    refine ⟨-α, σ β, ?_, ?_⟩
    · rw [hσ, map_neg, neg_mul_neg]
      linear_combination hc
    · have h1 : (g : W →ₗ[E] W) * heis Hf f₁ (-(α • u₀)) (σ β) = 1 := by
        rw [hge, Module.End.mul_eq_comp,
          heis_comp_heis_neg hHf h11 (heis_orth_smul hu₀ α) (heis_cond_smul hc)]
        rfl
      rw [Units.inv_eq_of_mul_eq_one_right h1, neg_smul]

variable (Hf f₁) in
@[expose] noncomputable def heisUnit (hHf : ∀ v w, σ (Hf v w) = Hf w v) (h11 : Hf f₁ f₁ = 0)
    {u₀ : W} (hu₀ : Hf f₁ u₀ = 0) (α β : E) (hc : β + σ β + σ α * α * Hf u₀ u₀ = 0) :
    LinearMap.GeneralLinearGroup E W where
  val := heis Hf f₁ (α • u₀) β
  inv := heis Hf f₁ (-(α • u₀)) (σ β)
  val_inv := heis_comp_heis_neg hHf h11 (heis_orth_smul hu₀ α) (heis_cond_smul hc)
  inv_val := heis_neg_comp_heis hHf h11 (heis_orth_smul hu₀ α) (heis_cond_smul hc)

theorem coe_heisUnit (hHf : ∀ v w, σ (Hf v w) = Hf w v) (h11 : Hf f₁ f₁ = 0) {u₀ : W}
    (hu₀ : Hf f₁ u₀ = 0) (α β : E) (hc : β + σ β + σ α * α * Hf u₀ u₀ = 0) :
    (heisUnit Hf f₁ hHf h11 hu₀ α β hc : W →ₗ[E] W) = heis Hf f₁ (α • u₀) β := rfl

theorem heisUnit_mem (hHf : ∀ v w, σ (Hf v w) = Hf w v) (hσ : ∀ c, σ (σ c) = c)
    (h11 : Hf f₁ f₁ = 0) {u₀ : W} (hu₀ : Hf f₁ u₀ = 0) (α β : E)
    (hc : β + σ β + σ α * α * Hf u₀ u₀ = 0) :
    heisUnit Hf f₁ hHf h11 hu₀ α β hc ∈ heisGroup Hf f₁ hHf hσ h11 u₀ hu₀ :=
  ⟨α, β, hc, rfl⟩

theorem heisGroup_le_sesqUnitaryGroup (hHf : ∀ v w, σ (Hf v w) = Hf w v) (hσ : ∀ c, σ (σ c) = c)
    (h11 : Hf f₁ f₁ = 0) {u₀ : W} (hu₀ : Hf f₁ u₀ = 0) :
    heisGroup Hf f₁ hHf hσ h11 u₀ hu₀ ≤ sesqUnitaryGroup Hf := by
  rintro g ⟨α, β, hc, hge⟩
  rw [mem_sesqUnitaryGroup, hge]
  exact heis_isometry hHf h11 (heis_orth_smul hu₀ α) (heis_cond_smul hc)

theorem pow_three_of_mem_heisGroup [CharP E 3] (hHf : ∀ v w, σ (Hf v w) = Hf w v)
    (hσ : ∀ c, σ (σ c) = c) (h11 : Hf f₁ f₁ = 0) {u₀ : W} (hu₀ : Hf f₁ u₀ = 0)
    {g : LinearMap.GeneralLinearGroup E W} (hg : g ∈ heisGroup Hf f₁ hHf hσ h11 u₀ hu₀) :
    g ^ 3 = 1 := by
  obtain ⟨α, β, -, hge⟩ := hg
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hge, pow_three, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    heis_pow_three h11 (heis_orth_smul' hHf hu₀ α) (heis_orth_smul hu₀ α) β]
  rfl

theorem exists_heis_zero_of_central [CharP E 3] (hHf : ∀ v w, σ (Hf v w) = Hf w v)
    (hσ : ∀ c, σ (σ c) = c) (h11 : Hf f₁ f₁ = 0) {u₀ : W} (hu₀ : Hf f₁ u₀ = 0)
    (hc₀ : Hf u₀ u₀ ≠ 0 ∨ u₀ = 0) {ω : E} (hω : σ ω ≠ ω) {z : W} (hz : Hf f₁ z ≠ 0)
    (hf₁ : f₁ ≠ 0) {g : LinearMap.GeneralLinearGroup E W}
    (hg : g ∈ heisGroup Hf f₁ hHf hσ h11 u₀ hu₀)
    (hcent : ∀ g' ∈ heisGroup Hf f₁ hHf hσ h11 u₀ hu₀, g * g' = g' * g) :
    ∃ β : E, (g : W →ₗ[E] W) = heis Hf f₁ 0 β := by
  obtain ⟨α, β, -, hge⟩ := hg
  refine ⟨β, ?_⟩
  rw [hge]
  rcases hc₀ with hc₀ | h0
  swap
  · rw [h0, smul_zero]
  suffices hα : α = 0 by rw [hα, zero_smul]
  have h3 : (3 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 3
  have hc0 : σ (Hf u₀ u₀) = Hf u₀ u₀ := hHf u₀ u₀
  have key : ∀ α' β' (hc' : β' + σ β' + σ α' * α' * Hf u₀ u₀ = 0),
      σ α * α' = σ α' * α := by
    intro α' β' hc'
    have e := congrArg (fun k : LinearMap.GeneralLinearGroup E W => (k : W →ₗ[E] W))
      (hcent _ (heisUnit_mem hHf hσ h11 hu₀ α' β' hc'))
    simp only [Units.val_mul, hge, coe_heisUnit, Module.End.mul_eq_comp] at e
    rw [heis_comp h11 (heis_orth_smul' hHf hu₀ α) (heis_orth_smul hu₀ α'),
      heis_comp h11 (heis_orth_smul' hHf hu₀ α') (heis_orth_smul hu₀ α),
      add_comm (α' • u₀)] at e
    have e2 := heis_inj_right hz hf₁ e
    simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul] at e2
    have e3 : (σ α * α' - σ α' * α) * Hf u₀ u₀ = 0 := by linear_combination -e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right hc₀)
  have k1 := key 1 (Hf u₀ u₀) (by
    rw [hc0, map_one, one_mul, one_mul]
    linear_combination (Hf u₀ u₀) * h3)
  have k2 := key ω (σ ω * ω * Hf u₀ u₀) (by
    rw [map_mul, map_mul, hσ, hc0]
    linear_combination (σ ω * ω * Hf u₀ u₀) * h3)
  rw [mul_one, map_one, one_mul] at k1
  rw [k1] at k2
  have h4 : α * (ω - σ ω) = 0 := by linear_combination k2
  exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 (Ne.symm hω))

end Heis

section SelfDual

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem sq_sub_one_eq_zero_of_supported (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ supportedUnitary B x {(a : K[X])})
    (N : primaryComponent (x : Module.End K V) (a : K[X]) →
      primaryComponent (x : Module.End K V) (a : K[X])) (hNN : ∀ w, N (N w) = 0)
    (hga : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
      (g : Module.End K V) (w : V) = (w : V) +
        ((N w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) :
    ((g : Module.End K V) - 1) ^ 2 = 0 := by
  refine ext_primaryComponent hsq fun c hc v hv => ?_
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  by_cases hca : c = a
  · subst hca
    set w : primaryComponent (x : Module.End K V) (a : K[X]) := ⟨v, hv⟩
    have e1 := hga w
    have e2 := hga (N w)
    change _ = (w : V) + _ at e1
    rw [e1, add_sub_cancel_left, e2, hNN, Submodule.coe_zero, add_zero, sub_self]
  · have e1 : (g : Module.End K V) v = v :=
      hg.2 c hc (fun h => hca (Set.mem_singleton_iff.1 h)) v hv
    rw [e1, sub_self, map_zero, sub_self]

theorem exists_pGroup_specialBlock_selfDual (H : UnitaryPrimaryData hK.bar B x) (hℓ : ℓ = 3)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    (ha : IsGoodBlock hK x a) (hfacts : SpecialBlockFacts B x a) :
    ∃ P : Subgroup (LinearMap.GeneralLinearGroup K V), P ≤ specialBlock B x (a : K[X]) ∧
      IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ g ∈ specialBlock B x (a : K[X]), u * g = g * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) →
        (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 := by
  classical
  subst hℓ
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  haveI := hK.finite
  haveI : CharP K 3 := hK.charP
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot (a : K[X])) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 3
  obtain ⟨hE, -, -, Hf, hHf, -, -, ⟨e, he⟩, φ, hφ, -⟩ :=
    (selfDualPrimaryBlock H a hself).unitaryForm
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W →ₗ[AdjoinRoot (a : K[X])] W) := Finite.of_injective _ LinearMap.coe_injective
  haveI : Finite (LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) :=
    Finite.of_injective _ Units.val_injective
  have hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  have hHf' : ∀ v w, hE.bar (Hf v w) = Hf w v := hHf.eq
  have hσ : ∀ c, hE.bar (hE.bar c) = c := hE.bar_bar
  let i0 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨0, by omega⟩
  let i1 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  obtain ⟨μ, hμ⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one hE
  set f₁ : W := e i0 + μ • e i1 with hf₁
  have h11 : Hf f₁ f₁ = 0 := by
    have e1 : μ * hE.bar μ = -1 := hμ
    simp only [hf₁, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, he,
      if_neg h01, if_neg h01.symm, ↓reduceIte, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    linear_combination e1
  have hf₁0 : Hf f₁ (e i0) = 1 := by
    simp only [hf₁, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, he, ↓reduceIte,
      if_neg h01.symm, smul_eq_mul, mul_zero, add_zero]
  have hf₁ne : f₁ ≠ 0 := fun h0 => by
    rw [h0, map_zero, LinearMap.zero_apply] at hf₁0
    exact zero_ne_one hf₁0
  obtain ⟨ω, hω⟩ := hE.exists_bar_ne
  obtain ⟨u₀, hu₀, hc₀, hcard⟩ : ∃ u₀ : W, ∃ hu₀ : Hf f₁ u₀ = 0, (Hf u₀ u₀ ≠ 0 ∨ u₀ = 0) ∧
      9 ≤ Nat.card (heisGroup Hf f₁ hHf' hσ h11 u₀ hu₀) := by
    by_cases hm3 : 3 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
    ·
      let i2 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨2, hm3⟩
      have h02 : i0 ≠ i2 := fun h => by simpa [i0, i2] using congrArg Fin.val h
      have h12 : i1 ≠ i2 := fun h => by simpa [i1, i2] using congrArg Fin.val h
      have hu₀ : Hf f₁ (e i2) = 0 := by
        simp only [hf₁, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, he, if_neg h02,
          if_neg h12, smul_eq_mul, mul_zero, add_zero]
      have hc1 : Hf (e i2) (e i2) = 1 := by rw [he, if_pos rfl]
      have hz0 : Hf (e i2) (e i0) = 0 := by rw [he, if_neg h02.symm]
      refine ⟨e i2, hu₀, Or.inl (by rw [hc1]; exact one_ne_zero), ?_⟩
      have h3 : (3 : AdjoinRoot (a : K[X])) = 0 := by exact_mod_cast CharP.cast_eq_zero _ 3
      have hcond : ∀ α : AdjoinRoot (a : K[X]),
          hE.bar α * α * Hf (e i2) (e i2) + hE.bar (hE.bar α * α * Hf (e i2) (e i2)) +
            hE.bar α * α * Hf (e i2) (e i2) = 0 := by
        intro α
        rw [hc1, map_mul, map_mul, hσ, map_one]
        linear_combination (hE.bar α * α) * h3
      let ι : AdjoinRoot (a : K[X]) → heisGroup Hf f₁ hHf' hσ h11 (e i2) hu₀ := fun α =>
        ⟨heisUnit Hf f₁ hHf' h11 hu₀ α _ (hcond α), heisUnit_mem hHf' hσ h11 hu₀ α _ (hcond α)⟩
      have hι : Function.Injective ι := by
        intro α α' hαα
        have e1 := congrArg (fun k : heisGroup Hf f₁ hHf' hσ h11 (e i2) hu₀ =>
          ((k : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) : W →ₗ[AdjoinRoot (a : K[X])] W)) hαα
        simp only [ι, coe_heisUnit] at e1
        exact heis_inj_left hHf' hu₀ hf₁0 hz0 (by rw [hc1]; exact one_ne_zero) e1
      have hEc : 9 ≤ Nat.card (AdjoinRoot (a : K[X])) := by
        rw [hE.card]
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (2 * (f * (a : K[X]).natDegree)) :=
            Nat.pow_le_pow_right (by norm_num) (by have := hE.one_le; omega)
      exact hEc.trans (Nat.card_le_card_of_injective ι hι)
    ·
      have hm2 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
      refine ⟨0, map_zero _, Or.inr rfl, ?_⟩
      have hcond : ∀ β : hE.traceZero, (β : AdjoinRoot (a : K[X])) + hE.bar β +
          hE.bar 0 * 0 * Hf 0 0 = 0 := by
        intro β
        have := β.2
        rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace] at this
        rw [map_zero, zero_mul, zero_mul, add_zero]
        exact this
      let ι : hE.traceZero → heisGroup Hf f₁ hHf' hσ h11 0 (map_zero _) := fun β =>
        ⟨heisUnit Hf f₁ hHf' h11 (map_zero _) 0 β (hcond β),
          heisUnit_mem hHf' hσ h11 (map_zero _) 0 β (hcond β)⟩
      have hι : Function.Injective ι := by
        intro β β' hββ
        have e1 := congrArg (fun k : heisGroup Hf f₁ hHf' hσ h11 0 (map_zero _) =>
          ((k : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) : W →ₗ[AdjoinRoot (a : K[X])] W)) hββ
        simp only [ι, coe_heisUnit] at e1
        exact Subtype.ext (heis_inj_right (z := e i0) (by rw [hf₁0]; exact one_ne_zero) hf₁ne e1)
      have hQ : 9 ≤ 3 ^ (f * (a : K[X]).natDegree) := by
        have h := ha.2 hself
        rw [hm2] at h
        have hd := hE.one_le
        by_contra hlt
        have h1 : f * (a : K[X]).natDegree = 1 := by
          by_contra hne
          have h2 : 3 ^ 2 ≤ 3 ^ (f * (a : K[X]).natDegree) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [h1, pow_one] at h
        exact h (by simp)
      have h1 := Nat.card_le_card_of_injective ι hι
      rw [hE.card_traceZero] at h1
      exact hQ.trans h1
  set S := heisGroup Hf f₁ hHf' hσ h11 u₀ hu₀ with hS
  have hle : S ≤ sesqUnitaryGroup Hf := heisGroup_le_sesqUnitaryGroup hHf' hσ h11 hu₀
  let Ψ : S →* LinearMap.GeneralLinearGroup K V :=
    (supportedUnitary B x {(a : K[X])}).subtype.comp
      (φ.symm.toMonoidHom.comp (Subgroup.inclusion hle))
  have hΨS : ∀ τ, Ψ τ ∈ supportedUnitary B x {(a : K[X])} :=
    fun τ => (φ.symm (Subgroup.inclusion hle τ)).2
  have hΨinj : Function.Injective Ψ := by
    intro τ τ' h
    apply Subgroup.inclusion_injective hle
    apply φ.symm.injective
    exact Subtype.ext h
  have hΨa : ∀ τ (w : W), ((Ψ τ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (w : V) =
      ((((τ : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) : W →ₗ[AdjoinRoot (a : K[X])] W) w : W) : V) := by
    intro τ w
    have h1 := hφ (φ.symm (Subgroup.inclusion hle τ)) (w : V) w.2
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} :=
    orbitFactor_eq_supportedUnitary_of_selfDual hself
  have hpow : ∀ τ : S, τ ^ 3 = 1 := fun τ => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_three_of_mem_heisGroup hHf' hσ h11 hu₀ τ.2)
  refine ⟨Ψ.range, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨τ, rfl⟩
    have hgS := hΨS τ
    have hgc : Ψ τ ∈ gl_centralizer x := supportedUnitary_le_gl_centralizer _ hgS
    rw [mem_specialBlock]
    refine ⟨by rw [hsupp]; exact hgS, hgc, ?_⟩
    have hres : blockRestrict x (a : K[X]) ⟨Ψ τ, hgc⟩ =
        (τ : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) := by
      apply blockGL_ext
      intro v hv
      rw [blockApply_blockRestrict]
      exact hΨa τ ⟨v, hv⟩
    apply eq_one_of_pow_three_eq_one
    rw [blockDetHom, MonoidHom.comp_apply, hres, ← map_pow,
      pow_three_of_mem_heisGroup hHf' hσ h11 hu₀ τ.2, map_one]
  ·
    intro y
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨τ, hτ⟩ := y.2
    rw [pow_one, Subgroup.coe_pow, ← hτ, ← map_pow, hpow, map_one]
    rfl
  ·
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv]
    exact hcard
  ·
    rintro _ ⟨τ, rfl⟩ hcent
    obtain ⟨c, hc⟩ := hfacts.scalar (Ψ τ) (hΨS τ).1 fun _ g hg => hcent g hg
    have hfix : ((τ : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) : W →ₗ[AdjoinRoot (a : K[X])] W) f₁ =
        f₁ := by
      obtain ⟨α, β, -, hτe⟩ := τ.2
      rw [hτe, heis_apply, h11, heis_orth_smul' hHf' hu₀ α, zero_smul, zero_smul, mul_zero,
        zero_smul, add_zero, sub_zero, add_zero]
    have hc1 : c = 1 := by
      have e1 := hc f₁
      rw [hΨa τ f₁, hfix] at e1
      have e2 : c • f₁ = (1 : AdjoinRoot (a : K[X])) • f₁ := by
        rw [one_smul]
        exact (Subtype.ext e1).symm
      exact smul_left_injective _ hf₁ne e2
    apply eq_one_of_forall_apply_eq H.squarefree
    intro b hb v hv
    by_cases hba : b = (a : K[X])
    · subst hba
      have e1 := hc ⟨v, hv⟩
      rw [hc1, one_smul] at e1
      exact e1
    · exact (hΨS τ).2 b hb (fun h => hba (Set.mem_singleton_iff.1 h)) v hv
  ·
    rintro _ ⟨τ, rfl⟩ hcent
    have hcentS : ∀ g' ∈ S, (τ : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) * g' =
        g' * (τ : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) W) := by
      intro g' hg'
      have h1 := hcent (Ψ ⟨g', hg'⟩) ⟨⟨g', hg'⟩, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hΨinj h1)
    obtain ⟨β, hβ⟩ := exists_heis_zero_of_central hHf' hσ h11 hu₀ hc₀ hω (z := e i0)
      (by rw [hf₁0]; exact one_ne_zero) hf₁ne τ.2 hcentS
    refine sq_sub_one_eq_zero_of_supported H.squarefree a (hΨS τ)
      (fun w => (β * Hf f₁ w) • f₁) (fun w => ?_) (fun w => ?_)
    · simp only [map_smul, h11, smul_eq_mul, mul_zero, zero_smul]
    · rw [hΨa, hβ, heis_apply, smul_zero, add_zero, map_zero, LinearMap.zero_apply, zero_smul,
        sub_zero, Submodule.coe_add]

theorem exists_pGroup_specialBlock_three (H : UnitaryPrimaryData hK.bar B x) (hℓ : ℓ = 3)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    (hfacts : SpecialBlockFacts B x a) :
    ∃ P : Subgroup (LinearMap.GeneralLinearGroup K V), P ≤ specialBlock B x (a : K[X]) ∧
      IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ g ∈ specialBlock B x (a : K[X]), u * g = g * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) →
        (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact exists_pGroup_specialBlock_selfDual H hℓ a hself ha hfacts
  · subst hℓ
    haveI : CharP K 3 := hK.charP
    have hq : 2 ≤ 3 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK.one_le)
    obtain ⟨P, h1, h2, h3, h4, h5⟩ :=
      exists_pGroup_specialBlock_paired H a (Ne.symm hself) ha.1 hq hfacts
    exact ⟨P, h1, h2, h3, h4, fun u hu _ => h5 u hu⟩

end SelfDual

end CFSG.LocalAnalysis.GLTheoremA.S2019
