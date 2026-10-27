module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Scalar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Eichler

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem three_eq_zero_of_card_eq_three [Finite K] (hK3 : Nat.card K = 3) : (3 : K) = 0 := by
  have := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK3] at h
  exact_mod_cast h

theorem two_ne_zero_of_card_eq_three [Finite K] (hK3 : Nat.card K = 3) : (2 : K) ≠ 0 := by
  intro h
  have h3 := three_eq_zero_of_card_eq_three hK3
  exact one_ne_zero (show (1 : K) = 0 by linear_combination h3 - h)

theorem eichler_pow_three [Finite K] (hK3 : Nat.card K = 3) {u w : V} (hw : polar Q u w = 0) :
    eichler Q u w * eichler Q u w * eichler Q u w = 1 := by
  have hww : polar Q u (w + w) = 0 := by rw [polar_add_right, hw, add_zero]
  rw [eichler_mul hw hw, eichler_mul hww hw]
  have h3 : w + w + w = (3 : K) • w := by module
  rw [h3, three_eq_zero_of_card_eq_three hK3, zero_smul, eichler_zero_right]

@[expose] def eichlerImages (Q : QuadraticForm K V) (W : Submodule K V) : Set (ProjOrthDerived Q) :=
  {s | ∃ (P : HypPair Q) (_ : P.e ∈ W) (_ : P.f ∈ W) (w : V) (_ : w ∈ W ⊓ P.perp)
      (hE : eichler Q P.e w ∈ orthDerived Q), s = QuotientGroup.mk ⟨eichler Q P.e w, hE⟩}

end Eichler

section Fixed

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem commute_of_fixed_order_three (hK3 : Nat.card K = 3) (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (α : MulAut (ProjOrthDerived Q))
    (hα : ∀ g g' : orthDerived Q,
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        α (QuotientGroup.mk g) = QuotientGroup.mk g')
    {E : V ≃ₗ[K] V} (hE : E ∈ orthDerived Q) (hE3 : E * E * E = 1) {v₀ : V} (hv₀ : v₀ ≠ 0)
    (hfix : α (QuotientGroup.mk ⟨E, hE⟩) = QuotientGroup.mk ⟨E, hE⟩) :
    ∀ v, F (E v) = E (F v) := by
  have hg' : semilinConj F σ hF E ∈ orthDerived Q := semilinConj_mem_orthDerived F σ hF μ hFQ hE
  have h1 := hα ⟨E, hE⟩ ⟨semilinConj F σ hF E, hg'⟩ (fun v => rfl)
  rw [hfix] at h1
  have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
  obtain ⟨c, hc⟩ := mem_scalars.mp h2
  have hg'c : ∀ v, semilinConj F σ hF E v = c • E v := by
    intro v
    have h3 := hc v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] at h3
    have h4 := congrArg E h3
    rw [LinearEquiv.apply_inv_apply', map_smul] at h4
    exact h4
  have hG3 : semilinConj F σ hF E * semilinConj F σ hF E * semilinConj F σ hF E = 1 := by
    rw [← map_mul, ← map_mul, hE3, map_one]
  have hE3v : E (E (E v₀)) = v₀ := by
    have := LinearEquiv.congr_fun hE3 v₀
    simpa using this
  have hc3 : c ^ 3 = 1 := by
    have h := LinearEquiv.congr_fun hG3 v₀
    have h1v : (1 : V ≃ₗ[K] V) v₀ = v₀ := rfl
    simp only [LinearEquiv.mul_apply, hg'c, map_smul, smul_smul, h1v, hE3v] at h
    have h' : (c * (c * c) - 1) • v₀ = 0 := by rw [sub_smul, one_smul, h, sub_self]
    have := (smul_eq_zero.mp h').resolve_right hv₀
    linear_combination this
  have hc1 : c = 1 := by
    have := Fintype.ofFinite K
    have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK3]
    have h := FiniteField.pow_card c
    rw [hcard, hc3] at h
    exact h.symm
  intro v
  have h := hg'c (F v)
  rw [hc1, one_smul] at h
  have h2 : semilinConj F σ hF E (F v) = F (E v) := by
    rw [semilinConj_apply, AddEquiv.symm_apply_apply]
  rw [h2] at h
  exact h

end Fixed

section Blocks

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem polarNondegOn_suppPerp {W : Submodule K V} (hQ : (polarBilin Q).Nondegenerate)
    (hW : PolarNondegOn Q W) : PolarNondegOn Q (suppPerp Q W) := by
  intro x hx hxy
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  have hsup : W ⊔ suppPerp Q W = ⊤ := (isCompl_suppPerp hW).sup_eq_top
  have hv : v ∈ W ⊔ suppPerp Q W := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  rw [polar_add_right Q x w w', hxy w' hw', add_zero, polar_comm Q x w, mem_suppPerp.mp hx w hw]

omit [FiniteDimensional K V] in
theorem commute_of_scalar_blocks {U₁ U₂ : Submodule K V} (hc : IsCompl U₁ U₂) (h E : V ≃ₗ[K] V)
    (a b : K) (ha : ∀ w ∈ U₁, h w = a • w) (hb : ∀ w ∈ U₂, h w = b • w)
    (hE1 : ∀ w ∈ U₁, E w ∈ U₁) (hE2 : ∀ w ∈ U₂, E w = w) (v : V) : h (E v) = E (h v) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp
    (by rw [hc.sup_eq_top]; trivial : v ∈ U₁ ⊔ U₂)
  have e1 : h (E (u + u')) = a • E u + b • u' := by
    rw [map_add E, hE2 u' hu', map_add h, ha _ (hE1 u hu), hb u' hu']
  have e2 : E (h (u + u')) = a • E u + b • u' := by
    rw [map_add h, ha u hu, hb u' hu', map_add E, map_smul E, map_smul E, hE2 u' hu']
  rw [e1, e2]

end Blocks

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
