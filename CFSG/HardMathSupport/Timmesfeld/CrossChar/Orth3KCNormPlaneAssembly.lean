module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCLocalComponents
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
section Component
variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}
theorem exists_special_component3 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hpne : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K) (Dg : Subgroup (MulAut
        (ProjOrthDerived Q)))
    (hDg : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ Dg)
    (x : orthDerived Q) (hxp : orderOf x = p) {E : Type*} [Field E] [Algebra K E]
    (D : QuadData K E) {μ₁ μ₂ : E} (hμ₁0 : μ₁ ≠ 0) (hμ₁1 : μ₁ ≠ 1) (hbar : D.bar μ₁ = μ₁⁻¹)
    (hroot₂ : aeval μ₂ (minpoly K μ₁) = 0) {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁}
    {φ₂ : E →ₗ[K] U₂} (hN : NormPlanes D Q U₁ U₂ φ₁ φ₂)
    (hx₁ : ∀ z, (x : V ≃ₗ[K] V) (φ₁ z : V) = (φ₁ (μ₁ * z) : V))
    (hx₂ : ∀ z, (x : V ≃ₗ[K] V) (φ₂ z : V) = (φ₂ (μ₂ * z) : V)) {G : Type*} [Group G]
    (hG : Group.IsPerfect G) (ι : G →* (V ≃ₗ[K] V))
    (hιO : ∀ g, ι g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hιx : ∀ g, ι g * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * ι g)
    (hιfix : ∀ g, ∀ w ∈ orthPerp Q (U₁ ⊔ U₂), ι g w = w) :
    ∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧ h = reciprocalPolynomial h ∧
      2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ∧
      ι.range ≤ specialBlock Q (x : V ≃ₗ[K] V) h ∧
      specialBlock Q (x : V ≃ₗ[K] V) h ≤
        orthDerived Q ⊓ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) ∧
      specialBlock Q (x : V ≃ₗ[K] V) h ≠ ⊥ ∧
      IsComponent (((componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf
        (Dg ⊓ Subgroup.centralizer
          ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
            Set (MulAut (ProjOrthDerived Q))))) ∧
      (componentImage Q (x : V ≃ₗ[K] V) h).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        inSubgroup CFSG.layer (Dg ⊓ Subgroup.centralizer
          ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
            Set (MulAut (ProjOrthDerived Q)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2le := hp.two_le
  have : Module.Finite K E := Module.Finite.of_basis D.basis
  have hxO : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hint : IsIntegral K μ₁ := Algebra.IsIntegral.isIntegral μ₁
  have hirr : Irreducible (minpoly K μ₁) := minpoly.irreducible hint
  have hmon : (minpoly K μ₁).Monic := minpoly.monic hint
  have hroot₁ : aeval μ₁ (minpoly K μ₁) = 0 := minpoly.aeval K μ₁
  have hR : U₁ ⊔ U₂ ≤ primaryComponent (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) :=
    sup_le_primaryComponent hN.φ₁_surjective hN.φ₂_surjective hx₁ hx₂ hroot₁ hroot₂
  have hR4 : finrank K ↥(U₁ ⊔ U₂) = 4 := hN.finrank_sup
  have hne : primaryComponent (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) ≠ ⊥ := by
    intro h0
    rw [h0, le_bot_iff] at hR
    rw [hR, finrank_bot] at hR4
    omega
  have hmem : minpoly K μ₁ ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot hirr hmon hne
  have hself : reciprocalPolynomial (minpoly K μ₁) = minpoly K μ₁ :=
    reciprocalPolynomial_minpoly_eq D.bar hμ₁0 hbar
  have hdeg : (minpoly K μ₁).natDegree ≤ 2 := by
    have : (minpoly K μ₁).natDegree ≤ finrank K E := minpoly.natDegree_le μ₁
    rwa [D.finrank_eq_two] at this
  have : Fact (Irreducible (minpoly K μ₁)) := ⟨hirr⟩
  have hmult : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (minpoly K μ₁) :=
    two_le_primaryMultiplicity hdeg hR hR4
  have hne1 : minpoly K μ₁ ≠ X - 1 := by
    intro h1
    have := hroot₁
    rw [h1, map_sub, aeval_X, map_one, sub_eq_zero] at this
    exact hμ₁1 this
  have hι : ι.range ≤ specialBlock Q (x : V ≃ₗ[K] V) (minpoly K μ₁) :=
    range_le_specialBlock hxO hmem hR hG ι hιO hιx hιfix
  obtain ⟨-, -, hZcard, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have ha : orderOf (QuotientGroup.mk x : ProjOrthDerived Q) = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      have hxZ : x ∈ (scalars K V).subgroupOf (orthDerived Q) := (QuotientGroup.eq_one_iff x).mp h1
      have h2 := orderOf_dvd_natCard (⟨x, hxZ⟩ : ↥((scalars K V).subgroupOf (orthDerived Q)))
      have h3 : orderOf (⟨x, hxZ⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) = p := by
        rw [← hxp]
        exact Subgroup.orderOf_mk x hxZ
      rw [h3] at h2
      have := Nat.le_of_dvd (by
        have : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
        exact this) h2
      have := hp.two_le
      omega
  obtain ⟨⟨Rep, hRep⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue3 hQ hT hp hpne hK4 hpl Dg hDg
      (QuotientGroup.mk x) ha x rfl hxp
  obtain ⟨-, -, -, -, -, hspecial, -, -⟩ := hmain Rep hRep
  have hhRep : minpoly K μ₁ ∈ Rep := mem_of_isOrbitRepresentatives_of_selfdual hxO hRep hmem hself
  obtain ⟨hsb, -, hcne, -, hcent, -, hcomp⟩ := hspecial _ hhRep hne1 hmult
  refine ⟨minpoly K μ₁, hmem, hne1, hself.symm, hmult, hι, ?_, ?_, hcomp, ?_⟩
  · intro g hg
    refine Subgroup.mem_inf.mpr ⟨hsb hg, ?_⟩
    exact (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _
      (specialBlock_le_supportedBlock _ hg))).2
  · intro hbot
    apply hcne
    rw [componentImage, hbot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  ·
    set C : Subgroup (MulAut (ProjOrthDerived Q)) := Dg ⊓ Subgroup.centralizer
      ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (MulAut (ProjOrthDerived Q))) with hC
    have hXC : (componentImage Q (x : V ≃ₗ[K] V) (minpoly K μ₁)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤ C := by
      rintro _ ⟨t, ht, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hDg ⟨t, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hcent ht)
      rw [← map_mul, ← map_mul, this]
    have hlayer : (((componentImage Q (x : V ≃ₗ[K] V) (minpoly K μ₁)).map
        (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))).subgroupOf C) ≤
        CFSG.layer ↥C := le_sSup hcomp
    have hmap := Subgroup.map_mono (f := C.subtype) hlayer
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXC] at hmap
    exact hmap
end Component
end CFSG.RankThree.PartOne.KCOrthogonal