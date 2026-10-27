module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.RankThree.Chevalley

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem exists_g2_twisted_data (hK : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ g z : ModGL .G2 K₂, g ∈ adjointGroup .G2 K₂ ∧ z ∈ adjointGroup .G2 K₂ ∧
      z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ ∧
      (∃ hz : z ∈ monomialSubgroup .G2 K₂,
        ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v) ∧
      conjEntrywiseImage K g =
        adjointGroup .G2 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) ∧
      (∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hodd₂ : Odd (Nat.card K₂) := by
    rw [hq2]
    exact hK.pow
  have h2 : (2 : K₂) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_natCard hodd₂)
  obtain ⟨hinv, ω, hω, hσω⟩ := exists_frobenius_eq_neg hdeg σ hσ
  have hPn := quadraticTorusP_mul_nSL σ hω h2 hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (quadraticTorusP ω hω h2)⁻¹ *
      rootSL2 .G2 K₂ g2v (quadraticTorusP ω hω h2)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ :=
    ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a (twoMulUnit ω hω h2) *
      rootWeylSL2 .G2 K₂ g2v (twoMulUnit ω hω h2) := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hzC : z ∈ adjointGroup .G2 K₂ := by
    rw [hzeq]
    exact mul_mem (hρC _ _) (hρC _ _)
  exact ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, conjEntrywiseImage_eq_fixed σ hσ hg hzdef,
    twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
