module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.RankThree.PartOne.RF4.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenG2 CFSG.RankThree.PartOne.RF4

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

structure QPlusModel (K : Type) [Field K] [Finite K] {K₂ : Type} [Field K₂] [Algebra K K₂]
    (σ : K₂ ≃+* K₂) where
  P : SL2 K₂
  g : ModGL .G2 K₂
  z : ModGL .G2 K₂
  hgdef : g = rootSL2 .G2 K₂ g2a P⁻¹ * rootSL2 .G2 K₂ g2v P⁻¹
  hg : g ∈ adjointGroup .G2 K₂
  hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹
  hz : z ∈ monomialSubgroup .G2 K₂
  hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v

namespace QPlusModel

variable {σ : K₂ ≃+* K₂}

abbrev gamma (M : QPlusModel K σ) : Subgroup (ModGL .G2 K₂) := conjEntrywiseImage K M.g

theorem nonempty_of_odd (hK : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) : Nonempty (QPlusModel K σ) := by
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
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a (twoMulUnit ω hω h2) *
      rootWeylSL2 .G2 K₂ g2v (twoMulUnit ω hω h2) := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  exact ⟨⟨_, g, z, hgdef, hg, hzdef, hzN, hw⟩⟩

theorem nonempty_of_charTwo [CharP K 2] (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) : Nonempty (QPlusModel K σ) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  obtain ⟨hinv, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
  have hPn := evenQuadraticP_mul_nSL σ hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (evenQuadraticP ω)⁻¹ *
      rootSL2 .G2 K₂ g2v (evenQuadraticP ω)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a 1 * rootWeylSL2 .G2 K₂ g2v 1 := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  exact ⟨⟨_, g, z, hgdef, hg, hzdef, hzN, hw⟩⟩

variable [Finite K₂]

theorem gamma_eq_fixed (M : QPlusModel K σ) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    M.gamma = adjointGroup .G2 K₂ ⊓
      (twistedEntrywise M.z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) :=
  conjEntrywiseImage_eq_fixed σ hσ M.hg M.hzdef

theorem torus_inf_gamma (M : QPlusModel K σ) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    torusGroup .G2 K₂ ⊓ M.gamma = torusTorsion K₂ (Nat.card K + 1) :=
  torusGroup_inf_eq_torusTorsion M.hz M.hw (σ : K₂ →+* K₂) hσ (M.gamma_eq_fixed hσ)

end QPlusModel

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
