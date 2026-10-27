module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QPlusModel
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoCent

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem QPlusModel.z_mem_adjointGroup (M : QPlusModel K σ) : M.z ∈ adjointGroup .G2 K₂ := by
  rw [M.hzdef]
  have h := (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K₂ σ ⟨M.g, M.hg⟩).2
  rw [CFSG.RankThree.PartTwo.KFacts.coe_g2FieldHom] at h
  exact mul_mem M.hg (inv_mem h)

theorem QPlusModel.exists_conj_plane_to_torsion (M : QPlusModel K σ)
    (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) (E : Subgroup ↥(adjointGroup .G2 K))
    [hE : CFSG.IsElementaryAbelian 3 E] (hcard : Nat.card E = 3 ^ 2) :
    ∃ y : ModGL .G2 K₂, y ∈ M.gamma ∧
      (E.map (twistEmb M.g)).map (MulAut.conj y).toMonoidHom = torusTorsion K₂ 3 := by
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    rw [hq2]
    have : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_left h3 _
  have hcent : ∀ x ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, x * v = v * x) →
      x ∈ torusGroup .G2 K₂ := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ : K₂ˣ, orderOf ζ = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcard : 3 ∣ Nat.card K₂ˣ := by
        rw [Nat.card_units]
        exact h3₂
      exact exists_prime_orderOf_dvd_card' 3 hcard
    have hprim : IsPrimitiveRoot (ζ : K₂) 3 := by
      have := IsPrimitiveRoot.orderOf ζ
      rw [hζ] at this
      exact IsPrimitiveRoot.coe_units_iff.2 this
    have hω : (ζ : K₂) ^ 2 + ζ + 1 = 0 := by
      have := hprim.geom_sum_eq_zero (by norm_num)
      simp [Finset.sum_range_succ] at this
      linear_combination this
    have hω1 : (ζ : K₂) ≠ 1 := hprim.ne_one (by norm_num)
    exact fun x hx hc => centralizer_torusTorsion_three_le (ζ : K₂) hω hω1 x hx hc
  have hFY : ∀ x ∈ adjointGroup .G2 K₂,
      twistedEntrywise M.z (σ : K₂ →+* K₂) x ∈ adjointGroup .G2 K₂ := fun x hx =>
    twistedEntrywise_mem_adjointGroup M.z_mem_adjointGroup hx
  obtain ⟨y', hy'C, hy'F, hy'⟩ := exists_fixed_conj_planeToTorsion (K := K) h3 hq2
    (twistedEntrywise M.z (σ : K₂ →+* K₂)) hFY
    (twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂))
      (fun c => by
        have h2 : σ * σ = 1 := by
          obtain ⟨-, hord, -⟩ := quadratic_frobenius hdeg σ hσ
          rw [← pow_two, ← hord]
          exact pow_orderOf_eq_one σ
        simpa using RingEquiv.ext_iff.1 h2 c) M.hzdef)
    (fun c => twistedEntrywise_rootDiagUnit M.hz M.hw (σ : K₂ →+* K₂) hσ c) hcent
    (M.gamma_eq_fixed hσ) E hcard
  refine ⟨y', ?_, hy'⟩
  rw [M.gamma_eq_fixed hσ]
  exact ⟨hy'C, hy'F⟩

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
