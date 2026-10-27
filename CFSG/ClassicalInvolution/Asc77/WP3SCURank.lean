module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Module
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups Matrix

section SL

variable {F : Type} [Field F]

theorem rank_eq_four_of_central_pair_sl (h2 : (2 : F) ≠ 0) {n : ℕ} {hn : 2 ≤ n}
    {R₁ R₂ : Subgroup SL(n, F)} (h₁ : R₁ ∈ longRootSet (K := F) hn)
    (h₂ : R₂ ∈ longRootSet (K := F) hn) (hne : R₁ ≠ R₂) {r₁ r₂ : SL(n, F)} (hr₁ : r₁ ∈ R₁)
    (hrc₁ : ∀ s ∈ R₁, r₁ * s = s * r₁) (hr₁1 : r₁ ≠ 1) (hr₂ : r₂ ∈ R₂)
    (hrc₂ : ∀ s ∈ R₂, r₂ * s = s * r₂) (hr₂1 : r₂ ≠ 1)
    (hcen : r₁ * r₂ ∈ Subgroup.center SL(n, F)) : n = 4 := by
  obtain ⟨i₁, hi₁⟩ := h₁
  obtain ⟨i₂, hi₂⟩ := h₂
  have e₁ : r₁ = i₁ := (CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center
    h2 (hi₁.isClassicalSL2 h2) hr₁ hrc₁).resolve_left hr₁1
  have e₂ : r₂ = i₂ := (CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center
    h2 (hi₂.isClassicalSL2 h2) hr₂ hrc₂).resolve_left hr₂1
  subst e₁ e₂
  obtain ⟨μ, -, hμ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hM₁ : (r₁ : Matrix (Fin n) (Fin n) F) * r₁ = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hi₁.mul_self, Matrix.SpecialLinearGroup.coe_one]
  have hM₂ : (r₂ : Matrix (Fin n) (Fin n) F) * r₂ = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hi₂.mul_self, Matrix.SpecialLinearGroup.coe_one]
  have hprod : (r₁ : Matrix (Fin n) (Fin n) F) * r₂ = μ • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← hμ]
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hM : (r₂ : Matrix (Fin n) (Fin n) F) = μ • (r₁ : Matrix (Fin n) (Fin n) F) := by
    calc (r₂ : Matrix (Fin n) (Fin n) F)
        = (r₁ * r₁ : Matrix (Fin n) (Fin n) F) * r₂ := by rw [hM₁, Matrix.one_mul]
      _ = (r₁ : Matrix (Fin n) (Fin n) F) * ((r₁ : Matrix (Fin n) (Fin n) F) * r₂) := by
          rw [Matrix.mul_assoc]
      _ = μ • (r₁ : Matrix (Fin n) (Fin n) F) := by
          rw [hprod, Matrix.mul_smul, Matrix.mul_one]
  have hμ2 : μ * μ = 1 := by
    have h1 : (r₂ : Matrix (Fin n) (Fin n) F) * r₂ = (μ * μ) • (1 : Matrix (Fin n) (Fin n) F) := by
      conv_lhs => rw [hM]
      rw [Matrix.smul_mul, Matrix.mul_smul, hM₁, smul_smul]
    rw [hM₂] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3.symm
  rcases mul_self_eq_one_iff.mp hμ2 with h | h
  · exfalso
    apply hne
    have : r₂ = r₁ := by
      apply Subtype.ext
      rw [hM, h, one_smul]
    rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, this]
  · have hsp : minusSpace r₂ = fixSpace r₁ := by
      ext v
      rw [mem_minusSpace, mem_fixSpace, hM, h, neg_smul, one_smul, Matrix.neg_mulVec]
      exact neg_inj
    have hc := Submodule.finrank_add_eq_of_isCompl (hi₁.isCompl h2)
    rw [hi₁.finrank_minusSpace h2, Module.finrank_fin_fun] at hc
    have hd : finrank F (minusSpace r₂) = 2 := hi₂.finrank_minusSpace h2
    rw [hsp] at hd
    omega

end SL

section SU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem rank_eq_four_of_central_pair_su (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hn3 : 3 ≤ n) {hn : 2 ≤ n} {R₁ R₂ : Subgroup (Su K p f n)}
    (h₁ : R₁ ∈ longRootSetU (K := K) (p := p) (f := f) hn)
    (h₂ : R₂ ∈ longRootSetU (K := K) (p := p) (f := f) hn) (hne : R₁ ≠ R₂)
    {r₁ r₂ : Su K p f n} (hr₁ : r₁ ∈ R₁) (hrc₁ : ∀ s ∈ R₁, r₁ * s = s * r₁) (hr₁1 : r₁ ≠ 1)
    (hr₂ : r₂ ∈ R₂) (hrc₂ : ∀ s ∈ R₂, r₂ * s = s * r₂) (hr₂1 : r₂ ≠ 1)
    (hcen : r₁ * r₂ ∈ Subgroup.center (Su K p f n)) : n = 4 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have hU : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  obtain ⟨i₁, hi₁⟩ := h₁
  obtain ⟨i₂, hi₂⟩ := h₂
  have e₁ : r₁ = i₁ := (CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center
    h2F (hi₁.isClassicalSL2 hK hp) hr₁ hrc₁).resolve_left hr₁1
  have e₂ : r₂ = i₂ := (CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center
    h2F (hi₂.isClassicalSL2 hK hp) hr₂ hrc₂).resolve_left hr₂1
  subst e₁ e₂
  obtain ⟨μ, hμ⟩ : ∃ μ : K, suMat (r₁ * r₂) = μ • (1 : Matrix (Fin n) (Fin n) K) := by
    refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.eq_smul_one_of_commute hU hp hn3
      (suMat (r₁ * r₂)) fun y hy => ?_
    have hy' : y ∈ SUid (unitaryInvolution K p f) n := by
      rw [SUid_eq_statedSU hK]
      exact hy
    have := Subgroup.mem_center_iff.mp hcen ⟨y, hy'⟩
    have h3 := congrArg (fun x : Su K p f n => suMat x) this
    simp only [suMat_mul] at h3
    exact h3.symm
  have hM₁ : suMat r₁ * suMat r₁ = 1 := hi₁.coe_mul_self
  have hM₂ : suMat r₂ * suMat r₂ = 1 := hi₂.coe_mul_self
  have hprod : suMat r₁ * suMat r₂ = μ • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [← suMat_mul, hμ]
  have hM : suMat r₂ = μ • suMat r₁ := by
    calc suMat r₂ = (suMat r₁ * suMat r₁) * suMat r₂ := by rw [hM₁, Matrix.one_mul]
      _ = suMat r₁ * (suMat r₁ * suMat r₂) := by rw [Matrix.mul_assoc]
      _ = μ • suMat r₁ := by rw [hprod, Matrix.mul_smul, Matrix.mul_one]
  have hμ2 : μ * μ = 1 := by
    have h1 : suMat r₂ * suMat r₂ = (μ * μ) • (1 : Matrix (Fin n) (Fin n) K) := by
      conv_lhs => rw [hM]
      rw [Matrix.smul_mul, Matrix.mul_smul, hM₁, smul_smul]
    rw [hM₂] at h1
    have h3 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3.symm
  rcases mul_self_eq_one_iff.mp hμ2 with h | h
  · exfalso
    apply hne
    have : r₂ = r₁ := by
      apply suMat_injective
      rw [hM, h, one_smul]
    rw [hi₁.eq_longRootGroupSU h2, hi₂.eq_longRootGroupSU h2, this]
  · have hsp : minusSpaceSU r₂ = fixSpaceSU r₁ := by
      ext v
      rw [mem_minusSpaceSU, mem_fixSpaceSU, hM, h, neg_smul, one_smul, Matrix.neg_mulVec]
      exact neg_inj
    have hc := Submodule.finrank_add_eq_of_isCompl (hi₁.isCompl hp)
    rw [hi₁.finrank_minusSpaceSU h2, Module.finrank_fin_fun] at hc
    have hd : finrank K (minusSpaceSU r₂) = 2 := hi₂.finrank_minusSpaceSU h2
    rw [hsp] at hd
    omega

end SU

section Model

variable {p e : ℕ} [Fact p.Prime]

@[expose] def CentralPairRank (t : StatedLieTag) (n p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible t n p e →
    ∀ {R₁ R₂ : Subgroup (modelUniv t n p e Fact.out).K},
      R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D →
      R₂ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D → R₁ ≠ R₂ →
      ∀ {r₁ r₂ : (modelUniv t n p e Fact.out).K}, r₁ ∈ R₁ → (∀ s ∈ R₁, r₁ * s = s * r₁) →
        r₁ ≠ 1 → r₂ ∈ R₂ → (∀ s ∈ R₂, r₂ * s = s * r₂) → r₂ ≠ 1 →
        r₁ * r₂ ∈ Subgroup.center (modelUniv t n p e Fact.out).K → n = 4

theorem centralPairRank_psl (hp2 : p ≠ 2) (n : ℕ) : CentralPairRank .PSL n p e := by
  intro hadm R₁ R₂ hR₁ hR₂ hne r₁ r₂ hr₁ hrc₁ hr₁1 hr₂ hrc₂ hr₂1 hcen
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have heq : fundamentalSubgroups .PSL (modelUniv .PSL (m + 1) p e Fact.out).D =
      longRootSet (K := GaloisField p e) hn :=
    Set.Subset.antisymm (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset hn)
      (CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl hn)
  exact rank_eq_four_of_central_pair_sl
    (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) (hn := hn)
    ((Set.ext_iff.mp heq R₁).mp hR₁) ((Set.ext_iff.mp heq R₂).mp hR₂) hne hr₁ hrc₁ hr₁1 hr₂ hrc₂
    hr₂1 hcen

theorem centralPairRank_psu (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (n : ℕ) :
    CentralPairRank .PSU n p e := by
  intro hadm R₁ R₂ hR₁ hR₂ hne r₁ r₂ hr₁ hrc₁ hr₁1 hr₂ hrc₂ hr₂1 hcen
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e he
  have hn3 : 3 ≤ n := hadm.2.2.1
  refine rank_eq_four_of_central_pair_su hK hp2 h5 hn3 (hn := by omega) (R₁ := R₁.map φ.toMonoidHom)
    (R₂ := R₂.map φ.toMonoidHom) ((hφ R₁).1 hR₁) ((hφ R₂).1 hR₂) ?_ (r₁ := φ r₁) (r₂ := φ r₂)
    ⟨r₁, hr₁, rfl⟩ ?_ (by simpa using hr₁1) ⟨r₂, hr₂, rfl⟩ ?_ (by simpa using hr₂1) ?_
  · exact fun h => hne (Subgroup.map_injective φ.injective h)
  · rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hrc₁ s hs]
  · rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hrc₂ s hs]
  · rw [← map_mul]
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hcen g']

end Model

end CFSG.ClassicalInvolution.Asc77
