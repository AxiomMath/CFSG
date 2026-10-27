module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.Asc77.WP3SCURank
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3
public import CFSG.ClassicalInvolution.Asc77.WP3ChainVToral
public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGU
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.ModelFacts.CF3All
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Module
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups Matrix

section Pure

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem rank_eq_four_of_central_pair_su3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hf : 1 ≤ f) {n : ℕ} (hn3 : 3 ≤ n) {hn : 2 ≤ n} {R₁ R₂ : Subgroup (Su K p f n)}
    (h₁ : R₁ ∈ longRootSetU (K := K) (p := p) (f := f) hn)
    (h₂ : R₂ ∈ longRootSetU (K := K) (p := p) (f := f) hn) (hne : R₁ ≠ R₂)
    {r₁ r₂ : Su K p f n} (hr₁ : r₁ ∈ R₁) (hrc₁ : ∀ s ∈ R₁, r₁ * s = s * r₁) (hr₁1 : r₁ ≠ 1)
    (hr₂ : r₂ ∈ R₂) (hrc₂ : ∀ s ∈ R₂, r₂ * s = s * r₂) (hr₂1 : r₂ ≠ 1)
    (hcen : r₁ * r₂ ∈ Subgroup.center (Su K p f n)) : n = 4 := by
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

end Pure

section Model


theorem compGen3Twin_psu {k : ℕ} (hadm : StatedLieAdmissible .PSU k 3 1) (hk : k ≠ 4) :
    CompGen3Twin (compModel 3 1 .PSU k) := by
  have hk3 : 3 ≤ k := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  have hfin : Finite (compModel 3 1 .PSU k).G :=
    finite_modelUniv (t := .PSU) hp2 Nat.prime_three trivial hadm
  obtain ⟨e, hfund⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  exfalso
  obtain ⟨e₁⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU) trivial hadm
    (by decide) (by decide) hR₁
  obtain ⟨e₂⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU) trivial hadm
    (by decide) (by decide) hR₂
  have hcen := hker (twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂)
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hcen' : sl2Inv e₁ * sl2Inv e₂ ∈ Subgroup.center (compModel 3 1 .PSU k).G := by
    have h1 : sl2Inv e₁ * sl2Inv e₂ = sl2Inv e₂ * (sl2Inv e₁)⁻¹ := by
      have hc := Subgroup.mem_center_iff.mp hcen (sl2Inv e₁)
      have hinv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ := inv_eq_of_mul_eq_one_right hsq₁
      rw [hinv] at hc ⊢
      have h3 := congrArg (fun x => x * sl2Inv e₁) hc
      simp only [mul_assoc, hsq₁, mul_one] at h3
      exact h3
    rw [h1]
    exact hcen
  have hne' : R₁.map e.toMonoidHom ≠ R₂.map e.toMonoidHom := by
    intro h
    exact hne (by rw [Subgroup.map_injective e.injective h])
  have hcenE : e (sl2Inv e₁) * e (sl2Inv e₂) ∈
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 k) := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen' x]
  have hres := rank_eq_four_of_central_pair_su3 (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hK
    hp2 le_rfl hk3 ((hfund R₁).mp hR₁) ((hfund R₂).mp hR₂) hne'
    (r₁ := e (sl2Inv e₁)) (r₂ := e (sl2Inv e₂))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₁))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₁) * e s₀ = e s₀ * e (sl2Inv e₁)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₁ hs₀])
    (fun h => sl2Inv_ne_one hodd e₁ (e.injective (by rw [h, map_one])))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₂) * e s₀ = e s₀ * e (sl2Inv e₂)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₂ hs₀])
    (fun h => sl2Inv_ne_one hodd e₂ (e.injective (by rw [h, map_one])))
    hcenE
  exact hk hres

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
