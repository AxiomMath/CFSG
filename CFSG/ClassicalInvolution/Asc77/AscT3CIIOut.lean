module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIBur

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups commutatorElement

section PSL2

variable {K : Type*} [Field K]

theorem pgl2FieldAut_mem_range (σ : K ≃+* K) {g : PGL2 K}
    (hg : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    pgl2FieldAut K σ g ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨x, rfl⟩ := hg
  exact ⟨psl2FieldAut K σ x, psl2FieldAut_toPGL σ x⟩

theorem pgl2FieldAut_mem_range_iff (σ : K ≃+* K) {g : PGL2 K} :
    pgl2FieldAut K σ g ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ↔
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  refine ⟨fun h => ?_, pgl2FieldAut_mem_range σ⟩
  have h1 := pgl2FieldAut_mem_range σ⁻¹ h
  have e : (pgl2FieldAut K σ⁻¹) ((pgl2FieldAut K σ) g) = g := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rwa [e] at h1

theorem isInnerAut_commutator_psl2_all [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (α β : MulAut (PSL2 K)) : IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  obtain ⟨g₁, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
  obtain ⟨h₁, τ, rfl⟩ := exists_pglAction_mul_psl2FieldAut β
  have hst : psl2FieldAut K σ * psl2FieldAut K τ = psl2FieldAut K τ * psl2FieldAut K σ := by
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  have e1 := psl2FieldAut_mul_pglAction_mul_inv σ h₁
  have e3 := psl2FieldAut_mul_pglAction_mul_inv τ g₁
  have hDB : psl2FieldAut K τ * (psl2FieldAut K σ)⁻¹ = (psl2FieldAut K σ)⁻¹ * psl2FieldAut K τ := by
    calc psl2FieldAut K τ * (psl2FieldAut K σ)⁻¹
        = (psl2FieldAut K σ)⁻¹ * (psl2FieldAut K σ * psl2FieldAut K τ) * (psl2FieldAut K σ)⁻¹ := by
          group
      _ = (psl2FieldAut K σ)⁻¹ * (psl2FieldAut K τ * psl2FieldAut K σ) * (psl2FieldAut K σ)⁻¹ := by
          rw [hst]
      _ = (psl2FieldAut K σ)⁻¹ * psl2FieldAut K τ := by group
  have key : (pglAction K g₁ * psl2FieldAut K σ) * (pglAction K h₁ * psl2FieldAut K τ) *
      (pglAction K g₁ * psl2FieldAut K σ)⁻¹ * (pglAction K h₁ * psl2FieldAut K τ)⁻¹ =
      pglAction K (g₁ * pgl2FieldAut K σ h₁ * (pgl2FieldAut K τ g₁)⁻¹ * h₁⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← e1, ← e3]
    calc (pglAction K g₁ * psl2FieldAut K σ) * (pglAction K h₁ * psl2FieldAut K τ) *
          (pglAction K g₁ * psl2FieldAut K σ)⁻¹ * (pglAction K h₁ * psl2FieldAut K τ)⁻¹
        = pglAction K g₁ * psl2FieldAut K σ * pglAction K h₁ * (psl2FieldAut K τ *
            (psl2FieldAut K σ)⁻¹) * (pglAction K g₁)⁻¹ * (psl2FieldAut K τ)⁻¹ *
            (pglAction K h₁)⁻¹ := by group
      _ = pglAction K g₁ * psl2FieldAut K σ * pglAction K h₁ * ((psl2FieldAut K σ)⁻¹ *
            psl2FieldAut K τ) * (pglAction K g₁)⁻¹ * (psl2FieldAut K τ)⁻¹ *
            (pglAction K h₁)⁻¹ := by rw [hDB]
      _ = _ := by group
  have hH : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index = 2 :=
    pgl2_psl2Range_index_eq_two K hK
  have hmem : g₁ * pgl2FieldAut K σ h₁ * (pgl2FieldAut K τ g₁)⁻¹ * h₁⁻¹ ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    simp only [Subgroup.mul_mem_iff_of_index_two hH, Subgroup.inv_mem_iff,
      pgl2FieldAut_mem_range_iff]
    tauto
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  rw [key, ← hx, pglAction_toPGL]

end PSL2

section SL2

variable {F : Type*} [Field F] [Finite F]

theorem isInnerAut_commutator_of_equiv_sl2 (hK : IsOddPrimePower (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {P : Type*} [Group P] (e : P ≃* SL(2, F)) (α β : MulAut P) :
    IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  have hperf : Group.IsPerfect P := CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e
  refine isInnerAut_of_isInnerAut_centerDescend ?_
  let e' : P ⧸ Subgroup.center P ≃* PSL2 F :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rw [← isInnerAut_congr e']
  simp only [map_mul, map_inv]
  exact isInnerAut_commutator_psl2_all hK _ _

end SL2

section Group

variable {G : Type} [Group G] {F : Type*} [Field F] [Finite F]

theorem outComm_of_equiv_sl2 (hK : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {K : Subgroup G} (e : K ≃* SL(2, F)) : OutComm K := by
  intro x hx y hy
  have hxy : ⁅x, y⁆ ∈ Subgroup.normalizer (K : Set G) := by
    have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  obtain ⟨k₀, hk₀⟩ := isInnerAut_commutator_of_equiv_sl2 hK h4 e
    (K.normalizerMonoidHom ⟨x, hx⟩) (K.normalizerMonoidHom ⟨y, hy⟩)
  refine ⟨k₀, k₀.2, fun g hg => ?_⟩
  have h1 : K.normalizerMonoidHom ⟨⁅x, y⁆, hxy⟩ = K.normalizerMonoidHom ⟨x, hx⟩ *
      K.normalizerMonoidHom ⟨y, hy⟩ * (K.normalizerMonoidHom ⟨x, hx⟩)⁻¹ *
      (K.normalizerMonoidHom ⟨y, hy⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  have h2 := congrArg (fun φ : MulAut K => ((φ ⟨g, hg⟩ : K) : G)) (h1.trans hk₀.symm)
  simpa using h2

end Group

section Galois

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime]

theorem outComm_of_equiv_galoisField (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ≃* SL(2, GaloisField p f)) : OutComm K := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  refine outComm_of_equiv_sl2 ⟨p, f, Fact.out, ?_, Nat.one_le_iff_ne_zero.mpr hf, hcard⟩
    (by rw [hcard]; exact (by norm_num : 4 ≤ 5).trans hq) e
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
  · exact absurd h hp
  · exact h

end Galois

end CFSG.ClassicalInvolution.Asc77.T3CII
