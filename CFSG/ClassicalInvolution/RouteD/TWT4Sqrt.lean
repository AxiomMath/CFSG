module

public import CFSG.ClassicalInvolution.RouteD.TWT4Inv
public import CFSG.ClassicalInvolution.Asc77.SU4Struct
public import CFSG.ClassicalInvolution.Asc77.SU4Hyp

public section

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.ClassicalInvolution.RouteD.SU4Pattern (BD BD_eq BD_mul det_BD conjTr_BD BD_one)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (suMat_blockEmb_zero
  suMat_blockEmb_two suMat_rootInvSU_inv_four twin_std_u)
open CFSG.ClassicalInvolution.RouteD.SCRSu4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD.TwinY

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Block

variable {K : Type} [Field K]

theorem BD_add (X Y X' Y' : Matrix (Fin 2) (Fin 2) K) :
    BD X Y + BD X' Y' = BD (X + X') (Y + Y') := by
  rw [BD_eq, BD_eq, BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem BD_smul (c : K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    c • BD X Y = BD (c • X) (c • Y) := by
  rw [BD_eq, BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem det_one_add_smul (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) (htr : M.trace = 0)
    (s : K) (hs : s * s = 1) : (1 + s • M).det = 2 := by
  rw [Matrix.det_fin_two] at hdet ⊢
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag] at htr
  simp
  linear_combination (s * s) * hdet + s * htr + hs

theorem sqrtBlock_sq (M : Matrix (Fin 2) (Fin 2) K) (hM2 : M * M = -1) {ε h s : K}
    (hε2 : ε * ε = -1) (hh : 2 * h = 1) (hs : s * s = 1) :
    ((h * (1 + s * ε)) • (1 + s • M)) * ((h * (1 + s * ε)) • (1 + s • M)) = ε • M := by
  have h1 : (1 + s • M) * (1 + s • M) = (2 * s) • M := by
    have : (1 + s • M) * (1 + s • M) = 1 + s • M + s • M + (s * s) • (M * M) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
        smul_smul, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [this, hM2, hs, two_mul, add_smul]
    simp only [one_smul]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, smul_smul]
  congr 1
  linear_combination (2 * s ^ 3 * h ^ 2) * hε2 + (-2 * s * h ^ 2 + 4 * h ^ 2 * ε) * hs +
    (ε * (2 * h + 1)) * hh


theorem sqrtBlock_comm (M : Matrix (Fin 2) (Fin 2) K) (a s : K) :
    (a • (1 + s • M)) * M = M * (a • (1 + s • M)) :=
  (((Commute.one_left M).add_left ((Commute.refl M).smul_left s)).smul_left a).eq

theorem sqrtBlock_mul_aux (M : Matrix (Fin 2) (Fin 2) K) (hM2 : M * M = -1) (ε s : K) :
    (1 + s • M) * (1 + ε • M) = (1 - s * ε) • (1 : Matrix (Fin 2) (Fin 2) K) + (ε + s) • M := by
  have : (1 + s • M) * (1 + ε • M) = 1 + ε • M + s • M + (s * ε) • (M * M) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [mul_comm ε s]
    abel
  rw [this, hM2, sub_smul, add_smul]
  simp only [one_smul, smul_neg]
  abel

theorem sqrtBlock_fix (M : Matrix (Fin 2) (Fin 2) K) (hM2 : M * M = -1) {ε h s : K}
    (hε2 : ε * ε = -1) (hh : 2 * h = 1) (hs : s * s = 1) :
    ((h * (1 + s * ε)) • (1 + s • M)) * (1 + ε • M) = 1 + ε • M := by
  rw [Matrix.smul_mul, sqrtBlock_mul_aux M hM2, smul_add, smul_smul, smul_smul]
  have e1 : h * (1 + s * ε) * (1 - s * ε) = 1 := by
    linear_combination hh + (-h * ε ^ 2) * hs + (-h) * hε2
  have e2 : h * (1 + s * ε) * (ε + s) = ε := by
    linear_combination ε * hh + (h * s) * hε2 + (h * ε) * hs
  rw [e1, e2, one_smul]

theorem det_sqrtBlock (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) (htr : M.trace = 0)
    {ε h s : K} (hε2 : ε * ε = -1) (hh : 2 * h = 1) (hs : s * s = 1) :
    ((h * (1 + s * ε)) • (1 + s • M)).det = s * ε := by
  rw [Matrix.det_smul, det_one_add_smul M hdet htr s hs]
  simp only [Fintype.card_fin]
  linear_combination (2 * h ^ 2 * ε ^ 2) * hs + (2 * h ^ 2) * hε2 + (s * ε * (2 * h + 1)) * hh

theorem sqrtBlock_unitary (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K) (hM2 : M * M = -1)
    (hMc : conjTr σ M = -M) {ε h s : K} (hε2 : ε * ε = -1) (hσε : σ ε = -ε) (hσh : σ h = h)
    (hσs : σ s = s) (hh : 2 * h = 1) (hs : s * s = 1) :
    conjTr σ ((h * (1 + s * ε)) • (1 + s • M)) * ((h * (1 + s * ε)) • (1 + s • M)) = 1 := by
  rw [conjTr_smul', conjTr_add, conjTr_one, conjTr_smul', hMc, map_mul, map_add, map_one,
    map_mul, hσh, hσs, hσε, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : (1 + s • -M) * (1 + s • M) = (2 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have : (1 + s • -M) * (1 + s • M) = 1 - (s * s) • (M * M) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
        smul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, smul_neg]
      abel
    rw [this, hM2, hs, two_smul]
    simp only [one_smul, smul_neg]
    abel
  rw [h1, smul_smul]
  have : h * (1 + s * -ε) * (h * (1 + s * ε)) * 2 = 1 := by
    linear_combination (2 * h + 1) * hh + (-2 * h ^ 2 * ε ^ 2) * hs + (-2 * h ^ 2) * hε2
  rw [this, one_smul]

end Block

section Sqrt

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_sqrt_block (hp : p ≠ 2) {A A' : Su K p f 2} (hA : suMat A * suMat A = -1)
    (hA' : suMat A' * suMat A' = -1) {ε : K} (hε2 : ε * ε = -1)
    (hσε : unitaryInvolution K p f ε = -ε) :
    ∃ c : Su K p f 4,
      suMat c * (ε • BD (suMat A) (suMat A')) = (ε • BD (suMat A) (suMat A')) * suMat c ∧
      suMat c * (1 + ε • BD (suMat A) (suMat A')) = 1 + ε • BD (suMat A) (suMat A') ∧
      suMat c * suMat c = ε • BD (suMat A) (suMat A') ∧
      suMat c * BD (suMat A) 1 = BD (suMat A) 1 * suMat c ∧
      suMat c * BD 1 (suMat A') = BD 1 (suMat A') * suMat c := by
  set σ := unitaryInvolution K p f with hσ
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  set h : K := (2 : K)⁻¹ with hhdef
  have hh : 2 * h = 1 := mul_inv_cancel₀ h2
  have hσh : σ h = h := by
    rw [hhdef, map_inv₀]
    congr 1
    exact map_ofNat σ 2
  have h11 : (1 : K) * 1 = 1 := one_mul 1
  have hm11 : (-1 : K) * -1 = 1 := by ring
  have hσ1 : σ (1 : K) = 1 := map_one σ
  have hσm1 : σ (-1 : K) = -1 := by rw [map_neg, map_one]
  have hMc := CFSG.ClassicalInvolution.RouteD.SCRSu4.conjTr_eq_neg_of_sq A hA
  have hMc' := CFSG.ClassicalInvolution.RouteD.SCRSu4.conjTr_eq_neg_of_sq A' hA'
  have hdetA := det_suMat A
  have hdetA' := det_suMat A'
  have htrA := trace_eq_zero_of_sq A hA
  have htrA' := trace_eq_zero_of_sq A' hA'
  set B₁ : Matrix (Fin 2) (Fin 2) K := (h * (1 + 1 * ε)) • (1 + (1 : K) • suMat A) with hB₁
  set B₂ : Matrix (Fin 2) (Fin 2) K := (h * (1 + (-1) * ε)) • (1 + (-1 : K) • suMat A') with hB₂
  have hdet : (BD B₁ B₂).det = 1 := by
    rw [det_BD, hB₁, hB₂, det_sqrtBlock _ hdetA htrA hε2 hh h11,
      det_sqrtBlock _ hdetA' htrA' hε2 hh hm11]
    linear_combination -hε2
  have hunit : conjTr σ (BD B₁ B₂) * BD B₁ B₂ = 1 := by
    rw [conjTr_BD, BD_mul, hB₁, hB₂, sqrtBlock_unitary σ _ hA hMc hε2 hσε hσh hσ1 hh h11,
      sqrtBlock_unitary σ _ hA' hMc' hε2 hσε hσh hσm1 hh hm11, BD_one]
  refine ⟨mkSU K p f (BD B₁ B₂) hdet hunit, ?_, ?_, ?_, ?_, ?_⟩
  · rw [suMat_mkSU, Matrix.mul_smul, Matrix.smul_mul, BD_mul, BD_mul, hB₁, hB₂,
      sqrtBlock_comm, sqrtBlock_comm]
  · rw [suMat_mkSU, ← BD_one, BD_smul, BD_add, BD_mul, hB₁, hB₂,
      sqrtBlock_fix _ hA hε2 hh h11, sqrtBlock_fix _ hA' hε2 hh hm11]
  · rw [suMat_mkSU, BD_mul, hB₁, hB₂, sqrtBlock_sq _ hA hε2 hh h11, sqrtBlock_sq _ hA' hε2 hh hm11,
      BD_smul]
  · rw [suMat_mkSU, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul, hB₁, sqrtBlock_comm]
  · rw [suMat_mkSU, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul, hB₂, sqrtBlock_comm]

end Sqrt

section BlockData

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_twin_block_data (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {a a' : Su K p f 4} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∃ (g : Su K p f 4) (A A' : Su K p f 2),
      a = g * blockEmb K p f 4 2 0 (by norm_num) A * g⁻¹ ∧
      a' = g * blockEmb K p f 4 2 2 (by norm_num) A' * g⁻¹ ∧
      suMat A * suMat A = -1 ∧ suMat A' * suMat A' = -1 := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hx2 : x * x = 1 := sl2_mul_self_eq_one_of_center (hi.isClassicalSL2 hK hp) hxR hxc
  have hx'2 : x' * x' = 1 := sl2_mul_self_eq_one_of_center (hi'.isClassicalSL2 hK hp) hx'R' hx'c
  have hc0 : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).inv_mem hsame
    simpa using this
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp ⟨i, hi⟩ ⟨i', hi'⟩ hne hxR hx2 hx1 hx'R' hx'2
    hx'1 hc0
  have hxg' : x = g * xU K p f * g⁻¹ := hxg
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := (Subgroup.center (Su K p f 4)).mul_mem hsq' hc0
    simpa [mul_assoc] using this
  have hA₁ : blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 0 (by norm_num) A *
        (xU K p f)⁻¹) * g⁻¹ = a * a * x⁻¹ := by
      rw [← hae, hA, hxg']
      group
    rw [e]
    exact hsq
  have hA₂ : blockEmb K p f 4 2 2 (by norm_num) A' * blockEmb K p f 4 2 2 (by norm_num) A' *
      (xU K p f)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (blockEmb K p f 4 2 2 (by norm_num) A' * blockEmb K p f 4 2 2 (by norm_num) A' *
        (xU K p f)⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', hA', hxg']
      group
    rw [e]
    exact hsq''
  have hAA := sq_neg_one_of_center_zero hK hA₁
  have hAA' := sq_neg_one_of_center_two hK hA₂
  refine ⟨g, A, A', ?_, ?_, hAA, hAA'⟩
  · rw [hA, hae]
  · rw [hA', hae']

end BlockData

section SqrtInv

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_blockEmb_zero_eq_BD (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 0 (by norm_num) A) = BD (suMat A) 1 := by
  rw [suMat_blockEmb_zero, BD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem suMat_blockEmb_two_eq_BD (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 2 (by norm_num) A) = BD 1 (suMat A) := by
  rw [suMat_blockEmb_two, BD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_sqrt_jEl (hp : p ≠ 2) {g : Su K p f 4} {A A' : Su K p f 2} {a a' : Su K p f 4}
    (ha : a = g * blockEmb K p f 4 2 0 (by norm_num) A * g⁻¹)
    (ha' : a' = g * blockEmb K p f 4 2 2 (by norm_num) A' * g⁻¹)
    (hA : suMat A * suMat A = -1) (hA' : suMat A' * suMat A' = -1) (ε : K) (hε2 : ε * ε = -1)
    (hσε : unitaryInvolution K p f ε = -ε) :
    ∃ c ∈ longRootGroupSU K p f (suMat (jEl (a * a') ε hε2 hσε)),
      c * c = jEl (a * a') ε hε2 hσε ∧ c * a = a * c ∧ c * a' = a' * c := by
  obtain ⟨c₀, h1, h2, h3, h4, h5⟩ := exists_sqrt_block hp hA hA' hε2 hσε
  have hu : a * a' = g * (blockEmb K p f 4 2 0 (by norm_num) A *
      blockEmb K p f 4 2 2 (by norm_num) A') * g⁻¹ := by
    rw [ha, ha']
    group
  have hsu : suMat (jEl (a * a') ε hε2 hσε) =
      suMat g * (ε • BD (suMat A) (suMat A')) * suMat g⁻¹ := by
    rw [suMat_jEl, hu, suMat_mul, suMat_mul, suMat_mul, suMat_blockEmb_zero_eq_BD,
      suMat_blockEmb_two_eq_BD, BD_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hc₀ : c₀ ∈ longRootGroupSU K p f (ε • BD (suMat A) (suMat A')) :=
    mem_longRootGroupSU.mpr ⟨h1, h2⟩
  refine ⟨g * c₀ * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [hsu]
    exact conj_mem_longRootGroupSU_conj g hc₀
  · apply suMat_injective
    have e : g * c₀ * g⁻¹ * (g * c₀ * g⁻¹) = g * (c₀ * c₀) * g⁻¹ := by group
    rw [e, hsu, suMat_mul, suMat_mul, suMat_mul, h3]
  · have e1 : g * c₀ * g⁻¹ * a = g * (c₀ * blockEmb K p f 4 2 0 (by norm_num) A) * g⁻¹ := by
      rw [ha]; group
    have e2 : a * (g * c₀ * g⁻¹) = g * (blockEmb K p f 4 2 0 (by norm_num) A * c₀) * g⁻¹ := by
      rw [ha]; group
    rw [e1, e2]
    congr 2
    apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_blockEmb_zero_eq_BD, h4]
  · have e1 : g * c₀ * g⁻¹ * a' = g * (c₀ * blockEmb K p f 4 2 2 (by norm_num) A') * g⁻¹ := by
      rw [ha']; group
    have e2 : a' * (g * c₀ * g⁻¹) = g * (blockEmb K p f 4 2 2 (by norm_num) A' * c₀) * g⁻¹ := by
      rw [ha']; group
    rw [e1, e2]
    congr 2
    apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_blockEmb_two_eq_BD, h5]

end SqrtInv

section SqrtInvFund

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_sqrt_inv_of_fund_centralizing (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {a a' : Su K p f 4} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Su K p f 4)) {ι : K} (hι2 : ι * ι = -1)
    (hσι : unitaryInvolution K p f ι = -ι) {L : Subgroup (Su K p f 4)}
    (hL : L ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4))
    (hLc : ∀ y ∈ L, y * (a * a') = (a * a') * y) {X : Type*} [Group X] {θ : Su K p f 4 →* X}
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) :
    ∃ r ∈ L, ∃ c ∈ L, r * r = 1 ∧ θ r ≠ 1 ∧ r * (a * a') ∈ Subgroup.center (Su K p f 4) ∧
      c * c = r ∧ c * a = a * c ∧ c * a' = a' * c := by
  obtain ⟨hι2', hσι'⟩ := neg_iota_props _ hι2 hσι
  obtain ⟨hu2, htr⟩ := su4_twin_sq_trace hK hp hR hR' hne hxR hxc hx1 hx'R' hx'c hx'1 hsame ha ha'
    hsq hsq'
  obtain ⟨g, A, A', hag, ha'g, hA, hA'⟩ := su4_twin_block_data hK hp hR hR' hne hxR hxc hx1 hx'R'
    hx'c hx'1 hsame ha ha' hsq hsq'
  rcases eq_longRootGroupSU_jEl hK hp hq hu2 htr hι2 hσι hL hLc with h | h
  · have hr := exists_isLongRootSU2_jEl hK hp hu2 htr ι hι2 hσι
    obtain ⟨c, hcL, hcc, hca, hca'⟩ := exists_sqrt_jEl hp hag ha'g hA hA' ι hι2 hσι
    refine ⟨jEl (a * a') ι hι2 hσι, ?_, c, ?_, jEl_mul_self hu2 ι hι2 hσι, ?_,
      jEl_mul_u_mem_center hu2 ι hι2 hσι, hcc, hca, hca'⟩
    · rw [h]
      exact jEl_mem_longRootGroup hu2 ι hι2 hσι
    · rw [h]
      exact hcL
    · exact CFSG.ClassicalInvolution.Models.Transfer.map_ne_one_of_isLongRootSU2 hK hp hq
        (by norm_num) hker hr
  · have hr := exists_isLongRootSU2_jEl hK hp hu2 htr (-ι) hι2' hσι'
    obtain ⟨c, hcL, hcc, hca, hca'⟩ := exists_sqrt_jEl hp hag ha'g hA hA' (-ι) hι2' hσι'
    refine ⟨jEl (a * a') (-ι) hι2' hσι', ?_, c, ?_, jEl_mul_self hu2 (-ι) hι2' hσι', ?_,
      jEl_mul_u_mem_center hu2 (-ι) hι2' hσι', hcc, hca, hca'⟩
    · rw [h]
      exact jEl_mem_longRootGroup hu2 (-ι) hι2' hσι'
    · rw [h]
      exact hcL
    · exact CFSG.ClassicalInvolution.Models.Transfer.map_ne_one_of_isLongRootSU2 hK hp hq
        (by norm_num) hker hr

end SqrtInvFund

section Model

variable {p : ℕ} [Fact p.Prime]


theorem twinMF_sqrt_central (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) (hmod : (p ^ e) % 4 = 3)
    {R R' : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    {x x' : (modelUniv .PSU 4 p e Fact.out).K}
    (hd : TwinDatumOn .PSU (modelUniv .PSU 4 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSU 4 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    {X : Type} [Group X] (ψ : (modelUniv .PSU 4 p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K)
    {S : Subgroup (modelUniv .PSU 4 p e Fact.out).K}
    (hS : S ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D)
    (hSc : ∀ s ∈ S, (a * a') * s = s * (a * a')) :
    ∃ r ∈ S, ∃ c ∈ S, r * r = 1 ∧ ψ r ≠ 1 ∧
      r * (a * a') ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K ∧
      c * c = r ∧ c * a = a * c ∧ c * a' = a' * c := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSU 4 p e :=
    ⟨Fact.out, he, by norm_num, fun h => by
      have : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega⟩
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hRm := (hφ R).mp hd.mem
  have hR'm := (hφ R').mp hd.mem'
  have hnem : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
    hd.ne (Subgroup.map_injective φ.injective h)
  have hxm : φ x ∈ R.map φ.toMonoidHom := ⟨x, hd.hx, rfl⟩
  have hxcm : ∀ r ∈ R.map φ.toMonoidHom, φ x * r = r * φ x := by
    rintro _ ⟨r, hr, rfl⟩
    show φ x * φ r = φ r * φ x
    rw [← map_mul, ← map_mul, hd.cx r hr]
  have hx1m : φ x ≠ 1 := fun h => hd.nx (φ.injective (h.trans (map_one φ).symm))
  have hx'm : φ x' ∈ R'.map φ.toMonoidHom := ⟨x', hd.hx', rfl⟩
  have hx'cm : ∀ r ∈ R'.map φ.toMonoidHom, φ x' * r = r * φ x' := by
    rintro _ ⟨r, hr, rfl⟩
    show φ x' * φ r = φ r * φ x'
    rw [← map_mul, ← map_mul, hd.cx' r hr]
  have hx'1m : φ x' ≠ 1 := fun h => hd.nx' (φ.injective (h.trans (map_one φ).symm))
  have hsamem : φ x * (φ x')⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    rw [← map_inv, ← map_mul]
    exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hd.same
  have ham : φ a ∈ R.map φ.toMonoidHom := ⟨a, ha, rfl⟩
  have ha'm : φ a' ∈ R'.map φ.toMonoidHom := ⟨a', ha', rfl⟩
  have hsqm : φ a * φ a * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq
  have hsq'm : φ a' * φ a' * (φ x')⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ hsq'
  obtain ⟨ι, hι2, hσι⟩ := exists_iota hK hmod
  have hc' : ∀ y ∈ S.map φ.toMonoidHom, y * (φ a * φ a') = (φ a * φ a') * y := by
    rintro _ ⟨s, hs, rfl⟩
    show φ s * (φ a * φ a') = (φ a * φ a') * φ s
    rw [← map_mul, ← map_mul, ← map_mul, hSc s hs]
  have hker' : (ψ.comp φ.symm.toMonoidHom).ker ≤
      Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
    intro s hs
    have hs' : φ.symm s ∈ ψ.ker := hs
    have := CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ (hker hs')
    simpa using this
  obtain ⟨r', hr'L, c', hc'L, hr'2, hr'1, hr'c, hc'c, hc'a, hc'a'⟩ :=
    exists_sqrt_inv_of_fund_centralizing hK hp2 hq hRm hR'm hnem hxm hxcm hx1m hx'm hx'cm hx'1m
      hsamem ham ha'm hsqm hsq'm hι2 hσι ((hφ S).mp hS) hc' hker'
  obtain ⟨r, hrS, rfl⟩ := hr'L
  obtain ⟨c, hcS, rfl⟩ := hc'L
  refine ⟨r, hrS, c, hcS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, map_one]
    exact hr'2
  · intro h
    apply hr'1
    show ψ (φ.symm (φ r)) = 1
    rw [MulEquiv.symm_apply_apply]
    exact h
  · have := CFSG.ClassicalInvolution.RouteD.SCRSu4.mem_center_map φ.symm hr'c
    simpa [map_mul] using this
  · apply φ.injective
    rw [map_mul]
    exact hc'c
  · apply φ.injective
    rw [map_mul, map_mul]
    exact hc'a
  · apply φ.injective
    rw [map_mul, map_mul]
    exact hc'a'

end Model

end CFSG.ClassicalInvolution.RouteD.TWT4
