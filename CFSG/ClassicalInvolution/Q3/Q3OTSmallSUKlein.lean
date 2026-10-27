module

public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSUSq

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem actsAsM_conj_inv3 (g : Su K p f 4) :
    ActsAsM (MulAut.conj (QuotientGroup.mk g : PU K p f))⁻¹ (suMat g⁻¹) (suMat g) := by
  have h := actsAsM_conj g⁻¹
  rwa [inv_inv, QuotientGroup.mk_inv, map_inv] at h

theorem actsAsM_smul3 {φ : MulAut (PU K p f)} {M Mi : Matrix (Fin 4) (Fin 4) K}
    (hφ : ActsAsM φ M Mi) {ν : K} (hν : ν ≠ 0) : ActsAsM φ (ν • M) (ν⁻¹ • Mi) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hν, one_smul, h1]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hν, one_smul, h2]
  · obtain ⟨h', hh', hm⟩ := h3 h
    refine ⟨h', hh', ?_⟩
    rw [hm, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hν,
      one_smul]

theorem actsAsM_of_smul_eq {φ : MulAut (PU K p f)} {M Mi : Matrix (Fin 4) (Fin 4) K}
    (hφ : ActsAsM φ M Mi) {ν : K} (hν : ν ≠ 0) {D : Matrix (Fin 4) (Fin 4) K} (hD : D = ν • M)
    (hDD : D * D = 1) : ActsAsM φ D D := by
  have h := actsAsM_smul3 hφ hν
  rw [← hD] at h
  have hMi : D = ν⁻¹ • Mi := left_inv_eq_right_inv hDD h.1
  rw [← hMi] at h
  exact h

theorem su4_klein_matrix3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    (hcop : ∀ z ∈ Subgroup.center (Su K p f 4), ¬ 3 ∣ orderOf z)
    (hL : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) {k : Su K p f 4} (hkR : k ∈ R)
    (hkk : (QuotientGroup.mk k : PU K p f) * QuotientGroup.mk k = QuotientGroup.mk x)
    (φ : MulAut (PU K p f))
    (hφR : ∀ r ∈ R, φ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hφR' : ∀ r ∈ R', φ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hφ2 : φ * φ = MulAut.conj (QuotientGroup.mk x : PU K p f)) :
    ∃ D : Matrix (Fin 4) (Fin 4) K, D * D = 1 ∧ conjTr (unitaryInvolution K p f) D * D = 1 ∧
      ActsAsM (MulAut.conj (QuotientGroup.mk k : PU K p f) * φ) D D := by
  obtain ⟨g, hRg, hR'g, hxg, hkg⟩ := twin_std_ku3 hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
    hkR hkk
  obtain ⟨c, hcdef⟩ : ∃ c : MulAut (PU K p f), c = MulAut.conj (QuotientGroup.mk g : PU K p f) :=
    ⟨_, rfl⟩
  have hcp : ∀ s : Su K p f 4, c (QuotientGroup.mk s) = QuotientGroup.mk (g * s * g⁻¹) := by
    intro s
    rw [hcdef, MulAut.conj_apply]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hcg : ActsAsM c (suMat g) (suMat g⁻¹) := by
    rw [hcdef]
    exact actsAsM_conj g
  have hcgi : ActsAsM c⁻¹ (suMat g⁻¹) (suMat g) := by
    rw [hcdef]
    exact actsAsM_conj_inv3 g
  obtain ⟨φ', hφ'def⟩ : ∃ φ' : MulAut (PU K p f), φ' = c⁻¹ * φ * c := ⟨_, rfl⟩
  have hφ'p : ∀ s : Su K p f 4, φ' (QuotientGroup.mk s) = c⁻¹ (φ (c (QuotientGroup.mk s))) := by
    intro s
    rw [hφ'def]
    rfl
  have hfixφ' : ∀ S : Subgroup (Su K p f 4),
      (∀ r ∈ S.map (MulAut.conj g).toMonoidHom, φ (QuotientGroup.mk r) = QuotientGroup.mk r) →
      ∀ r ∈ S, φ' (QuotientGroup.mk r) = QuotientGroup.mk r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hφ'p, hcp, hS _ hmem, ← hcp]
    simp
  have hfix0 := hfixφ' ((blockEmb K p f 4 2 0 (by norm_num)).range) (hRg ▸ hφR)
  have hfix2 := hfixφ' ((blockEmb K p f 4 2 2 (by norm_num)).range) (hR'g ▸ hφR')
  have hφ'2 : φ' * φ' = MulAut.conj (QuotientGroup.mk
      (rootInvSU K p f (show 2 ≤ 4 by norm_num)) : PU K p f) := by
    have e1 : φ' * φ' = c⁻¹ * (φ * φ) * c := by
      rw [hφ'def]
      group
    have e2 : MulAut.conj (QuotientGroup.mk (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) *
        g⁻¹) : PU K p f) = c * MulAut.conj (QuotientGroup.mk
          (rootInvSU K p f (show 2 ≤ 4 by norm_num)) : PU K p f) * c⁻¹ := by
      rw [hcdef]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rw [e1, hφ2, hxg, e2]
    group
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hact⟩ := su4_sq_blocks3 hK hp hf hcop hL φ'
    (fun A => hfix0 _ ⟨A, rfl⟩) (fun A => hfix2 _ ⟨A, rfl⟩) hφ'2
  have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : K, i₀ = b * a⁻¹ := ⟨_, rfl⟩
  have hi : i₀ * i₀ = -1 := by
    rw [hi₀]
    linear_combination (a⁻¹ * a⁻¹) * hab - (a * a⁻¹ + 1) * hainv
  have hi0 : i₀ ≠ 0 := by
    rw [hi₀]
    exact mul_ne_zero hb (inv_ne_zero ha)
  have hσa : unitaryInvolution K p f a = a⁻¹ := eq_inv_of_mul_eq_one_left ha1
  have hσb : unitaryInvolution K p f b = b⁻¹ := eq_inv_of_mul_eq_one_left hb1
  have hσi : unitaryInvolution K p f i₀ = -i₀ := by
    have h1 : unitaryInvolution K p f i₀ * i₀ = 1 := by
      rw [hi₀, map_mul, map_inv₀, hσa, hσb, inv_inv]
      calc b⁻¹ * a * (b * a⁻¹) = (b⁻¹ * b) * (a * a⁻¹) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hb, hainv, one_mul]
    have h2 : (-i₀) * i₀ = 1 := by linear_combination (-1 : K) * hi
    exact mul_right_cancel₀ hi0 (h1.trans h2.symm)
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin 4) (Fin 4) K,
      Dm = !![0, i₀, 0, 0; -i₀, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := ⟨_, rfl⟩
  have hDD : Dm * Dm = 1 := by
    rw [hDm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hi]
  have hDh : conjTr (unitaryInvolution K p f) Dm = Dm := by
    generalize unitaryInvolution K p f = σ at hσi ⊢
    rw [hDm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, hσi]
  have hDu : conjTr (unitaryInvolution K p f) Dm * Dm = 1 := by
    rw [hDh]
    exact hDD
  obtain ⟨J0, hJ0⟩ : ∃ J0 : Su K p f 4, J0 = blockEmb K p f 4 2 0 (by norm_num) (jSU K p f) :=
    ⟨_, rfl⟩
  have hJmat : suMat J0 = !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [hJ0, suMat_blockEmb_zero, suMat_jSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hkJ : k = g * J0 * g⁻¹ := by
    rw [hJ0]
    exact hkg
  have hM : suMat J0 *
      (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K) =
      !![0, a, 0, 0; -a, 0, 0, 0; 0, 0, b, 0; 0, 0, 0, b] := by
    rw [hJmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  obtain ⟨ν, hν⟩ : ∃ ν : K, ν = i₀ * a⁻¹ := ⟨_, rfl⟩
  have hν0 : ν ≠ 0 := by
    rw [hν]
    exact mul_ne_zero hi0 (inv_ne_zero ha)
  have hνa : ν * a = i₀ := by rw [hν, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  have hνb : ν * b = -1 := by
    rw [hν]
    calc i₀ * a⁻¹ * b = i₀ * (b * a⁻¹) := by ring
      _ = i₀ * i₀ := by rw [← hi₀]
      _ = -1 := hi
  have hνM : ν • (!![0, a, 0, 0; -a, 0, 0, 0; 0, 0, b, 0; 0, 0, 0, b] :
      Matrix (Fin 4) (Fin 4) K) = Dm := by
    rw [hDm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hνa, hνb]
  have hJact : ActsAsM (MulAut.conj (QuotientGroup.mk J0 : PU K p f) * φ') Dm Dm := by
    refine actsAsM_of_smul_eq ((actsAsM_conj J0).mul hact) hν0 ?_ hDD
    rw [hM, hνM]
  have hfin := (hcg.mul hJact).mul hcgi
  have hconj : c * (MulAut.conj (QuotientGroup.mk J0 : PU K p f) * φ') * c⁻¹ =
      MulAut.conj (QuotientGroup.mk k : PU K p f) * φ := by
    have e : MulAut.conj (QuotientGroup.mk k : PU K p f) =
        c * MulAut.conj (QuotientGroup.mk J0 : PU K p f) * c⁻¹ := by
      rw [hkJ, hcdef]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rw [e, hφ'def]
    group
  have hD2 : suMat g * (Dm * suMat g⁻¹) = suMat g * Dm * suMat g⁻¹ :=
    (Matrix.mul_assoc _ _ _).symm
  rw [hD2, hconj] at hfin
  refine ⟨suMat g * Dm * suMat g⁻¹, ?_, ?_, hfin⟩
  · calc suMat g * Dm * suMat g⁻¹ * (suMat g * Dm * suMat g⁻¹)
        = suMat g * (Dm * (suMat g⁻¹ * suMat g) * Dm) * suMat g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [suMat_inv_mul_suMat, Matrix.mul_one, hDD, Matrix.mul_one, suMat_mul_suMat_inv]
  · have hg1 : conjTr (unitaryInvolution K p f) (suMat g) * suMat g = 1 := g.2.2
    have hg2 : conjTr (unitaryInvolution K p f) (suMat g⁻¹) * suMat g⁻¹ = 1 := (g⁻¹).2.2
    calc conjTr (unitaryInvolution K p f) (suMat g * Dm * suMat g⁻¹) *
          (suMat g * Dm * suMat g⁻¹)
        = conjTr (unitaryInvolution K p f) (suMat g⁻¹) *
            (conjTr (unitaryInvolution K p f) Dm *
              (conjTr (unitaryInvolution K p f) (suMat g) * suMat g) * Dm) * suMat g⁻¹ := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hg1, Matrix.mul_one, hDu, Matrix.mul_one, hg2]

end CFSG.ClassicalInvolution.Q3.Q3OT
