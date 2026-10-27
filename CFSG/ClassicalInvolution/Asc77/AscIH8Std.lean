module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyAll

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section MatrixFacts

variable {F : Type*} [Field F]

theorem embPair_two_eq_one_of_commute_rot (A : Matrix (Fin 2) (Fin 2) F) (hdet : A.det = 1)
    (h : embPair 2 A * embPair 0 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
      embPair 0 Phan.rotMat * embPair 2 A) : A = 1 := by
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h12 := congrFun (congrFun h 1) 2
  simp [embPair, Phan.rotMat, Matrix.mul_apply, Fin.sum_univ_three] at h01 h10 h12
  have e01 : A 0 1 = 0 := h01.symm
  rw [Matrix.det_fin_two, e01, h10, h12] at hdet
  have e00 : A 0 0 = 1 := by simpa using hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, h10, h12, e00]

theorem embPair_zero_conj_rot (M A' : Matrix (Fin 2) (Fin 2) F)
    (h : embPair 0 M * embPair 2 (Phan.rotMat : Matrix (Fin 2) (Fin 2) F) =
      embPair 2 A' * embPair 0 M) : M 0 1 = 0 ∧ M 1 0 = 0 := by
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h20 := congrFun (congrFun h 2) 0
  simp [embPair, Phan.rotMat, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02 h20
  refine ⟨?_, h20⟩
  rcases h02 with h | h
  · rw [h, zero_mul] at h01
    exact absurd h01 (by simp)
  · exact h

theorem mul_comm_of_offDiag_eq_zero {M M' : Matrix (Fin 2) (Fin 2) F} (h01 : M 0 1 = 0)
    (h10 : M 1 0 = 0) (h01' : M' 0 1 = 0) (h10' : M' 1 0 = 0) : M * M' = M' * M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h01', h10',
    mul_comm]

end MatrixFacts

section Linear

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem B23_perfect (h4 : 4 ≤ Nat.card F) : WeakCT.B23 F ≤ ⁅WeakCT.B23 F, WeakCT.B23 F⁆ :=
  range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4)
    (WeakCT.blockSL F 3 2 1 (by omega))

theorem B12_perfect (h4 : 4 ≤ Nat.card F) : WeakCT.B12 F ≤ ⁅WeakCT.B12 F, WeakCT.B12 F⁆ :=
  range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4)
    (WeakCT.blockSL F 3 2 0 (by omega))

omit [Finite F] in
theorem coe_blockSL_zero (A : SL(2, F)) :
    ((WeakCT.blockSL F 3 2 0 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      embPair 2 (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [WeakCT.coe_blockSL, Phan.embPair_two_eq_blockMat]

omit [Finite F] in
theorem coe_blockSL_one (A : SL(2, F)) :
    ((WeakCT.blockSL F 3 2 1 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      embPair 0 (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [WeakCT.coe_blockSL, Phan.embPair_zero_eq_blockMat]

theorem LinearBlockStandardPair.eq_one_of_centralizes (h4 : 4 ≤ Nat.card F) {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) {x : X} (hx : x ∈ U)
    (hc : ∀ y ∈ V, x * y = y * x) : x = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hU] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hcomm : ∀ g ∈ WeakCT.B23 F, b * g = g * b := by
    refine
      CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
      (B23_perfect h4) ?_
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker]
    have := hc (θ g) (hV ▸ Subgroup.mem_map_of_mem θ hg)
    simp only [map_mul, map_inv]
    rw [this]
    group
  obtain ⟨A, rfl⟩ := hb
  have hr : WeakCT.blockSL F 3 2 1 (by omega) (WeakCT.rotSL) ∈ WeakCT.B23 F := ⟨_, rfl⟩
  have h1 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F))
    (hcomm _ hr)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h1
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = 1 :=
    embPair_two_eq_one_of_commute_rot _ A.2 h1
  have : A = 1 := Subtype.ext hA
  rw [this, map_one, map_one]

theorem LinearBlockStandardPair.comm_of_normalizes (h4 : 4 ≤ Nat.card F) {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair F W U V) {x y : X} (hxV : x ∈ V) (hyV : y ∈ V)
    (hxN : x ∈ Subgroup.normalizer (U : Set X)) (hyN : y ∈ Subgroup.normalizer (U : Set X)) :
    x * y = y * x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hV] at hxV hyV
  obtain ⟨g, hg, rfl⟩ := hxV
  obtain ⟨g', hg', rfl⟩ := hyV
  rw [← hU] at hxN hyN
  have key : ∀ g ∈ WeakCT.B23 F,
      θ g ∈ Subgroup.normalizer (((WeakCT.B12 F).map θ : Subgroup X) : Set X) →
      ∃ M : SL(2, F), g = WeakCT.blockSL F 3 2 1 (by omega) M ∧
        (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    intro g hg hgN
    have hgN' := ih8_mem_normalizer_of_map hker (B12_perfect h4) hgN
    obtain ⟨M, rfl⟩ := hg
    refine ⟨M, rfl, ?_⟩
    have hb : WeakCT.blockSL F 3 2 0 (by omega) (WeakCT.rotSL) ∈ WeakCT.B12 F := ⟨_, rfl⟩
    obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
    have h2 : WeakCT.blockSL F 3 2 0 (by omega) A' * WeakCT.blockSL F 3 2 1 (by omega) M =
        WeakCT.blockSL F 3 2 1 (by omega) M * WeakCT.blockSL F 3 2 0 (by omega) WeakCT.rotSL := by
      rw [hA']
      group
    have h3 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_zero, coe_blockSL_one] at h3
    exact embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨M, rfl, h01, h10⟩ := key g hg hxN
  obtain ⟨M', rfl, h01', h10'⟩ := key g' hg' hyN
  have hMM : M * M' = M' * M :=
    Subtype.ext (by
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      exact mul_comm_of_offDiag_eq_zero h01 h10 h01' h10')
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hMM]

end Linear

section Unitary

open CFSG.ClassicalInvolution.Models (suMat det_suMat)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {X : Type} [Group X]

theorem unitaryB23_perfect (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Phan.B23 K p f ≤ ⁅Phan.B23 K p f, Phan.B23 K p f⁆ :=
  range_le_commutator (isPerfect_su_two hK hq) (embSUid (unitaryInvolution K p f) 0)

theorem unitaryB12_perfect (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Phan.B12 K p f ≤ ⁅Phan.B12 K p f, Phan.B12 K p f⁆ :=
  range_le_commutator (isPerfect_su_two hK hq) (embSUid (unitaryInvolution K p f) 2)

theorem UnitaryBlockStandardPair.eq_one_of_centralizes (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : 5 ≤ p ^ f) {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V) {x : X}
    (hx : x ∈ U) (hc : ∀ y ∈ V, x * y = y * x) : x = 1 := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  rw [← hU] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hcomm : ∀ g ∈ Phan.B23 K p f, b * g = g * b := by
    refine
      CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
      (unitaryB23_perfect hK hq) ?_
    intro g hg
    apply hker
    rw [MonoidHom.mem_ker]
    have := hc (θ g) (hV ▸ Subgroup.mem_map_of_mem θ hg)
    simp only [map_mul, map_inv]
    rw [this]
    group
  obtain ⟨A, rfl⟩ := hb
  have hr : embSUid (unitaryInvolution K p f) 0 (Phan.rotSU (unitaryInvolution K p f)) ∈
      Phan.B23 K p f := ⟨_, rfl⟩
  have h1 := congrArg suMat (hcomm _ hr)
  simp only [Models.suMat_mul] at h1
  have hA : suMat A = 1 := embPair_two_eq_one_of_commute_rot _ (det_suMat A) h1
  have : A = 1 := Models.suMat_injective (by rw [hA, Models.suMat_one])
  rw [this, map_one, map_one]

theorem UnitaryBlockStandardPair.comm_of_normalizes (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : 5 ≤ p ^ f) {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V)
    {x y : X} (hxV : x ∈ V) (hyV : y ∈ V) (hxN : x ∈ Subgroup.normalizer (U : Set X))
    (hyN : y ∈ Subgroup.normalizer (U : Set X)) : x * y = y * x := by
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  rw [← hV] at hxV hyV
  obtain ⟨g, hg, rfl⟩ := hxV
  obtain ⟨g', hg', rfl⟩ := hyV
  rw [← hU] at hxN hyN
  have key : ∀ g ∈ Phan.B23 K p f,
      θ g ∈ Subgroup.normalizer (((Phan.B12 K p f).map θ : Subgroup X) : Set X) →
      ∃ M : Phan.Su K p f 2, g = embSUid (unitaryInvolution K p f) 0 M ∧
        suMat M 0 1 = 0 ∧ suMat M 1 0 = 0 := by
    intro g hg hgN
    have hgN' := ih8_mem_normalizer_of_map hker (unitaryB12_perfect hK hq) hgN
    obtain ⟨M, rfl⟩ := hg
    refine ⟨M, rfl, ?_⟩
    have hb : embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) ∈
        Phan.B12 K p f := ⟨_, rfl⟩
    obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.mp hgN' _).mp hb
    have h2 : embSUid (unitaryInvolution K p f) 2 A' * embSUid (unitaryInvolution K p f) 0 M =
        embSUid (unitaryInvolution K p f) 0 M *
          embSUid (unitaryInvolution K p f) 2 (Phan.rotSU (unitaryInvolution K p f)) := by
      rw [hA']
      group
    have h3 := congrArg suMat h2
    simp only [Models.suMat_mul] at h3
    exact embPair_zero_conj_rot _ _ h3.symm
  obtain ⟨M, rfl, h01, h10⟩ := key g hg hxN
  obtain ⟨M', rfl, h01', h10'⟩ := key g' hg' hyN
  have hMM : M * M' = M' * M := by
    apply Models.suMat_injective
    simp only [Models.suMat_mul]
    exact mul_comm_of_offDiag_eq_zero h01 h10 h01' h10'
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hMM]

end Unitary

section Commuting

variable {p e : ℕ} [Fact p.Prime]

theorem four_le_of_commutes_psl (hp2 : p ≠ 2) {n : ℕ} (hn3 : 3 ≤ n)
    {R S : Subgroup (modelUniv .PSL n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL n p e Fact.out).D)
    (hS : S ∈ fundamentalSubgroups .PSL (modelUniv .PSL n p e Fact.out).D) (hne : R ≠ S)
    (hc : Commutes R S) : 4 ≤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [fundamentalSubgroups_psl_eq (p := p) (f := e) (by omega : 1 ≤ m)] at hR hS
  obtain ⟨i₁, h₁⟩ := hR
  obtain ⟨i₂, h₂⟩ := hS
  exact four_le_of_commutes (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) hn3
    h₁ h₂ hne hc

theorem four_le_of_commutes_psu (hp2 : p ≠ 2) {n : ℕ} (hadm : StatedLieAdmissible .PSU n p e)
    {R S : Subgroup (modelUniv .PSU n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e Fact.out).D)
    (hS : S ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p e Fact.out).D) (hne : R ≠ S)
    (hc : Commutes R S) : 4 ≤ n := by
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hn : 2 ≤ n := by omega
  have hR' := (hφ R).mp hR
  have hS' := (hφ S).mp hS
  obtain ⟨V₀, n₀, d₀, hV₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp hR'
  obtain ⟨V₁, n₁, d₁, hV₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp hS'
  have hne' : V₀ ≠ V₁ := by
    intro h
    apply hne
    exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (by rw [hV₀, hV₁, h])
  have hc' : Commutes (R.map φ.toMonoidHom) (S.map φ.toMonoidHom) :=
    (commutes_map_equiv φ).mpr hc
  rw [hV₀, hV₁] at hc'
  have horth := (commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₁ d₁ hne').mp hc'
  have hsum := Phan.finrank_sup_of_disjoint (disjoint_of_orth n₁ horth)
  have hle := Submodule.finrank_le (V₀ ⊔ V₁)
  rw [Module.finrank_fin_fun] at hle
  omega

end Commuting

theorem ih8_stdDichotomy {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {k e : ℕ}
    (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hadm : StatedLieAdmissible t k p e) : ModelFacts.StandardPairDichotomy p t k e :=
  ModelFacts.standardPairDichotomy_of_FE ModelFacts.standardPairDichotomyFE_proved hfund hG2 hD4
    hadm

end CFSG.ClassicalInvolution.Asc77
