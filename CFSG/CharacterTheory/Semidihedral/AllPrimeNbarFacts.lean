module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
import CFSG.CharacterTheory.Semidihedral.AllPrimeDataInputs

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped commutatorElement Pointwise
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem frontier_commutator_N_le_L₀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ⁅(frontierSetting S fS t p f).N, (frontierSetting S fS t p f).N⁆ ≤
      (frontierSetting S fS t p f).L₀ := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨-, -, hcomm⟩ :=
    LocalLayerAbelianQuotients.actual_matrix_layer_preimage_has_abelian_quotient
      t n p f hp hpodd hf F A rho data
  change ⁅C t, C t⁆ ≤ (localLayerPreimage t).map (C t).subtype
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  refine ⟨⁅(⟨g₁, hg₁⟩ : C t), ⟨g₂, hg₂⟩⁆, hcomm ?_, rfl⟩
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem frontier_L_le_N {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    (frontierSetting S fS t p f).L ≤ (frontierSetting S fS t p f).N :=
  sup_le (Subgroup.map_subtype_le _) (frontier_S_le_C hn S fS t ht p f)

theorem frontier_L_normal {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).N ≤
      Subgroup.normalizer ((frontierSetting S fS t p f).L : Set G) := by
  have hcomm := frontier_commutator_N_le_L₀ hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  have hLN := frontier_L_le_N hn S fS t ht p f
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  intro h hh
  have h1 : g * h * g⁻¹ = ⁅g, h⁆ * h := by rw [commutatorElement_def]; group
  rw [h1]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (hcomm (Subgroup.commutator_mem_commutator hg (hLN hh)))) hh

private theorem layer_quotient_isCyclic {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht2 : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    IsCyclic (H t ⧸ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) := by
  obtain ⟨-, hJindex, hz, hc, hunique, ⟨P, ⟨eP⟩⟩, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t := simple_le_index_two _ _ hJindex hnonab
  have hp2 : p ≠ 2 := fun h => (by decide : ¬Odd (2 : ℕ)) (h ▸ hpodd)
  obtain ⟨-, -, -, -, F, -, -, -, A, rho, eta, -, -, -, -, -, -, -, -, -, -, hcyc, -⟩ :=
    ActualLayerOddExtensions.actual_linear_two_local_layer_odd_field_extension
      (nu t (tInC t)) hz hc (barKappa t) (barKappa_surjective t) (barKappa_kernel t)
      (n - 1) (by omega) P (by
        have he : n - 1 - 1 = n - 2 := by omega
        rw [he]
        exact eP) hnonab hcentral hnc (J t) hJindex hLJ hunique ⟨hp, hp2, hf⟩ hmodel
  exact hcyc

theorem frontier_N_mod_L_cyclic {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ g ∈ (frontierSetting S fS t p f).N, ∀ m ∈ (frontierSetting S fS t p f).N,
      ∃ k : ℤ, m * (g ^ k)⁻¹ ∈ (frontierSetting S fS t p f).L := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hcyc := layer_quotient_isCyclic n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
    hmodel
  set Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hY
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := H t ⧸ Y)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : C t, QuotientGroup.mk' Y (nu t g₀) = γ :=
    ((QuotientGroup.mk'_surjective Y).comp (QuotientGroup.mk'_surjective (N t))) γ
  refine ⟨(g₀ : G), g₀.2, fun m hm => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ (QuotientGroup.mk' Y (nu t ⟨m, hm⟩)))
  refine ⟨k, Subgroup.mem_sup_left ⟨⟨m, hm⟩ * (g₀ ^ k)⁻¹, ?_, rfl⟩⟩
  change nu t (⟨m, hm⟩ * (g₀ ^ k)⁻¹) ∈ Y
  rw [← QuotientGroup.eq_one_iff (N := Y), ← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv,
    map_inv, map_zpow, map_zpow, hg₀, ← hk, mul_inv_cancel]

section Matrices

private theorem matrix_commute_of_commute_nonscalar {F : Type*} [Field F]
    (g X₁ X₂ : Matrix (Fin 2) (Fin 2) F) (hg : ¬ (g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 0 = g 1 1))
    (h₁ : g * X₁ = X₁ * g) (h₂ : g * X₂ = X₂ * g) : X₁ * X₂ = X₂ * X₁ := by
  have entries : ∀ X : Matrix (Fin 2) (Fin 2) F, g * X = X * g →
      g 0 1 * X 1 0 = X 0 1 * g 1 0 ∧ g 0 1 * (X 1 1 - X 0 0) = X 0 1 * (g 1 1 - g 0 0) ∧
        g 1 0 * (X 0 0 - X 1 1) = X 1 0 * (g 0 0 - g 1 1) := by
    intro X hX
    have e00 := congrFun (congrFun hX 0) 0
    have e01 := congrFun (congrFun hX 0) 1
    have e10 := congrFun (congrFun hX 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
    exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e10⟩
  obtain ⟨A1, B1, C1⟩ := entries X₁ h₁
  obtain ⟨A2, B2, C2⟩ := entries X₂ h₂
  have key : X₁ 0 1 * X₂ 1 0 = X₂ 0 1 * X₁ 1 0 ∧
      X₂ 0 1 * (X₁ 0 0 - X₁ 1 1) = X₁ 0 1 * (X₂ 0 0 - X₂ 1 1) ∧
      X₁ 1 0 * (X₂ 0 0 - X₂ 1 1) = X₂ 1 0 * (X₁ 0 0 - X₁ 1 1) := by
    by_cases hb : g 0 1 = 0
    · by_cases hc : g 1 0 = 0
      · have had : g 1 1 - g 0 0 ≠ 0 := fun h => hg ⟨hb, hc, by linear_combination -h⟩
        have hy : ∀ X : Matrix (Fin 2) (Fin 2) F,
            g 0 1 * (X 1 1 - X 0 0) = X 0 1 * (g 1 1 - g 0 0) → X 0 1 = 0 := fun X h =>
          (mul_eq_zero.mp (by rw [← h, hb, zero_mul])).resolve_right had
        have hz : ∀ X : Matrix (Fin 2) (Fin 2) F,
            g 1 0 * (X 0 0 - X 1 1) = X 1 0 * (g 0 0 - g 1 1) → X 1 0 = 0 := fun X h =>
          (mul_eq_zero.mp (by rw [← h, hc, zero_mul])).resolve_right
            (fun h' => had (by linear_combination -h'))
        rw [hy X₁ B1, hy X₂ B2, hz X₁ C1, hz X₂ C2]
        exact ⟨by ring, by ring, by ring⟩
      · have hy : ∀ X : Matrix (Fin 2) (Fin 2) F,
            g 0 1 * X 1 0 = X 0 1 * g 1 0 → X 0 1 = 0 := fun X h =>
          (mul_eq_zero.mp (by rw [← h, hb, zero_mul])).resolve_right hc
        rw [hy X₁ A1, hy X₂ A2]
        refine ⟨by ring, by ring, ?_⟩
        apply mul_left_cancel₀ hc
        linear_combination X₁ 1 0 * C2 - X₂ 1 0 * C1
    · have k1 : X₁ 0 1 * X₂ 1 0 = X₂ 0 1 * X₁ 1 0 := by
        apply mul_left_cancel₀ hb
        linear_combination X₁ 0 1 * A2 - X₂ 0 1 * A1
      have k2 : X₂ 0 1 * (X₁ 0 0 - X₁ 1 1) = X₁ 0 1 * (X₂ 0 0 - X₂ 1 1) := by
        apply mul_left_cancel₀ hb
        linear_combination X₁ 0 1 * B2 - X₂ 0 1 * B1
      refine ⟨k1, k2, ?_⟩
      apply mul_left_cancel₀ hb
      linear_combination (X₂ 0 0 - X₂ 1 1) * A1 - (X₁ 0 0 - X₁ 1 1) * A2 - g 1 0 * k2
  obtain ⟨K1, K2, K3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · linear_combination K1
  · linear_combination K2
  · linear_combination K3
  · linear_combination -K1

private theorem gl_commute_of_commute_nonscalar {F : Type*} [Field F]
    {g X₁ X₂ : GL (Fin 2) F} (hg : ¬ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = g)
    (h₁ : g * X₁ = X₁ * g) (h₂ : g * X₂ = X₂ * g) : X₁ * X₂ = X₂ * X₁ := by
  apply Units.ext
  refine matrix_commute_of_commute_nonscalar (g : Matrix (Fin 2) (Fin 2) F) _ _ ?_
    (congrArg Units.val h₁) (congrArg Units.val h₂)
  rintro ⟨h01, h10, hd⟩
  apply hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  rw [Matrix.det_fin_two, h01, h10, ← hd] at hdet
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, hd]

end Matrices

section TorusAction

variable {F : Type} [Field F]

private theorem exists_conj_J_one (h2 : (2 : F) ≠ 0) (D₀ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hD : D₀ * D₀ = -1) :
    ∃ P : GL (Fin 2) F, Matrix.SpecialLinearGroup.toGL D₀ * P = P * MatrixCoverData.J F 1 := by
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : F, (D₀ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := D₀.2
    rw [hm, Matrix.det_fin_two_of] at this
    exact this
  have hsq : (D₀ : Matrix (Fin 2) (Fin 2) F) * D₀ = -1 := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
      (X : Matrix (Fin 2) (Fin 2) F)) hD
    simpa using this
  rw [hm] at hsq
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e11 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have htr : d = -a := by
    have h : (a + d) ^ 2 = 0 := by linear_combination e00 + e11 + 2 * hdet
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linear_combination this
  subst htr
  have key : ∀ Q : Matrix (Fin 2) (Fin 2) F, (hQ : Q.det ≠ 0) →
      !![a, b; c, -a] * Q = Q * !![0, -1; 1, 0] →
      ∃ P : GL (Fin 2) F, Matrix.SpecialLinearGroup.toGL D₀ * P = P * MatrixCoverData.J F 1 := by
    intro Q hQ h
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQ, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul, MatrixCoverData.J_matrix]
    change (D₀ : Matrix (Fin 2) (Fin 2) F) * Q = Q * _
    rw [hm, Units.val_one]
    exact h
  by_cases hc : c = 0
  · subst hc
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by
        intro ha
        rw [ha] at e00
        apply one_ne_zero (α := F)
        linear_combination e00
      refine key !![1, a; 1, -a] ?_ ?_
      · rw [Matrix.det_fin_two_of]
        intro h
        apply ha
        have h' : (2 : F) * a = 0 := by linear_combination -h
        exact (mul_eq_zero.mp h').resolve_left h2
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination e00
    · refine key !![0, b; 1, -a] ?_ ?_
      · rw [Matrix.det_fin_two_of]; simpa using hb
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination e00
  · refine key !![1, a; 0, c] ?_ ?_
    · rw [Matrix.det_fin_two_of]; simpa using hc
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination e00


private theorem anticomm_J_torus (g : Matrix (Fin 2) (Fin 2) F)
    (hg : g * !![0, -1; 1, 0] = -(!![0, -1; 1, 0] * g)) (x y : F) :
    g * !![x, -y; y, x] = !![x, y; -y, x] * g := by
  obtain ⟨α, β, γ, δ, rfl⟩ : ∃ α β γ δ : F, g = !![α, β; γ, δ] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at hg
  have e00 := congrFun (congrFun hg 0) 0
  have e01 := congrFun (congrFun hg 0) 1
  simp at e00 e01
  have hδ : δ = -α := by linear_combination -e01
  subst e00 hδ
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem torus_one_cyclic [Finite F] (h2 : (2 : F) ≠ 0) :
    IsCyclic (MatrixTorus.Torus F 1) := by
  by_cases hs : IsSquare (-((1 : Fˣ) : F))
  · exact MatrixTorus.split_torus_cyclic F 1 h2 hs
  · exact MatrixTorus.nonsplit_torus_cyclic F 1 hs

private theorem torus_one_card [Finite F] (h2 : (2 : F) ≠ 0) :
    (IsSquare (-1 : F) → Nat.card (MatrixTorus.Torus F 1) = Nat.card F - 1) ∧
      (¬ IsSquare (-1 : F) → Nat.card (MatrixTorus.Torus F 1) = Nat.card F + 1) :=
  ⟨fun hs => MatrixTorus.split_torus_card F 1 h2 (by simpa using hs),
    fun hs => MatrixTorus.nonsplit_torus_card F 1 (by simpa using hs)⟩

private theorem card_eq_card_fixed_pow [Finite F] (τ : F ≃+* F) :
    Nat.card F = Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) ^ orderOf τ := by
  have : IsGaloisGroup (Subgroup.zpowers τ) (FixedPoints.subfield (Subgroup.zpowers τ) F) F :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers τ) F
  have hdeg : Module.finrank (FixedPoints.subfield (Subgroup.zpowers τ) F) F = orderOf τ := by
    rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers τ)
      (FixedPoints.subfield (Subgroup.zpowers τ) F) F, Nat.card_zpowers]
  rw [← hdeg]
  exact Module.natCard_eq_pow_finrank

private theorem mem_fixed_of_apply_eq (τ : F ≃+* F) {c : F} (hc : τ c = c) :
    c ∈ FixedPoints.subfield (Subgroup.zpowers τ) F := by
  intro ρ
  have hle : Subgroup.zpowers τ ≤ MulAction.stabilizer (F ≃+* F) c := by
    rw [Subgroup.zpowers_le]
    exact hc
  exact hle ρ.2

private theorem isSquare_neg_one_fixed_iff [Finite F] (τ : F ≃+* F) (hτ : Odd (orderOf τ)) :
    IsSquare (-1 : FixedPoints.subfield (Subgroup.zpowers τ) F) ↔ IsSquare (-1 : F) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hA : Odd (Nat.card (Subgroup.zpowers τ)) := by rwa [Nat.card_zpowers]
    have hfix := MatrixCover.square_root_fixed F (Subgroup.zpowers τ) hA (-1) b (by
      rw [sq, ← hb]
      simp)
    refine ⟨⟨b, fun ρ => hfix ρ⟩, Subtype.ext ?_⟩
    simpa using hb

private theorem exists_fixed_lift (τ : F ≃+* F) (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hX : Matrix.SpecialLinearGroup.map τ.toRingHom X = X) :
    ∃ X₀ : Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield (Subgroup.zpowers τ) F),
      Matrix.SpecialLinearGroup.map (FixedPoints.subfield (Subgroup.zpowers τ) F).subtype X₀ =
        X := by
  have hfix : ∀ i j, (X : Matrix (Fin 2) (Fin 2) F) i j ∈
      FixedPoints.subfield (Subgroup.zpowers τ) F := by
    intro i j
    apply mem_fixed_of_apply_eq τ
    have := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) F =>
      (Y : Matrix (Fin 2) (Fin 2) F) i j) hX
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
  let M : Matrix (Fin 2) (Fin 2) (FixedPoints.subfield (Subgroup.zpowers τ) F) :=
    Matrix.of fun i j => ⟨_, hfix i j⟩
  have hM : (FixedPoints.subfield (Subgroup.zpowers τ) F).subtype.mapMatrix M = X := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply Subtype.val_injective
    change (FixedPoints.subfield (Subgroup.zpowers τ) F).subtype M.det = 1
    rw [RingHom.map_det, hM]
    exact X.2
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

private theorem exists_prime_dvd_pow_sub {x y : ℤ} (hx : Odd x) (hy : y = 1 ∨ y = -1)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hsize : (r : ℤ) * |x - y| < |x ^ r - y ^ r|) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ r ∧ (ℓ : ℤ) ∣ x ^ r - y ^ r ∧ ¬ (ℓ : ℤ) ∣ x - y := by
  have : Fact r.Prime := ⟨hr⟩
  set Φ := ∑ i ∈ Finset.range r, x ^ i * y ^ (r - 1 - i) with hΦ
  have hfac : Φ * (x - y) = x ^ r - y ^ r := geom_sum₂_mul x y r
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hy2 : y ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hyr : y ^ (r - 1) = 1 := by
    obtain ⟨k, hk⟩ := hrodd
    rw [show r - 1 = 2 * k by omega, pow_mul, hy2, one_pow]
  have hyodd : Odd y := by rcases hy with rfl | rfl <;> decide
  have hxy : 0 < |x - y| := by
    rcases (abs_nonneg (x - y)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hxy' : x = y := sub_eq_zero.mp (abs_eq_zero.mp h.symm)
      rw [hxy'] at hsize
      simp at hsize
  have hΦbig : (r : ℤ) < |Φ| := by
    rw [← hfac, abs_mul] at hsize
    exact lt_of_mul_lt_mul_right hsize hxy.le
  have hred : ∀ m : ℤ, m ∣ x - y → (m ∣ Φ ↔ m ∣ r) := by
    intro m hm
    rw [hΦ, dvd_geom_sum₂_iff_of_dvd_sub hm, hyr, mul_one]
  have h2xy : (2 : ℤ) ∣ x - y := (hx.sub_odd hyodd).two_dvd
  have hΦodd : ¬ (2 : ℤ) ∣ Φ := by
    rw [hred 2 h2xy]
    intro h
    have h' : (2 : ℕ) ∣ r := by exact_mod_cast h
    exact (Nat.not_even_iff_odd.mpr hrodd) (even_iff_two_dvd.mpr h')
  have hrsq : ¬ ((r : ℤ) ^ 2 ∣ Φ) := by
    intro h
    have hrΦ : (r : ℤ) ∣ Φ := (dvd_pow_self (r : ℤ) two_ne_zero).trans h
    have hrxy : (r : ℤ) ∣ x - y := by
      have h1 : (r : ℤ) ∣ x ^ r - y ^ r := hfac ▸ dvd_mul_of_dvd_left hrΦ _
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 ⊢
      push_cast at h1 ⊢
      rwa [ZMod.pow_card, ZMod.pow_card] at h1
    obtain ⟨b, hb⟩ := hrxy
    have hxb : x = y + r * b := by linear_combination hb
    have hcong := odd_sq_dvd_geom_sum₂_sub y b hrodd
    rw [← hxb, ← hΦ, hyr, mul_one] at hcong
    have h3 : (r : ℤ) ^ 2 ∣ r := by
      have := dvd_sub h hcong
      simpa using this
    have h4 : (r : ℤ) ∣ 1 := by
      have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne_zero
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by
        have : (r : ℤ) * 1 = r * (r * c) := by linear_combination hc
        exact (mul_left_cancel₀ hr0 this)⟩
    have h5 : r ∣ 1 := by exact_mod_cast h4
    exact hr.one_lt.ne' (Nat.dvd_one.mp h5)
  have hM0 : Φ.natAbs ≠ 0 := by
    intro h
    rw [Int.natAbs_eq_zero] at h
    rw [h, abs_zero] at hΦbig
    exact absurd hΦbig (not_lt.mpr (Int.natCast_nonneg r))
  obtain ⟨e, M, hrM, hM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 r hr.one_lt.ne'
  have he : e ≤ 1 := by
    by_contra he
    apply hrsq
    have h1 : r ^ 2 ∣ Φ.natAbs := hM ▸ dvd_mul_of_dvd_left (pow_dvd_pow r (by omega)) _
    have h2 : ((r ^ 2 : ℕ) : ℤ) ∣ Φ := Int.natCast_dvd.mpr h1
    exact_mod_cast h2
  have hM1 : M ≠ 1 := by
    rintro rfl
    rw [mul_one] at hM
    have h1 : Φ.natAbs ≤ r := by
      rw [hM]
      calc r ^ e ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos he
        _ = r := pow_one r
    have h2 : |Φ| ≤ r := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h1
    exact absurd hΦbig (not_lt.mpr h2)
  set ℓ := M.minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime hM1
  have hℓM : ℓ ∣ M := Nat.minFac_dvd M
  have hℓΦ : (ℓ : ℤ) ∣ Φ := by
    apply Int.natCast_dvd.mpr
    rw [hM]
    exact dvd_mul_of_dvd_right hℓM _
  have hℓr : ℓ ≠ r := by
    intro h
    rw [h] at hℓM
    exact hrM hℓM
  refine ⟨ℓ, hℓp, ?_, hℓr, hfac ▸ dvd_mul_of_dvd_left hℓΦ _, ?_⟩
  · intro h
    rw [h] at hℓΦ
    exact hΦodd (by exact_mod_cast hℓΦ)
  · intro h
    have h1 := (hred ℓ h).mp hℓΦ
    have h2 : ℓ ∣ r := by exact_mod_cast h1
    exact hℓr ((Nat.prime_dvd_prime_iff_eq hℓp hr).mp h2)

private theorem two_mul_mul_le_pow {q r : ℕ} (hq : 3 ≤ q) (hr : 3 ≤ r) : 2 * r * q ≤ q ^ r := by
  have h3 : ∀ k : ℕ, 2 * (k + 3) ≤ 3 ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      have : 1 ≤ 3 ^ (k + 2) := Nat.one_le_pow _ _ (by norm_num)
      omega
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  calc 2 * (k + 3) * q ≤ 3 ^ (k + 2) * q := Nat.mul_le_mul_right _ (h3 k)
    _ ≤ q ^ (k + 2) * q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq _)
    _ = q ^ (k + 3) := by ring

private theorem exists_prime_dvd_torus {q₀ r : ℕ} (hq : Odd q₀) (h3 : 3 ≤ q₀) (hr : r.Prime)
    (hr2 : r ≠ 2) :
    (∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ r ∧ ℓ ∣ q₀ ^ r - 1 ∧ ¬ ℓ ∣ q₀ - 1) ∧
      (∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ r ∧ ℓ ∣ q₀ ^ r + 1 ∧ ¬ ℓ ∣ q₀ + 1) := by
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    rcases (show r = 2 ∨ 3 ≤ r by omega) with h | h
    · exact absurd h hr2
    · exact h
  have hbig := two_mul_mul_le_pow h3 hr3
  have hodd : Odd (q₀ : ℤ) := by exact_mod_cast hq
  have hpow1 : 1 ≤ q₀ ^ r := Nat.one_le_pow _ _ (by omega)
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  constructor
  · obtain ⟨ℓ, hℓ, hℓ2, hℓr, hdvd, hndvd⟩ := exists_prime_dvd_pow_sub hodd (Or.inl rfl) hr hr2
      (by
        rw [one_pow, abs_of_nonneg (by omega), abs_of_nonneg (by
          have : (1 : ℤ) ≤ (q₀ : ℤ) ^ r := by exact_mod_cast hpow1
          linarith)]
        have : (2 * r * q₀ : ℤ) ≤ (q₀ : ℤ) ^ r := by exact_mod_cast hbig
        have : (3 * r : ℤ) ≤ r * q₀ := by
          have : (3 : ℤ) ≤ q₀ := by exact_mod_cast h3
          nlinarith
        nlinarith)
    refine ⟨ℓ, hℓ, hℓ2, hℓr, ?_, ?_⟩
    · have : ((q₀ ^ r - 1 : ℕ) : ℤ) = (q₀ : ℤ) ^ r - 1 ^ r := by
        rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one, one_pow]
      exact Int.natCast_dvd_natCast.mp (this ▸ hdvd)
    · intro h
      apply hndvd
      have : ((q₀ - 1 : ℕ) : ℤ) = (q₀ : ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q₀ by omega), Nat.cast_one]
      exact this ▸ Int.natCast_dvd_natCast.mpr h
  · obtain ⟨ℓ, hℓ, hℓ2, hℓr, hdvd, hndvd⟩ := exists_prime_dvd_pow_sub hodd (Or.inr rfl) hr hr2
      (by
        rw [hrodd.neg_one_pow, sub_neg_eq_add, sub_neg_eq_add,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        have : (2 * r * q₀ : ℤ) ≤ (q₀ : ℤ) ^ r := by exact_mod_cast hbig
        have : (3 * r : ℤ) ≤ r * q₀ := by
          have : (3 : ℤ) ≤ q₀ := by exact_mod_cast h3
          nlinarith
        nlinarith)
    refine ⟨ℓ, hℓ, hℓ2, hℓr, ?_, ?_⟩
    · have : ((q₀ ^ r + 1 : ℕ) : ℤ) = (q₀ : ℤ) ^ r - (-1) ^ r := by
        rw [hrodd.neg_one_pow]; push_cast; ring
      exact Int.natCast_dvd_natCast.mp (this ▸ hdvd)
    · intro h
      apply hndvd
      have : ((q₀ + 1 : ℕ) : ℤ) = (q₀ : ℤ) - (-1) := by push_cast; ring
      exact this ▸ Int.natCast_dvd_natCast.mpr h

private theorem exists_torus_element [Finite F] (hodd : Odd (Nat.card F)) (τ : F ≃+* F)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hτ : orderOf τ = r)
    (D₀ : Matrix.SpecialLinearGroup (Fin 2) F) (hD₀ : D₀ * D₀ = -1) (h g : GL (Fin 2) F)
    (hh : h * Matrix.GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL D₀) *
      h⁻¹ = Matrix.SpecialLinearGroup.toGL D₀)
    (hg : g * Matrix.SpecialLinearGroup.toGL D₀ * g⁻¹ = (Matrix.SpecialLinearGroup.toGL D₀)⁻¹)
    (ψ ψs : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hψ : ∀ Z, Matrix.SpecialLinearGroup.toGL (ψ Z) =
      h * Matrix.GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL Z) * h⁻¹)
    (hψs : ∀ Z, Matrix.SpecialLinearGroup.toGL (ψs Z) =
      g * Matrix.SpecialLinearGroup.toGL Z * g⁻¹) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ r ∧ ∃ K : Matrix.SpecialLinearGroup (Fin 2) F,
      orderOf K = ℓ ∧ ψ K ∈ Subgroup.zpowers K ∧ ψ K ≠ K ∧ ψs K = K⁻¹ := by
  classical
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨P, hP⟩ := exists_conj_J_one h2 D₀ hD₀
  have hD : Matrix.SpecialLinearGroup.toGL D₀ = P * MatrixCoverData.J F 1 * P⁻¹ := by
    rw [← hP, mul_inv_cancel_right]
  have hJτ : Matrix.GeneralLinearGroup.map τ.toRingHom (MatrixCoverData.J F 1) =
      MatrixCoverData.J F 1 := by
    rw [MatrixCoverData.field_map_J, map_one]
  have hJns : ¬ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = MatrixCoverData.J F 1 := by
    rintro ⟨c, hc⟩
    have h01 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    simp [Matrix.GeneralLinearGroup.coe_scalar, MatrixCoverData.J_matrix] at h01
  have hcard : Nat.card F = Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) ^ r :=
    hτ ▸ card_eq_card_fixed_pow τ
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hF₀odd : Odd (Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F)) := by
    rw [hcard] at hodd
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_pow.mpr ⟨hev, hr.ne_zero⟩)
  have hF₀3 : 3 ≤ Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) := by
    have : 1 < Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hF₀odd
    omega
  have h2₀ : (2 : FixedPoints.subfield (Subgroup.zpowers τ) F) ≠ 0 :=
    OddFieldSL2.two_ne_zero_of_odd_card _ hF₀odd
  have hsq := isSquare_neg_one_fixed_iff τ (hτ ▸ hrodd)
  obtain ⟨ℓ, hℓ, hℓ2, hℓr, hℓT, hℓT₀⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ r ∧
      ℓ ∣ Nat.card (MatrixTorus.Torus F 1) ∧
        ¬ ℓ ∣ Nat.card (MatrixTorus.Torus (FixedPoints.subfield (Subgroup.zpowers τ) F) 1) := by
    obtain ⟨hm, hp⟩ := exists_prime_dvd_torus hF₀odd hF₀3 hr hr2
    by_cases hs : IsSquare (-1 : F)
    · rw [(torus_one_card h2).1 hs, (torus_one_card h2₀).1 (hsq.mpr hs), hcard]
      exact hm
    · rw [(torus_one_card h2).2 hs, (torus_one_card h2₀).2 (fun h => hs (hsq.mp h)), hcard]
      exact hp
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K', hK'⟩ := exists_prime_orderOf_dvd_card' ℓ hℓT
  have hτ1 : τ ((1 : Fˣ) : F) = ((1 : Fˣ) : F) := by simp
  set τK' := MatrixTorus.torusFieldEquiv F 1 τ hτ1 K' with hτK'
  have hτK'ord : orderOf τK' = ℓ := by rw [hτK', MulEquiv.orderOf_eq, hK']
  have hτK'val : (τK' : Matrix.SpecialLinearGroup (Fin 2) F) =
      Matrix.SpecialLinearGroup.map τ.toRingHom K' := rfl
  have hmove : τK' ≠ K' := by
    intro heq
    have hX : Matrix.SpecialLinearGroup.map τ.toRingHom (K' : Matrix.SpecialLinearGroup (Fin 2) F) =
        K' := by rw [← hτK'val, heq]
    obtain ⟨X₀, hX₀⟩ := exists_fixed_lift τ _ hX
    have e : ∀ i j, (((X₀ : Matrix (Fin 2) (Fin 2) _) i j :
        FixedPoints.subfield (Subgroup.zpowers τ) F) : F) =
        ((K' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
      intro i j
      rw [← hX₀]
      rfl
    have hX₀T : X₀ ∈ MatrixTorus.Torus (FixedPoints.subfield (Subgroup.zpowers τ) F) 1 := by
      obtain ⟨h01, h11⟩ := (MatrixTorus.mem_torus_iff F 1 K').mp K'.2
      rw [MatrixTorus.mem_torus_iff]
      constructor
      · apply Subtype.ext
        rw [e]
        simp only [Subfield.coe_mul, Subfield.coe_neg, Units.val_one, OneMemClass.coe_one, e]
        simpa using h01
      · apply Subtype.ext
        rw [e, e]
        exact h11
    have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        (FixedPoints.subfield (Subgroup.zpowers τ) F).subtype) := by
      intro A B hAB
      apply Subtype.ext
      ext i j
      have := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) F =>
        (Y : Matrix (Fin 2) (Fin 2) F) i j) hAB
      exact this
    have hord : orderOf (⟨X₀, hX₀T⟩ :
        MatrixTorus.Torus (FixedPoints.subfield (Subgroup.zpowers τ) F) 1) = ℓ := by
      rw [Subgroup.orderOf_mk, ← orderOf_injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        (FixedPoints.subfield (Subgroup.zpowers τ) F).subtype) hinj X₀, hX₀,
        Subgroup.orderOf_coe, hK']
    exact hℓT₀ (hord ▸ orderOf_dvd_natCard _)
  have := torus_one_cyclic h2
  obtain ⟨j, hj⟩ : ∃ j : ℤ, K' ^ j = τK' := by
    have heq : Subgroup.zpowers K' = Subgroup.zpowers τK' :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hK', hτK'ord])
    exact Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers τK')
  have hTJ : ∀ X : MatrixTorus.Torus F 1, MatrixCoverData.J F 1 *
      Matrix.SpecialLinearGroup.toGL (X : Matrix.SpecialLinearGroup (Fin 2) F) =
      Matrix.SpecialLinearGroup.toGL (X : Matrix.SpecialLinearGroup (Fin 2) F) *
        MatrixCoverData.J F 1 := by
    intro X
    have := X.2
    change Matrix.SpecialLinearGroup.toGL (X : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      Subgroup.centralizer {MatrixCoverData.J F 1} at this
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  set c := MatrixCoverData.slConjugation F P with hc
  have hcK : ∀ X, Matrix.SpecialLinearGroup.toGL (c X) =
      P * Matrix.SpecialLinearGroup.toGL X * P⁻¹ := MatrixCoverData.slConjugation_toGL F P
  have hψK : ψ (c K') = c τK' := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hψ, hcK, hcK, hτK'val, MatrixCoverData.toGL_field_map, map_mul, map_mul, map_inv]
    set Y := Matrix.GeneralLinearGroup.map τ.toRingHom
      (Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F))
    set τP := Matrix.GeneralLinearGroup.map τ.toRingHom P
    have hh' : MatrixCoverData.J F 1 * (P⁻¹ * h * τP) = (P⁻¹ * h * τP) * MatrixCoverData.J F 1 := by
      have h1 : Matrix.GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL D₀) =
          τP * MatrixCoverData.J F 1 * τP⁻¹ := by
        rw [hD, map_mul, map_mul, map_inv, hJτ]
      rw [h1, hD] at hh
      calc MatrixCoverData.J F 1 * (P⁻¹ * h * τP)
          = P⁻¹ * (P * MatrixCoverData.J F 1 * P⁻¹) * h * τP := by group
        _ = P⁻¹ * (h * (τP * MatrixCoverData.J F 1 * τP⁻¹) * h⁻¹) * h * τP := by rw [hh]
        _ = (P⁻¹ * h * τP) * MatrixCoverData.J F 1 := by group
    have hY : MatrixCoverData.J F 1 * Y = Y * MatrixCoverData.J F 1 := by
      have := hTJ τK'
      rwa [hτK'val, MatrixCoverData.toGL_field_map] at this
    have hcomm := gl_commute_of_commute_nonscalar hJns hh' hY
    calc h * (τP * Y * τP⁻¹) * h⁻¹ = P * ((P⁻¹ * h * τP) * Y) * (P⁻¹ * h * τP)⁻¹ * P⁻¹ := by
          group
      _ = P * (Y * (P⁻¹ * h * τP)) * (P⁻¹ * h * τP)⁻¹ * P⁻¹ := by rw [hcomm]
      _ = P * Y * P⁻¹ := by group
  refine ⟨ℓ, hℓ, hℓ2, hℓr, c K', ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hK']
  · rw [hψK, ← hj, Subgroup.coe_zpow, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  · rw [hψK]
    intro heq
    exact hmove (Subtype.ext (c.injective heq))
  ·
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hψs, map_inv, hcK]
    obtain ⟨x, y, hxy, -⟩ := (MatrixTorus.torus_coordinates F 1 K').mp K'.2
    have hg' : ((P⁻¹ * g * P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] =
        -(!![0, -1; 1, 0] * ((P⁻¹ * g * P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
      have hJinv : (((MatrixCoverData.J F 1)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          -!![0, -1; 1, 0] := by
        rw [Matrix.coe_units_inv, MatrixCoverData.J_matrix]
        apply Matrix.inv_eq_right_inv
        rw [Matrix.mul_neg, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have h1 : (P⁻¹ * g * P) * MatrixCoverData.J F 1 =
          (MatrixCoverData.J F 1)⁻¹ * (P⁻¹ * g * P) := by
        rw [hD] at hg
        calc (P⁻¹ * g * P) * MatrixCoverData.J F 1
            = P⁻¹ * (g * (P * MatrixCoverData.J F 1 * P⁻¹) * g⁻¹) * (P * P⁻¹ * g * P) := by
              group
          _ = P⁻¹ * (P * MatrixCoverData.J F 1 * P⁻¹)⁻¹ * (P * P⁻¹ * g * P) := by rw [hg]
          _ = (MatrixCoverData.J F 1)⁻¹ * (P⁻¹ * g * P) := by group
      have h2 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) h1
      simp only [Units.val_mul] at h2
      rw [hJinv, MatrixCoverData.J_matrix, Units.val_one] at h2
      simp only [Units.val_mul]
      rw [h2, Matrix.neg_mul]
    have hK'm : ((Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![x, -y; y, x] := by
      rw [show ((Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ((K' : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) from rfl, hxy, MatrixTorus.torusMatrix]
      simp
    have hK'inv : (((Matrix.SpecialLinearGroup.toGL
        (K' : Matrix.SpecialLinearGroup (Fin 2) F))⁻¹ : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = !![x, y; -y, x] := by
      rw [← map_inv, show ((Matrix.SpecialLinearGroup.toGL
        ((K' : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = (((K' : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ :
            Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
        Matrix.SpecialLinearGroup.coe_inv, hxy, MatrixTorus.torusMatrix,
        Matrix.adjugate_fin_two_of]
      simp
    have hkey : (P⁻¹ * g * P) * Matrix.SpecialLinearGroup.toGL
        (K' : Matrix.SpecialLinearGroup (Fin 2) F) =
        (Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F))⁻¹ *
          (P⁻¹ * g * P) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul ((Matrix.SpecialLinearGroup.toGL
        (K' : Matrix.SpecialLinearGroup (Fin 2) F))⁻¹), hK'm, hK'inv]
      exact anticomm_J_torus _ hg' x y
    calc g * (P * Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F) *
          P⁻¹) * g⁻¹
        = P * ((P⁻¹ * g * P) * Matrix.SpecialLinearGroup.toGL
            (K' : Matrix.SpecialLinearGroup (Fin 2) F)) * (P⁻¹ * g * P)⁻¹ * P⁻¹ := by group
      _ = P * ((Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F))⁻¹ *
            (P⁻¹ * g * P)) * (P⁻¹ * g * P)⁻¹ * P⁻¹ := by rw [hkey]
      _ = (P * Matrix.SpecialLinearGroup.toGL (K' : Matrix.SpecialLinearGroup (Fin 2) F) *
            P⁻¹)⁻¹ := by group

end TorusAction

private theorem eq_of_comp_eq_of_perfect {Y E Q : Type*} [Group Y] [Group E] [Group Q]
    [Group.IsPerfect Y] {π : E →* Q} (hcen : π.ker ≤ Subgroup.center E)
    {β₁ β₂ : Y →* E} (h : ∀ y, π (β₁ y) = π (β₂ y)) : β₁ = β₂ := by
  have hmem : ∀ x, β₁ x * (β₂ x)⁻¹ ∈ Subgroup.center E := fun x => hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel])
  let γ : Y →* Subgroup.center E :=
    { toFun := fun x => ⟨β₁ x * (β₂ x)⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hc := Subgroup.mem_center_iff.1 (hmem y)
        change β₁ (x * y) * (β₂ (x * y))⁻¹ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        calc β₁ x * β₁ y * ((β₂ y)⁻¹ * (β₂ x)⁻¹)
            = β₁ x * ((β₁ y * (β₂ y)⁻¹) * (β₂ x)⁻¹) := by group
          _ = β₁ x * ((β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹)) := by rw [← hc]
          _ = β₁ x * (β₂ x)⁻¹ * (β₁ y * (β₂ y)⁻¹) := by group) }
  have hγ : ∀ x, γ x = 1 := by
    intro x
    have hx : x ∈ commutator Y := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact Abelianization.commutator_subset_ker γ hx
  ext x
  have := congrArg Subtype.val (hγ x)
  simp only [γ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  exact mul_inv_eq_one.1 this

variable {G : Type} [Group G]

private theorem layer_centralizer_commute (t : G) {F : Type} [Field F] [Finite F]
    (hF4 : 4 ≤ Nat.card F) (A : Subgroup (F ≃+* F)) (hAodd : Odd (Nat.card A))
    (rho : Gamma t →* coordinateE F) (hinj : Function.Injective rho)
    (hrange : rho.range = OddFieldLift.Gamma F A)
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t),
      (rho (barKappa t x)).val =
        coordinatePSLAction F (ProjectiveSL2Cover.nativeQuotient F (eta x)))
    (s : C t) (hs2 : s ^ 2 = 1) (hsZ : kappa t s ≠ 1)
    (y₁ y₂ : H t) (hy₁ : y₁ ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hy₂ : y₂ ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t))
    (hc₁ : nu t s * y₁ = y₁ * nu t s) (hc₂ : nu t s * y₂ = y₂ * nu t s) :
    y₁ * y₂ = y₂ * y₁ := by
  classical
  let Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  have hYn : Y.Normal := Subgroup.Normal.comap inferInstance _
  have hF4' : ∃ u : Finset F, u.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
    exact ⟨u, hu⟩
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4'
  have : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  set gs : OddFieldLift.Gamma F A := ⟨rho (kappa t s), hrange ▸ ⟨kappa t s, rfl⟩⟩ with hgs
  have hgs2 : gs ^ 2 = 1 := by
    apply Subtype.ext
    change rho (kappa t s) ^ 2 = 1
    rw [← map_pow, ← map_pow, hs2, map_one, map_one]
  have hD : (rho (kappa t s) : Equiv.Perm (Omega F)) ∈ coordinateD F :=
    MatrixCover.gamma_involution_mem_linear F A hAodd gs hgs2
  obtain ⟨g, hg⟩ := Principal.exists_coordinateGLAction_eq hD
  let cY : Y →* Y := MonoidHom.codRestrict ((MulAut.conj (nu t s)).toMonoidHom.comp Y.subtype) Y
    (fun y => hYn.conj_mem _ y.2 _)
  let β₁ : Y →* GL (Fin 2) F := (Matrix.SpecialLinearGroup.toGL.comp eta.toMonoidHom).comp cY
  let β₂ : Y →* GL (Fin 2) F :=
    (MulAut.conj g).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp eta.toMonoidHom)
  have hcen : (coordinateGLAction F).ker ≤ Subgroup.center (GL (Fin 2) F) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    apply coordinatePGLAction_injective F
    rw [map_one]
    exact hx
  have hπ : ∀ y, coordinateGLAction F (β₁ y) = coordinateGLAction F (β₂ y) := by
    intro y
    have h1 : coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta (cY y))) =
        (rho (barKappa t (cY y : H t))).val := by
      rw [Principal.coordinateGLAction_toGL]
      exact (heta (cY y)).symm
    have h2 : coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta y)) =
        (rho (barKappa t (y : H t))).val := by
      rw [Principal.coordinateGLAction_toGL]
      exact (heta y).symm
    change coordinateGLAction F (Matrix.SpecialLinearGroup.toGL (eta (cY y))) =
      coordinateGLAction F (g * Matrix.SpecialLinearGroup.toGL (eta y) * g⁻¹)
    rw [map_mul, map_mul, map_inv, hg, h1, h2]
    change (rho (barKappa t (nu t s * (y : H t) * (nu t s)⁻¹))).val = _
    rw [map_mul, map_mul, map_inv, barKappa_nu, map_mul, map_mul, map_inv]
    rfl
  have hβ := eq_of_comp_eq_of_perfect hcen hπ
  have hgns : ¬ ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c = g := by
    rintro ⟨c, rfl⟩
    apply hsZ
    apply hinj
    rw [map_one]
    apply Subtype.ext
    rw [← hg, Principal.coordinateGLAction_scalar]
    rfl
  have hcomm : ∀ (y : H t) (hy : y ∈ Y), nu t s * y = y * nu t s →
      g * Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) =
        Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) * g := by
    intro y hy hcy
    have hcY : cY ⟨y, hy⟩ = ⟨y, hy⟩ := by
      apply Subtype.ext
      change nu t s * y * (nu t s)⁻¹ = y
      rw [hcy, mul_inv_cancel_right]
    have h := DFunLike.congr_fun hβ ⟨y, hy⟩
    change Matrix.SpecialLinearGroup.toGL (eta (cY ⟨y, hy⟩)) =
      g * Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) * g⁻¹ at h
    rw [hcY] at h
    calc g * Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩)
        = g * Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) * g⁻¹ * g := by group
      _ = Matrix.SpecialLinearGroup.toGL (eta ⟨y, hy⟩) * g := by rw [← h]
  have hX := gl_commute_of_commute_nonscalar hgns (hcomm y₁ hy₁ hc₁) (hcomm y₂ hy₂ hc₂)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul] at hX
  have hXY := eta.injective (Matrix.SpecialLinearGroup.toGL_injective hX)
  exact congrArg Subtype.val hXY

private theorem frontier_L_le_L₀_sup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).L ≤
      (frontierSetting S fS t p f).L₀ ⊔ Subgroup.zpowers (fS (s n) : G) := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  refine sup_le le_sup_left ?_
  have hS : ((frontierSetting S fS t p f).S : Subgroup G) =
      Subgroup.closure {FocalFusion.ambientHom n (S : Subgroup G) fS (r n * s n),
        FocalFusion.ambientHom n (S : Subgroup G) fS (s n)} := by
    rw [← Set.image_pair, ← MonoidHom.map_closure, sd_closure_rs_s (by omega),
      ← MonoidHom.range_eq_map, FocalFusion.ambientHom_range]
    rfl
  rw [hS, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · apply Subgroup.mem_sup_left
    have hmem : FocalFusion.ambientHom n (S : Subgroup G) fS (r n * s n) ∈ C t :=
      frontier_S_le_C hn S fS t ht p f (fS (r n * s n)).property
    have hx4 : orderOf (⟨_, hmem⟩ : C t) = 4 := by
      rw [Subgroup.orderOf_mk, orderOf_ambientHom, orderOf_rs hn]
    exact ⟨_, actual_order_four_image_mem_layer n hn S fS hG t ht2 F A p f rho data _ hx4, rfl⟩
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

private theorem frontier_ON_le_solvRadIn_L {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).ON ≤ solvRadIn (frontierSetting S fS t p f).L := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hOL : (frontierSetting S fS t p f).ON ≤ (frontierSetting S fS t p f).L :=
    hσ.ON_le_L₀.trans le_sup_left
  have hLN := frontier_L_le_N hn S fS t ht p f
  have hMn : ((frontierSetting S fS t p f).ON.subgroupOf
      (frontierSetting S fS t p f).L).Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      ((frontierSetting S fS t p f).N_le_normalizer_ON (hLN l.2)) x).mp hx
  have hMsolv : Group.IsSolvable ((frontierSetting S fS t p f).ON.subgroupOf
      (frontierSetting S fS t p f).L) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOL).toEquiv]
    exact (frontierSetting S fS t p f).odd_card_ON
  have hle : (frontierSetting S fS t p f).ON.subgroupOf (frontierSetting S fS t p f).L ≤
      CFSG.solvableRadical (frontierSetting S fS t p f).L := le_sSup ⟨hMn, hMsolv⟩
  intro x hx
  exact ⟨⟨x, hOL hx⟩, hle hx, rfl⟩

theorem frontier_C_inf_L_commutator_le_ON {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ⁅(frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L,
        (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L⁆ ≤
      (frontierSetting S fS t p f).ON := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, heta, -⟩ := data.compatible_layer
  have hF4 : 4 ≤ Nat.card F := by
    rw [data.field_card]
    omega
  let s' : C t := ⟨(fS (s n) : G), hsC⟩
  have hs'2 : orderOf s' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hs2
  have hs't : s' ≠ tInC t := fun h => hst (congrArg Subtype.val h)
  obtain ⟨hNZK, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  have hsZ : kappa t s' ≠ 1 := fun h =>
    actual_noncentral_involution_not_mem_K n hn S fS hG t ht2 s' hs'2 hs't
      (hNZK ((QuotientGroup.eq_one_iff s').mp h))
  have hs'sq : s' ^ 2 = 1 := by
    rw [← hs'2]
    exact pow_orderOf_eq_one s'
  have hLs := frontier_L_le_L₀_sup hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hmodel
  have hcoe : (((frontierSetting S fS t p f).L₀ ⊔ Subgroup.zpowers (fS (s n) : G) :
      Subgroup G) : Set G) =
      ((frontierSetting S fS t p f).L₀ : Set G) * (Subgroup.zpowers (fS (s n) : G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr
      (hσ.N_le_normalizer_L₀ ((frontierSetting S fS t p f).x₂_mem_N hσ)))
  have hdecomp : ∀ c ∈ (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L,
      ∃ l : C t, l ∈ localLayerPreimage t ∧ s' * l = l * s' ∧
        ∃ k : ℤ, c = ((l * s' ^ k : C t) : G) := by
    intro c hc
    have hcs : (fS (s n) : G) * c = c * (fS (s n) : G) :=
      Subgroup.mem_centralizer_iff.mp hc.1 _ (frontierSetting S fS t p f).x₂_mem_T
    have hmem : c ∈ (((frontierSetting S fS t p f).L₀ ⊔ Subgroup.zpowers (fS (s n) : G) :
        Subgroup G) : Set G) := hLs hc.2
    rw [hcoe] at hmem
    obtain ⟨l, hl, w, hw, rfl⟩ := Set.mem_mul.mp hmem
    obtain ⟨l', hl', rfl⟩ := hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨l', hl', ?_, k, rfl⟩
    have hcomm : (s' : G) * (l' : G) * (s' : G) ^ k = (l' : G) * (s' : G) * (s' : G) ^ k := by
      calc (s' : G) * (l' : G) * (s' : G) ^ k = (s' : G) * ((l' : G) * (s' : G) ^ k) := by
            rw [mul_assoc]
        _ = (l' : G) * (s' : G) ^ k * (s' : G) := hcs
        _ = (l' : G) * (s' : G) * (s' : G) ^ k := by
            rw [mul_assoc, (Commute.self_zpow (s' : G) k).eq.symm, ← mul_assoc]
    exact Subtype.ext (mul_right_cancel hcomm)
  rw [Subgroup.commutator_le]
  intro c₁ hc₁ c₂ hc₂
  rw [frontierSetting_ON]
  obtain ⟨l₁, hl₁, hls₁, k₁, rfl⟩ := hdecomp c₁ hc₁
  obtain ⟨l₂, hl₂, hls₂, k₂, rfl⟩ := hdecomp c₂ hc₂
  refine ⟨⁅l₁ * s' ^ k₁, l₂ * s' ^ k₂⁆, ?_, rfl⟩
  have hy₁ : Commute (nu t s') (nu t l₁) := by
    change nu t s' * nu t l₁ = nu t l₁ * nu t s'
    rw [← map_mul, ← map_mul, hls₁]
  have hy₂ : Commute (nu t s') (nu t l₂) := by
    change nu t s' * nu t l₂ = nu t l₂ * nu t s'
    rw [← map_mul, ← map_mul, hls₂]
  have hy₁₂ : Commute (nu t l₁) (nu t l₂) :=
    layer_centralizer_commute t hF4 A data.field_group_odd rho data.faithful data.full_image
      eta heta s' hs'sq hsZ (nu t l₁) (nu t l₂) hl₁ hl₂ hy₁.eq hy₂.eq
  have hc : Commute (nu t (l₁ * s' ^ k₁)) (nu t (l₂ * s' ^ k₂)) := by
    rw [map_mul, map_mul, map_zpow, map_zpow]
    exact (hy₁₂.mul_right (hy₁.symm.zpow_right k₂)).mul_left
      ((hy₂.zpow_left k₁).mul_right (Commute.zpow_zpow_self _ k₁ k₂))
  change ⁅l₁ * s' ^ k₁, l₂ * s' ^ k₂⁆ ∈ N t
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact hc.eq

theorem frontier_C_inf_L_commutator {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ⁅(frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L,
        (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L⁆ ≤
      solvRadIn (frontierSetting S fS t p f).L :=
  (frontier_C_inf_L_commutator_le_ON hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel).trans
    (frontier_ON_le_solvRadIn_L hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
      hmodel)

theorem frontier_II42ii {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ⁅(frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀,
        (frontierSetting S fS t p f).C ⊓ (frontierSetting S fS t p f).L₀⁆ ≤
      (frontierSetting S fS t p f).ON :=
  (Subgroup.commutator_mono (inf_le_inf_left _ le_sup_left)
    (inf_le_inf_left _ le_sup_left)).trans
    (frontier_C_inf_L_commutator_le_ON hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel)

theorem frontier_C_odd {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ c ∈ (frontierSetting S fS t p f).C, Odd (orderOf c) →
      c ∈ oddCoreIn (frontierSetting S fS t p f).C := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  intro c hc hodd
  have hCeq := frontier_C_eq n hn S fS t ht p f
  rw [frontier_F₀_eq_T n hn S fS t ht p f] at hCeq
  have hTC := (frontierSetting S fS t p f).T_le_C hσ
  have hK : IsKleinFour (frontierSetting S fS t p f).T := by
    rw [frontierSetting_T hn S fS t ht p f]
    exact qdFour_isKleinFour hn _ fS
  have hcoe : ((oddCoreIn (frontierSetting S fS t p f).C ⊔ (frontierSetting S fS t p f).T :
      Subgroup G) : Set G) = (oddCoreIn (frontierSetting S fS t p f).C : Set G) *
        ((frontierSetting S fS t p f).T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hTC.trans (le_normalizer_oddCoreIn _))
  obtain ⟨k, hk⟩ := hodd
  have hdd : c ^ (k + 1) * c ^ (k + 1) = c := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  have hd : c ^ (k + 1) ∈ (((oddCoreIn (frontierSetting S fS t p f).C ⊔
      (frontierSetting S fS t p f).T : Subgroup G)) : Set G) := by
    rw [hCeq]
    exact Subgroup.pow_mem _ hc _
  rw [hcoe] at hd
  obtain ⟨o, ho, w, hw, how⟩ := Set.mem_mul.mp hd
  have hw2 : w * w = 1 := by
    have h := IsKleinFour.inv_eq_self (⟨w, hw⟩ : (frontierSetting S fS t p f).T)
    have h' := congrArg Subtype.val h
    change w⁻¹ = w at h'
    have h1 : w⁻¹ * w = 1 := inv_mul_cancel w
    rwa [h'] at h1
  rw [← hdd, ← how]
  have e : o * w * (o * w) = o * (w * o * w⁻¹) * (w * w) := by group
  rw [e, hw2, mul_one]
  exact Subgroup.mul_mem _ ho ((Subgroup.mem_normalizer_iff.mp
    (le_normalizer_oddCoreIn _ (hTC hw)) o).mp ho)

section Model

variable {F : Type} [Field F] (A : Subgroup (F ≃+* F)) (a : (MatrixCover.FixedField F A)ˣ)

private def modelSL :
    Matrix.SpecialLinearGroup (Fin 2) F →* MatrixCover.MatrixFieldModel F A a :=
  (SemidirectProduct.inl : MatrixCoverData.M F (MatrixCover.fixedUnit F A a) →*
    MatrixCover.MatrixFieldModel F A a).comp
      (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A a))

private theorem modelSL_injective : Function.Injective (modelSL A a) :=
  SemidirectProduct.inl_injective.comp (MatrixCoverData.inclusion_injective F _)

private def modelConj (x : MatrixCover.MatrixFieldModel F A a) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
  (MulAut.conj x.left.left).toMonoidHom.comp
    ((MatrixCoverData.action F (MatrixCover.fixedUnit F A a) x.left.right).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map (x.right : F ≃+* F).toRingHom))

private theorem model_mul_SL (x : MatrixCover.MatrixFieldModel F A a)
    (Z : Matrix.SpecialLinearGroup (Fin 2) F) :
    x * modelSL A a Z = modelSL A a (modelConj A a x Z) * x := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left]
      simp only [modelSL, modelConj, MonoidHom.comp_apply, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MatrixCoverData.inclusion,
        MatrixCover.matrixFieldAction_pair, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MulAut.one_apply]
      group
    · simp [modelSL, MatrixCoverData.inclusion, MatrixCover.matrixFieldAction_pair]
  · simp [modelSL]

private theorem modelSL_conj (x : MatrixCover.MatrixFieldModel F A a)
    (Z : Matrix.SpecialLinearGroup (Fin 2) F) :
    modelSL A a (modelConj A a x Z) = x * modelSL A a Z * x⁻¹ := by
  rw [model_mul_SL, mul_inv_cancel_right]

private def modelMat (x : MatrixCover.MatrixFieldModel F A a) : GL (Fin 2) F :=
  Matrix.SpecialLinearGroup.toGL x.left.left *
    MatrixCoverData.J F (MatrixCover.fixedUnit F A a) ^ MatrixCoverData.exponent x.left.right

private theorem modelConj_toGL (x : MatrixCover.MatrixFieldModel F A a)
    (Z : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL (modelConj A a x Z) =
      modelMat A a x * Matrix.GeneralLinearGroup.map (x.right : F ≃+* F).toRingHom
        (Matrix.SpecialLinearGroup.toGL Z) * (modelMat A a x)⁻¹ := by
  change Matrix.SpecialLinearGroup.toGL (x.left.left * MatrixCoverData.action F _ x.left.right
    (Matrix.SpecialLinearGroup.map (x.right : F ≃+* F).toRingHom Z) * x.left.left⁻¹) = _
  rw [map_mul, map_mul, map_inv, MatrixCoverData.action_toGL, MatrixCoverData.toGL_field_map,
    modelMat]
  group

private theorem modelConj_toGL_of_right (x : MatrixCover.MatrixFieldModel F A a)
    (hx : x.right = 1) (Z : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL (modelConj A a x Z) =
      modelMat A a x * Matrix.SpecialLinearGroup.toGL Z * (modelMat A a x)⁻¹ := by
  have h1 : Matrix.GeneralLinearGroup.map (x.right : F ≃+* F).toRingHom
      (Matrix.SpecialLinearGroup.toGL Z) = Matrix.SpecialLinearGroup.toGL Z := by
    rw [hx]
    apply Units.ext
    ext i j
    rfl
  rw [modelConj_toGL, h1]

end Model

section ModelFrontier

private theorem frontier_model {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (A : Subgroup (F ≃+* F))
      (a : (MatrixCover.FixedField F A)ˣ) (phi : MatrixCover.MatrixFieldModel F A a ≃* H t),
      Odd (Nat.card F) ∧ Odd (Nat.card A) ∧
      (∀ c : C t, c ∈ localLayerPreimage t ↔ ∃ X, phi (modelSL A a X) = nu t c) ∧
      phi (modelSL A a (-1)) = nu t (tInC t) ∧
      ∀ x : C t, orderOf x = 4 → x ∈ localLayerPreimage t := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  have hodd : Odd (Nat.card F) := by
    rw [data.field_card]
    exact hpodd.pow
  have hodd₀ : Odd (Nat.card (MatrixCover.FixedField F A)) := by
    rw [data.fixed_field_card]
    exact hpodd.pow
  obtain ⟨a, -, ha⟩ := ActualFourGroupCentralizer.odd_field_generator_nonsquare _ hodd₀
  obtain ⟨-, phi, hphit, hphiY, -⟩ := data.every_coefficient a ha
  refine ⟨F, hfield, hfinite, A, a, phi, hodd, data.field_group_odd, ?_, hphit, ?_⟩
  · intro c
    change nu t c ∈ (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ↔ _
    rw [← hphiY, MonoidHom.mem_range]
    rfl
  · intro x hx
    exact actual_order_four_image_mem_layer n hn S fS hG t ht2 F A p f rho data x hx

private theorem frontier_v_s {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∃ v₀ s₀ : C t, (v₀ : G) ∈ (frontierSetting S fS t p f).D ∧
      (s₀ : G) ∈ (frontierSetting S fS t p f).D ∧ (s₀ : G) = (frontierSetting S fS t p f).x₂ ∧
      orderOf v₀ = 4 ∧ v₀ * v₀ = tInC t ∧ s₀ * s₀ = 1 ∧ s₀ * v₀ * s₀⁻¹ = v₀⁻¹ := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, -, -, hsC, hs2, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have := sdFourSubgroup_isKleinFour hn
  have hvC : FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) ∈ C t :=
    frontier_S_le_C hn S fS t ht p f (fS _).property
  refine ⟨⟨_, hvC⟩, ⟨(fS (s n) : G), hsC⟩, ?_, (frontierSetting S fS t p f).T_le_D hσ
    (frontierSetting S fS t p f).x₂_mem_T, rfl, ?_, ?_, ?_, ?_⟩
  · rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  · rw [Subgroup.orderOf_mk, orderOf_ambientHom, orderOf_sdV hn]
  · apply Subtype.ext
    change FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) *
      FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) = t
    rw [← map_mul, ← pow_add, ht, map_pow]
    congr 1
    have h : 2 ^ (n - 2) = 2 ^ (n - 3) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    omega
  · apply Subtype.ext
    change (fS (s n) : G) * (fS (s n) : G) = 1
    have h := pow_orderOf_eq_one (fS (s n) : G)
    rw [hs2] at h
    rw [← sq]
    exact h
  · apply Subtype.ext
    change (fS (s n) : G) * FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) *
      (fS (s n) : G)⁻¹ = (FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)))⁻¹
    change FocalFusion.ambientHom n (S : Subgroup G) fS (s n) *
      FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)) *
        (FocalFusion.ambientHom n (S : Subgroup G) fS (s n))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, sd_s_conj_quarter hn, map_inv]

private theorem model_v_s {G : Type} [Group G] (t : G) {F : Type} [Field F]
    {A : Subgroup (F ≃+* F)} {a : (MatrixCover.FixedField F A)ˣ}
    (phi : MatrixCover.MatrixFieldModel F A a ≃* H t) (hA : Odd (Nat.card A))
    (hY : ∀ c : C t, c ∈ localLayerPreimage t ↔ ∃ X, phi (modelSL A a X) = nu t c)
    (hphit : phi (modelSL A a (-1)) = nu t (tInC t))
    (v₀ s₀ : C t) (hvL : v₀ ∈ localLayerPreimage t) (hv2 : v₀ * v₀ = tInC t)
    (hs2 : s₀ * s₀ = 1) (hsv : s₀ * v₀ * s₀⁻¹ = v₀⁻¹) :
    ∃ (D₀ : Matrix.SpecialLinearGroup (Fin 2) F) (xs : MatrixCover.MatrixFieldModel F A a),
      phi (modelSL A a D₀) = nu t v₀ ∧ phi xs = nu t s₀ ∧ xs.right = 1 ∧ D₀ * D₀ = -1 ∧
        modelConj A a xs D₀ = D₀⁻¹ := by
  obtain ⟨D₀, hD₀⟩ := (hY v₀).mp hvL
  have hxs : phi (phi.symm (nu t s₀)) = nu t s₀ := phi.apply_symm_apply _
  refine ⟨D₀, phi.symm (nu t s₀), hD₀, hxs, ?_, ?_, ?_⟩
  · have hxs2 : phi.symm (nu t s₀) * phi.symm (nu t s₀) = 1 := by
      rw [← map_mul, ← map_mul, hs2, map_one, map_one]
    have h := congrArg SemidirectProduct.right hxs2
    rw [SemidirectProduct.mul_right, SemidirectProduct.one_right] at h
    have hdvd : orderOf (phi.symm (nu t s₀)).right ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    have hodd : Odd (orderOf (phi.symm (nu t s₀)).right) := hA.of_dvd_nat (orderOf_dvd_natCard _)
    have h1 : orderOf (phi.symm (nu t s₀)).right = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  · apply modelSL_injective A a
    apply phi.injective
    rw [map_mul, map_mul, hD₀, ← map_mul, hv2, hphit]
  · apply modelSL_injective A a
    apply phi.injective
    rw [modelSL_conj, map_mul, map_mul, map_inv, hxs, hD₀, map_inv, map_inv, hD₀, ← map_inv,
      ← map_mul, ← map_mul, hsv, map_inv]

private theorem frontier_odd_mem_L₀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (y : G) (hyL : y ∈ (frontierSetting S fS t p f).L) (hyodd : Odd (orderOf y)) :
    y ∈ (frontierSetting S fS t p f).L₀ := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, -, -, -, hs2, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hLs := frontier_L_le_L₀_sup hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hmodel
  have hsN : Subgroup.zpowers (fS (s n) : G) ≤
      Subgroup.normalizer ((frontierSetting S fS t p f).L₀ : Set G) :=
    Subgroup.zpowers_le.mpr (hσ.N_le_normalizer_L₀ ((frontierSetting S fS t p f).x₂_mem_N hσ))
  have hcoe : (((frontierSetting S fS t p f).L₀ ⊔ Subgroup.zpowers (fS (s n) : G) :
      Subgroup G) : Set G) =
      ((frontierSetting S fS t p f).L₀ : Set G) * (Subgroup.zpowers (fS (s n) : G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hsN
  obtain ⟨k, hk⟩ := hyodd
  have hyy : y ^ (k + 1) * y ^ (k + 1) = y := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  have hu : y ^ (k + 1) ∈ (((frontierSetting S fS t p f).L₀ ⊔ Subgroup.zpowers (fS (s n) : G) :
      Subgroup G) : Set G) := hLs (Subgroup.pow_mem _ hyL _)
  rw [hcoe] at hu
  obtain ⟨l, hl, w, hw, hlw⟩ := Set.mem_mul.mp hu
  have hww : w * w = 1 := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : (fS (s n) : G) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (fS (s n) : G)
      rwa [hs2] at h
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_ofNat, h1, one_zpow]
  rw [← hyy, ← hlw]
  have e : l * w * (l * w) = l * (w * l * w⁻¹) * (w * w) := by group
  rw [e, hww, mul_one]
  exact Subgroup.mul_mem _ hl ((Subgroup.mem_normalizer_iff.mp (hsN hw) l).mp hl)

theorem frontier_II43iii {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ y ∈ (frontierSetting S fS t p f).L,
      y ∈ Subgroup.centralizer ((frontierSetting S fS t p f).D : Set G) → Odd (orderOf y) →
        y ∈ (frontierSetting S fS t p f).ON := by
  intro y hyL hyD hyodd
  obtain ⟨F, _, _, A, a, phi, hFodd, hAodd, hY, hphit, hL4⟩ :=
    frontier_model hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨v₀, s₀, hvD, hsD, -, hv4, hv2, hs2, hsv⟩ :=
    frontier_v_s hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  obtain ⟨D₀, xs, hD₀, hxs, hxs1, hD₀2, hxsD⟩ :=
    model_v_s t phi hAodd hY hphit v₀ s₀ (hL4 v₀ hv4) hv2 hs2 hsv
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hFodd
  have hyL₀ := frontier_odd_mem_L₀ hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel y hyL hyodd
  obtain ⟨y', hy'L, rfl⟩ := hyL₀
  obtain ⟨Y₀, hY₀⟩ := (hY y').mp hy'L
  have hyv : y' * v₀ = v₀ * y' :=
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hyD _ hvD).symm
  have hys : s₀ * y' * s₀⁻¹ = y' := by
    have h : y' * s₀ = s₀ * y' := Subtype.ext (Subgroup.mem_centralizer_iff.mp hyD _ hsD).symm
    rw [← h, mul_inv_cancel_right]
  have hYD : Y₀ * D₀ = D₀ * Y₀ := by
    apply modelSL_injective A a
    apply phi.injective
    rw [map_mul, map_mul, map_mul, map_mul, hY₀, hD₀, ← map_mul, ← map_mul, hyv]
  have hYs : modelConj A a xs Y₀ = Y₀ := by
    apply modelSL_injective A a
    apply phi.injective
    rw [modelSL_conj, map_mul, map_mul, map_inv, hxs, hY₀, ← map_inv, ← map_mul, ← map_mul, hys]
  have hg1 : modelMat A a xs * Matrix.SpecialLinearGroup.toGL Y₀ =
      Matrix.SpecialLinearGroup.toGL Y₀ * modelMat A a xs := by
    have h := modelConj_toGL_of_right A a xs hxs1 Y₀
    rw [hYs] at h
    calc modelMat A a xs * Matrix.SpecialLinearGroup.toGL Y₀
        = modelMat A a xs * Matrix.SpecialLinearGroup.toGL Y₀ * (modelMat A a xs)⁻¹ *
            modelMat A a xs := by group
      _ = Matrix.SpecialLinearGroup.toGL Y₀ * modelMat A a xs := by rw [← h]
  have hg2 : modelMat A a xs * Matrix.SpecialLinearGroup.toGL D₀ * (modelMat A a xs)⁻¹ =
      (Matrix.SpecialLinearGroup.toGL D₀)⁻¹ := by
    rw [← modelConj_toGL_of_right A a xs hxs1, hxsD, map_inv]
  have hY₀sq : Y₀ * Y₀ = 1 := by
    by_cases hsc : ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) c =
        Matrix.SpecialLinearGroup.toGL Y₀
    · obtain ⟨c, hc⟩ := hsc
      have hdet := congrArg Matrix.GeneralLinearGroup.det hc
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
      have hdet1 : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL Y₀) = 1 := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact Y₀.2
      rw [hdet1] at hdet
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_mul, map_one, ← hc, ← map_mul, ← sq, hdet, map_one]
    · exfalso
      have hYD' : Matrix.SpecialLinearGroup.toGL Y₀ * Matrix.SpecialLinearGroup.toGL D₀ =
          Matrix.SpecialLinearGroup.toGL D₀ * Matrix.SpecialLinearGroup.toGL Y₀ := by
        rw [← map_mul, ← map_mul, hYD]
      have hc := gl_commute_of_commute_nonscalar hsc hg1.symm hYD'
      have hD1 : (Matrix.SpecialLinearGroup.toGL D₀)⁻¹ = Matrix.SpecialLinearGroup.toGL D₀ := by
        rw [← hg2, hc, mul_inv_cancel_right]
      have hDD : D₀ * D₀ = 1 := by
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [map_mul, map_one]
        nth_rewrite 1 [← hD1]
        exact inv_mul_cancel _
      rw [hD₀2] at hDD
      have h00 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
        (X : Matrix (Fin 2) (Fin 2) F) 0 0) hDD
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at h00
      apply h2
      linear_combination -h00
  have hy2 : nu t y' ^ 2 = 1 := by
    rw [sq, ← hY₀, ← map_mul, ← map_mul, hY₀sq, map_one, map_one]
  have hdvd2 : orderOf (nu t y') ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have hodd' : Odd (orderOf (nu t y')) := by
    apply Odd.of_dvd_nat _ (orderOf_map_dvd (nu t) y')
    rwa [orderOf_injective _ (C t).subtype_injective] at hyodd
  have h1 : orderOf (nu t y') = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact h1
    · rw [h1] at hodd'
      exact absurd hodd' (by decide)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [frontierSetting_ON]
  exact ⟨y', h1, rfl⟩

theorem frontier_II43 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ p' : ℕ, p'.Prime → p' ≠ 2 →
      ∀ w ∈ Subgroup.centralizer ((frontierSetting S fS t p f).D : Set G),
        (∃ n : ℕ, w ^ p' ^ n = 1) → w ∉ (frontierSetting S fS t p f).L →
          w ^ p' ∈ (frontierSetting S fS t p f).ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p' ∧
            ∃ K₀ : Subgroup G, (frontierSetting S fS t p f).ON ≤ K₀ ∧
              K₀ ≤ (frontierSetting S fS t p f).N ∧
              (frontierSetting S fS t p f).ON.relIndex K₀ = s ∧
              w ∈ Subgroup.normalizer (K₀ : Set G) ∧
              (∀ k ∈ K₀, (frontierSetting S fS t p f).x₂ * k * (frontierSetting S fS t p f).x₂⁻¹ *
                k ∈ (frontierSetting S fS t p f).ON) ∧
              ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ (frontierSetting S fS t p f).ON →
                k ∈ (frontierSetting S fS t p f).ON := by
  intro p' hp' hp'2 w hwD hwm hwL hwON
  obtain ⟨m, hwm⟩ := hwm
  have : Fact p'.Prime := ⟨hp'⟩
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨F, _, _, A, a, phi, hFodd, hAodd, hY, hphit, hL4⟩ :=
    frontier_model hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨v₀, s₀, hvD, -, hs₀, hv4, hv2, hs2, hsv⟩ :=
    frontier_v_s hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  obtain ⟨D₀, xs, hD₀, hxs, hxs1, hD₀2, hxsD⟩ :=
    model_v_s t phi hAodd hY hphit v₀ s₀ (hL4 v₀ hv4) hv2 hs2 hsv
  have hON : ∀ c : C t, (c : G) ∈ (frontierSetting S fS t p f).ON ↔ nu t c = 1 := by
    intro c
    rw [frontierSetting_ON, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨c', hc', hcc'⟩
      rwa [← Subtype.ext hcc']
    · intro hc
      exact ⟨c, hc, rfl⟩
  have htD : t ∈ (frontierSetting S fS t p f).D :=
    (frontierSetting S fS t p f).T_le_D hσ (frontierSetting S fS t p f).x_mem_T
  have hwN : w ∈ C t :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwD t htD).symm
  set w' : C t := ⟨w, hwN⟩ with hw'
  set xw := phi.symm (nu t w') with hxwdef
  have hxw : phi xw = nu t w' := phi.apply_symm_apply _
  have hxwp : xw ^ p' = 1 := by
    have h := (hON (w' ^ p')).mp hwON
    rw [hxwdef, ← map_pow, ← map_pow, h, map_one]
  have hxwm : xw ^ p' ^ m = 1 := by
    have h : w' ^ p' ^ m = 1 := Subtype.ext hwm
    rw [hxwdef, ← map_pow, ← map_pow, h, map_one, map_one]
  have hτp : xw.right ^ p' = 1 := by
    have h := congrArg SemidirectProduct.rightHom hxwp
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  have hτ1 : xw.right ≠ 1 := by
    intro h1
    apply hwL
    have hxw_inl : xw = SemidirectProduct.inl xw.left := SemidirectProduct.ext rfl h1
    have hl : xw.left ^ p' ^ m = 1 := by
      apply SemidirectProduct.inl_injective (φ := MatrixCover.matrixFieldAction F A a)
      rw [map_pow, ← hxw_inl, hxwm, map_one]
    have he : xw.left.right = 1 := by
      have h2 := congrArg SemidirectProduct.rightHom hl
      rw [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h2
      obtain ⟨k, hk⟩ := (hp'.odd_of_ne_two hp'2).pow (n := m)
      have he2 : xw.left.right ^ 2 = 1 := by
        have h := pow_card_eq_one' (G := MatrixCoverData.C2) (x := xw.left.right)
        rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
      rw [hk, pow_succ, pow_mul, he2, one_pow, one_mul] at h2
      exact h2
    have hxw_SL : xw = modelSL A a xw.left.left := by
      apply SemidirectProduct.ext
      · exact SemidirectProduct.ext rfl he
      · exact h1
    have hwL₀ : w' ∈ localLayerPreimage t := (hY w').mpr ⟨xw.left.left, by rw [← hxw_SL, hxw]⟩
    exact Subgroup.mem_sup_left ⟨w', hwL₀, rfl⟩
  have hτord : orderOf (xw.right : F ≃+* F) = p' := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hτp hτ1
  have hwv : w' * v₀ * w'⁻¹ = v₀ := by
    have h : v₀ * w' = w' * v₀ := Subtype.ext (Subgroup.mem_centralizer_iff.mp hwD _ hvD)
    rw [← h, mul_inv_cancel_right]
  have hψD : modelConj A a xw D₀ = D₀ := by
    apply modelSL_injective A a
    apply phi.injective
    rw [modelSL_conj, map_mul, map_mul, map_inv, hxw, hD₀, ← map_inv, ← map_mul, ← map_mul, hwv]
  have hh : modelMat A a xw * Matrix.GeneralLinearGroup.map (xw.right : F ≃+* F).toRingHom
      (Matrix.SpecialLinearGroup.toGL D₀) * (modelMat A a xw)⁻¹ =
        Matrix.SpecialLinearGroup.toGL D₀ := by
    rw [← modelConj_toGL, hψD]
  have hg : modelMat A a xs * Matrix.SpecialLinearGroup.toGL D₀ * (modelMat A a xs)⁻¹ =
      (Matrix.SpecialLinearGroup.toGL D₀)⁻¹ := by
    rw [← modelConj_toGL_of_right A a xs hxs1, hxsD, map_inv]
  obtain ⟨ℓ, hℓ, hℓ2, hℓp', K, hK, hψK, hψK', hψsK⟩ :=
    exists_torus_element hFodd (xw.right : F ≃+* F) hp' hp'2 hτord D₀ hD₀2 (modelMat A a xw)
      (modelMat A a xs) hh hg (modelConj A a xw) (modelConj A a xs) (modelConj_toGL A a xw)
      (modelConj_toGL_of_right A a xs hxs1)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hψK
  set K₁ : Subgroup (H t) := (Subgroup.zpowers K).map (phi.toMonoidHom.comp (modelSL A a))
    with hK₁
  have hmemK : ∀ k ∈ (K₁.comap (nu t)).map (C t).subtype, ∃ c : C t, (c : G) = k ∧
      ∃ i : ℤ, phi (modelSL A a (K ^ i)) = nu t c := by
    rintro k ⟨c, ⟨Z, hZ, hZc⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hZ
    exact ⟨c, rfl, i, hZc⟩
  have hmemK' : ∀ (c : C t) (i : ℤ), phi (modelSL A a (K ^ i)) = nu t c →
      (c : G) ∈ (K₁.comap (nu t)).map (C t).subtype := fun c i h =>
    ⟨c, ⟨K ^ i, Subgroup.zpow_mem_zpowers K i, h⟩, rfl⟩
  have hconj : ∀ (x : MatrixCover.MatrixFieldModel F A a) (u c : C t)
      (Z : Matrix.SpecialLinearGroup (Fin 2) F), phi x = nu t u →
      phi (modelSL A a Z) = nu t c →
        phi (modelSL A a (modelConj A a x Z)) = nu t (u * c * u⁻¹) := by
    intro x u c Z hx hZ
    rw [modelSL_conj, map_mul, map_mul, map_inv, hx, hZ, ← map_inv, ← map_mul, ← map_mul]
  refine ⟨ℓ, hℓ, hℓ2, hℓp', (K₁.comap (nu t)).map (C t).subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [frontierSetting_ON]
    refine Subgroup.map_mono fun c hc => ?_
    change nu t c ∈ K₁
    have h1 : nu t c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    rw [h1]
    exact one_mem _
  · exact Subgroup.map_subtype_le _
  ·
    rw [frontierSetting_ON, Subgroup.relIndex_map_map_of_injective _ _ (C t).subtype_injective]
    have hker : N t = (⊥ : Subgroup (H t)).comap (nu t) := by
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [show (N t).relIndex (K₁.comap (nu t)) =
        ((⊥ : Subgroup (H t)).comap (nu t)).relIndex (K₁.comap (nu t)) from
      congrArg (fun X : Subgroup (C t) => X.relIndex (K₁.comap (nu t))) hker,
      Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.relIndex_bot_left, hK₁,
      Subgroup.card_map_of_injective (phi.injective.comp (modelSL_injective A a)),
      Nat.card_zpowers, hK]
  ·
    apply Subgroup.mem_normalizer_fintype
    intro k hk
    obtain ⟨c, rfl, i, hci⟩ := hmemK k hk
    have h := hconj xw w' c (K ^ i) hxw hci
    rw [map_zpow, ← hj, ← zpow_mul] at h
    exact hmemK' (w' * c * w'⁻¹) (j * i) h
  ·
    intro k hk
    obtain ⟨c, rfl, i, hci⟩ := hmemK k hk
    have h := hconj xs s₀ c (K ^ i) hxs hci
    rw [map_zpow, hψsK, inv_zpow'] at h
    rw [← hs₀]
    apply (hON (s₀ * c * s₀⁻¹ * c)).mpr
    rw [map_mul, ← h, ← hci, ← map_mul, ← map_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      map_one, map_one]
  ·
    intro k hk hwk
    obtain ⟨c, rfl, i, hci⟩ := hmemK k hk
    have h := hconj xw w' c (K ^ i) hxw hci
    have h1 : nu t (w' * c * w'⁻¹ * c⁻¹) = 1 := (hON _).mp hwk
    rw [map_mul, map_inv, mul_inv_eq_one, ← h, ← hci] at h1
    have h2 : modelConj A a xw (K ^ i) = K ^ i :=
      modelSL_injective A a (phi.injective h1)
    rw [map_zpow, ← hj, ← zpow_mul] at h2
    have h3 : K ^ ((j - 1) * i) = 1 := by
      rw [sub_mul, zpow_sub, h2, one_mul, mul_inv_cancel]
    have h4 := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rw [hK] at h4
    rcases Int.Prime.dvd_mul' hℓ h4 with h5 | h5
    · exfalso
      apply hψK'
      rw [← hj]
      obtain ⟨u, hu⟩ := h5
      rw [show j = 1 + ℓ * u by linear_combination hu, zpow_add, zpow_one, zpow_mul]
      have hKℓ : K ^ (ℓ : ℤ) = 1 := by
        rw [zpow_natCast, ← hK]
        exact pow_orderOf_eq_one K
      rw [hKℓ, one_zpow, mul_one]
    · have hKi : K ^ i = 1 := by
        rw [← hK] at h5
        exact orderOf_dvd_iff_zpow_eq_one.mp h5
      apply (hON c).mpr
      rw [← hci, hKi, map_one, map_one]

end ModelFrontier

end CFSG.Semidihedral.AllPrime
