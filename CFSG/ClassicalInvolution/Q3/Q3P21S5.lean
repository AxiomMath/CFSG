module

public import CFSG.ClassicalInvolution.Q3.Q3TIYSu4Fix
public import CFSG.ClassicalInvolution.Q3.Q3URPat
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.SU4ThreeModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution.RouteD.SU4Pattern
open scoped MatrixGroups

section Arith

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_ne_three (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f) :
    ∃ u : K, unitaryInvolution K p f u * u = 1 ∧ unitaryInvolution K p f u ≠ u := by
  obtain ⟨c, hc, hc2⟩ := Q3TIY.exists_norm_one_ne3 hK hq
  refine ⟨c, hc, fun he => hc2 ?_⟩
  rw [he] at hc
  exact hc

theorem blockDiag_of_normalizes3 (hK : Nat.card K = (p ^ f) ^ 2) (hq : 3 ≤ p ^ f)
    {G : Matrix (Fin 4) (Fin 4) K} (hiso : conjTr (unitaryInvolution K p f) G * G = 1)
    (hsq : ∃ s : K, G * G = s • (1 : Matrix (Fin 4) (Fin 4) K))
    (hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G) :
    G = BD !![G 0 0, G 0 1; G 1 0, G 1 1] !![G 2 2, G 2 3; G 3 2, G 3 3] := by
  obtain ⟨u, hu, hne⟩ := exists_norm_one_ne_three hK hq
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hu' : u * σ u = 1 := by rw [mul_comm]; exact hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    simp
  have hu1' : σ u ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg σ h1
    rwa [hσσ, map_one] at this
  have hdet1 : (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp [hu']
  have hiso1 : conjTr σ (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) *
      (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ, hu, hu']
  obtain ⟨s, hs⟩ := hsq
  have hGs : G = s • conjTr σ G := eq_smul_conjTr_of_sq σ hiso hs
  obtain ⟨A', hA'⟩ := hnorm (Models.mkSU K p f _ hdet1 hiso1)
  rw [suMat_mkSU] at hA'
  have e20 := congrFun (congrFun hA' 2) 0
  have e30 := congrFun (congrFun hA' 3) 0
  have e21 := congrFun (congrFun hA' 2) 1
  have e31 := congrFun (congrFun hA' 3) 1
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four] at e20 e30 e21 e31
  have z20 : G 2 0 = 0 := by
    have : G 2 0 * (u - 1) = 0 := by linear_combination e20
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z30 : G 3 0 = 0 := by
    have : G 3 0 * (u - 1) = 0 := by linear_combination e30
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z21 : G 2 1 = 0 := by
    have : G 2 1 * (σ u - 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have z31 : G 3 1 = 0 := by
    have : G 3 1 * (σ u - 1) = 0 := by linear_combination e31
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have hT : ∀ i j : Fin 4, G i j = s * σ (G j i) := fun i j => by
    have := congrFun (congrFun hGs i) j
    simpa [conjTr] using this
  have z02 : G 0 2 = 0 := by rw [hT, z20, map_zero, mul_zero]
  have z03 : G 0 3 = 0 := by rw [hT, z30, map_zero, mul_zero]
  have z12 : G 1 2 = 0 := by rw [hT, z21, map_zero, mul_zero]
  have z13 : G 1 3 = 0 := by rw [hT, z31, map_zero, mul_zero]
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [z20, z30, z21, z31, z02, z03, z12, z13]


theorem block_data_three3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) {G : Matrix (Fin 4) (Fin 4) K}
    (hiso : conjTr (unitaryInvolution K p f) G * G = 1) (hsq : ∃ s : K, G * G = s • 1)
    (hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G)
    (hnon : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      G * blockMat 4 0 (suMat A) ≠ blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * G) :
    ∃ (a : K) (H₁ H₂ : Matrix (Fin 2) (Fin 2) K), G = BD H₁ H₂ ∧
      unitaryInvolution K p f a * a = -1 ∧
      conjTr (unitaryInvolution K p f) H₁ * H₁ = 1 ∧ H₁ * H₁ = a ^ 2 • 1 ∧ H₁ ≠ a • 1 ∧
      H₁ ≠ (-a) • 1 ∧ conjTr (unitaryInvolution K p f) H₂ * H₂ = 1 ∧ H₂ * H₂ = a ^ 2 • 1 ∧
      H₂ ≠ a • 1 ∧ H₂ ≠ (-a) • 1 := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  obtain ⟨s, hs⟩ := hsq
  have hGform := blockDiag_of_normalizes3 hK hq hiso ⟨s, hs⟩ hnorm
  set P : Matrix (Fin 2) (Fin 2) K := !![G 0 0, G 0 1; G 1 0, G 1 1] with hP
  set T : Matrix (Fin 2) (Fin 2) K := !![G 2 2, G 2 3; G 3 2, G 3 3] with hT
  clear_value P T
  clear hP hT
  subst hGform
  rw [conjTr_BD, BD_mul, ← BD_one] at hiso
  obtain ⟨hI1, hI2⟩ := BD_inj hiso
  rw [BD_mul, ← BD_smul_one] at hs
  obtain ⟨hS1, hS2⟩ := BD_inj hs
  have hnon' : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      P * suMat A ≠ (suMat r * suMat A * suMat r⁻¹) * P := by
    intro r
    obtain ⟨A, hA⟩ := hnon r
    refine ⟨A, fun h => hA ?_⟩
    rw [blockMat_zero_eq_BD, blockMat_zero_eq_BD, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul,
      h]
  have hPns : ∀ d : K, P ≠ d • 1 := by
    intro d hd
    obtain ⟨A, hA⟩ := hnon' 1
    apply hA
    rw [hd, suMat_one, inv_one, suMat_one, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul]
  have e00 := congrFun (congrFun hS1 0) 0
  have e01 := congrFun (congrFun hS1 0) 1
  have e10 := congrFun (congrFun hS1 1) 0
  have e11 := congrFun (congrFun hS1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have htr : P 0 0 + P 1 1 = 0 := by
    by_contra hne
    have hb : P 0 1 = 0 := by
      have : P 0 1 * (P 0 0 + P 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hc : P 1 0 = 0 := by
      have : P 1 0 * (P 0 0 + P 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne
    have had : P 0 0 = P 1 1 := by
      have : (P 0 0 - P 1 1) * (P 0 0 + P 1 1) = 0 := by
        rw [hb, hc] at e00 e11
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    apply hPns (P 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  have hdetP : P.det = -s := by
    rw [Matrix.det_fin_two]
    have : P 1 1 = -P 0 0 := by linear_combination htr
    rw [this]
    linear_combination (-1 : K) * e00
  have hdetN : σ P.det * P.det = 1 := by
    have h1 := congrArg Matrix.det hI1
    have e : (conjTr σ P).det = σ P.det := by
      show ((P.map σ)ᵀ).det = σ P.det
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (σ : K →+* K) P).symm
    rw [Matrix.det_mul, e, Matrix.det_one] at h1
    exact h1
  have hev : Even (p ^ f + 1) := ⟨(p ^ f + 1) / 2, by omega⟩
  have hs1 : s ^ (p ^ f + 1) = 1 := by
    have := norm_pow_eq_one (K := K) (p := p) (f := f) hdetN
    rw [hdetP, neg_pow, hev.neg_one_pow, one_mul] at this
    exact this
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hs1
    exact zero_ne_one hs1
  obtain ⟨a, ha⟩ : ∃ a : K, a ^ 2 = s := by
    have := Fintype.ofFinite K
    have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hsqr : IsSquare s := by
      rw [FiniteField.isSquare_iff hrc hs0, ← Nat.card_eq_fintype_card, hK]
      obtain ⟨m, hm⟩ : ∃ m, p ^ f = 2 * m + 1 := ⟨p ^ f / 2, by omega⟩
      have h3 : (p ^ f) ^ 2 = 2 * ((p ^ f + 1) * m) + 1 := by rw [hm]; ring
      have h4 : (p ^ f) ^ 2 / 2 = (p ^ f + 1) * m := by
        rw [h3, Nat.mul_add_div (by norm_num)]
        norm_num
      rw [h4, pow_mul, hs1, one_pow]
    obtain ⟨a, hasq⟩ := hsqr
    exact ⟨a, by rw [hasq]; ring⟩
  have hanorm : σ a * a = 1 ∨ σ a * a = -1 := by
    have h1 : a ^ (p ^ f + 1) * a ^ (p ^ f + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, ha, hs1]
    have h2' : σ a * a = a ^ (p ^ f + 1) := by
      rw [hσ, unitaryInvolution_apply, ← pow_succ]
    rw [h2']
    exact mul_self_eq_one_iff.mp h1
  rcases hanorm with hn1 | hn1
  ·
    exfalso
    obtain ⟨ι, hι, hσι⟩ := exists_sqrt_neg_one_three hK hq3
    set e : K := a * ι with he
    have hσe : σ e * e = 1 := by
      rw [he, map_mul, hσι]
      linear_combination (-(ι * ι)) * hn1 - hι
    have he2 : e * e = -s := by
      have : a * ι * (a * ι) = a ^ 2 * (ι * ι) := by ring
      rw [he, this, hι, ha]
      ring
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at he2
      exact hs0 (neg_eq_zero.mp he2.symm)
    have hriso : conjTr σ (e⁻¹ • P) * (e⁻¹ • P) = 1 := by
      have : σ e⁻¹ * e⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hσe, inv_one]
      rw [conjTr_smul_aux, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI1, this, one_smul]
    have hrdet : (e⁻¹ • P).det = 1 := by
      rw [Matrix.det_smul, hdetP]
      simp only [Fintype.card_fin]
      field_simp
      linear_combination -he2
    set r : Su K p f 2 := Models.mkSU K p f (e⁻¹ • P) hrdet hriso with hr
    obtain ⟨A, hA⟩ := hnon' r
    apply hA
    have hrm : suMat r = e⁻¹ • P := suMat_mkSU hrdet hriso
    have key : P = e • suMat r := by rw [hrm, smul_smul, mul_inv_cancel₀ he0, one_smul]
    calc P * suMat A = (e • suMat r) * suMat A := by rw [← key]
      _ = e • (suMat r * suMat A * (suMat r⁻¹ * suMat r)) := by
          rw [suMat_inv_mul_suMat, Matrix.mul_one, Matrix.smul_mul]
      _ = suMat r * suMat A * suMat r⁻¹ * (e • suMat r) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = suMat r * suMat A * suMat r⁻¹ * P := by rw [← key]
  ·
    have hPa : P * P = a ^ 2 • 1 := by rw [ha]; exact hS1
    have hTa : T * T = a ^ 2 • 1 := by rw [ha]; exact hS2
    refine ⟨a, P, T, rfl, hn1, hI1, hPa, hPns a, hPns (-a), hI2, hTa, ?_, ?_⟩
    · intro hTe
      have := congrFun (congrFun hI2 0) 0
      rw [hTe] at this
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at this
      rw [hn1] at this
      apply h2
      linear_combination -this
    · intro hTe
      have := congrFun (congrFun hI2 0) 0
      rw [hTe] at this
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at this
      rw [hn1] at this
      apply h2
      linear_combination -this

end Arith

section Core

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_chart_lift3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hqq : p ^ f = 3)
    {F : Type} [Field F] [Finite F] (ε : F ≃+* fixedSubfield K p f)
    {X : Type} [Group X] (ψ : Su K p f 4 →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (hcop : ∀ x ∈ ψ.ker, ¬ 3 ∣ orderOf x)
    (hker1 : ∀ z ∈ rootSU2 K p f (by norm_num : 2 ≤ 4), z ∈ ψ.ker → z = 1)
    (θ : SL(2, F) →* X) (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (ρ : X ≃* X) (d : Fˣ) (hθρ : ∀ s, ρ (θ s) = θ (diagConj2 d 1 s))
    (α : Su K p f 4 →* Su K p f 4) (hα : ∀ x, ψ (α x) = ρ (ψ x)) :
    ∃ θ' : SL(2, F) →* Su K p f 4, Function.Injective θ' ∧
      θ'.range = rootSU2 K p f (by norm_num : 2 ≤ 4) ∧
      ∀ s, α (θ' s) = θ' (diagConj2 d 1 s) := by
  classical
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hcardF : Nat.card F = 3 := by
    rw [Nat.card_congr ε.toEquiv, card_fixedSubfield hK, hqq]
  have hL : ∀ l : SL(2, F), l ^ 3 ∈ ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ :=
    fun l => Q3W.pow_three_mem_commutator_of_equiv hcardF
      (Subgroup.topEquiv (G := SL(2, F))) l trivial
  obtain ⟨ν, hνinj, hνrange, -⟩ := exists_natChart hK hp2 ε
  set R : Subgroup (Su K p f 4) := rootSU2 K p f hn with hR
  have hinjR : ∀ a ∈ R, ∀ b ∈ R, ψ a = ψ b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hker1 _ (R.mul_mem (R.inv_mem ha) hb) h1)
  have hνR : ∀ s, ν s ∈ R := fun s => hνrange ▸ ⟨s, rfl⟩
  set θ₂ : SL(2, F) →* X := ψ.comp ν with hθ₂
  have hθ₂inj : Function.Injective θ₂ := by
    intro s t hst
    exact hνinj (hinjR _ (hνR s) _ (hνR t) hst)
  have hθ₂range : θ₂.range = θ.range := by
    rw [hθ, hθ₂, MonoidHom.range_comp, hνrange]
  have hex : ∀ s : SL(2, F), ∃ s' : SL(2, F), θ₂ s' = θ s := fun s => by
    have : θ s ∈ θ₂.range := hθ₂range ▸ ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := this
    exact ⟨s', hs'⟩
  choose γf hγf using hex
  let γ0 : SL(2, F) →* SL(2, F) :=
    { toFun := γf
      map_one' := hθ₂inj (by rw [hγf, map_one, map_one])
      map_mul' := fun s t => hθ₂inj (by rw [hγf, map_mul, map_mul, hγf, hγf]) }
  have hγsurj : Function.Surjective γ0 := fun t => by
    have : θ₂ t ∈ θ.range := hθ₂range ▸ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := this
    exact ⟨s, hθ₂inj (by show θ₂ (γf s) = θ₂ t; rw [hγf]; exact hs)⟩
  have hγinj : Function.Injective γ0 := Finite.injective_iff_surjective.2 hγsurj
  have hγθ : ∀ s, θ₂ (γ0 s) = θ s := hγf
  set θ' : SL(2, F) →* Su K p f 4 := ν.comp γ0 with hθ'
  have hθ'ψ : ∀ s, ψ (θ' s) = θ s := fun s => hγθ s
  have hθ'inj : Function.Injective θ' := hνinj.comp hγinj
  have hθ'range : θ'.range = R := by
    rw [hθ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hγsurj, Subgroup.map_top, hνrange]
  have key := Q3W.hom_eq_of_central_ker3_gen (θ := ψ) hker hcop (L := SL(2, F)) hL
    (α.comp θ') (θ'.comp (diagConj2 d 1).toMonoidHom) (fun s => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hα, hθ'ψ, hθ'ψ, hθρ])
  exact ⟨θ', hθ'inj, hθ'range, fun s => DFunLike.congr_fun key s⟩

theorem core_fixed_short_linear3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ f)
    (hqq : p ^ f = 3) (hq3 : p ^ f % 4 = 3) {F : Type} [Field F] [Finite F]
    (ε : F ≃+* fixedSubfield K p f) {X : Type} [Group X] (ψ : Su K p f 4 →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su K p f 4)) (hcop : ∀ x ∈ ψ.ker, ¬ 3 ∣ orderOf x)
    (hker1 : ∀ z ∈ rootSU2 K p f (by norm_num : 2 ≤ 4), z ∈ ψ.ker → z = 1)
    (hperf : Group.IsPerfect (Su K p f 4)) (τ : X ≃* X) (hτ : ∀ x, τ (τ x) = x)
    (θ : SL(2, F) →* X) (hθ : θ.range = (rootSU2 K p f (by norm_num : 2 ≤ 4)).map ψ)
    (hθτ : ∀ s, τ (θ s) = θ (diagConj2 (-1) 1 s)) (hlin : LinearLift ψ τ) :
    ∃ (Q : GL (Fin 4) K) (hQ : conjTr (unitaryInvolution K p f) (Q : Matrix (Fin 4) (Fin 4) K) *
        (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4),
      (∀ r : Fin 4, r = 0 ∨ r = 1 → (Q : Matrix (Fin 4) (Fin 4) K) r 0 = 0 ∧
        (Q : Matrix (Fin 4) (Fin 4) K) r 3 = 0) ∧
      ∀ (y : Su K p f 4) (M : Matrix (Fin 4) (Fin 4) K), M * levi4 = levi4 * M →
        suMat y = (Q : Matrix (Fin 4) (Fin 4) K) * M *
          ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) → τ (ψ y) = ψ y := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hn : (2 : ℕ) ≤ 4 := by norm_num
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hcardF : Nat.card F = p ^ f := by
    rw [Nat.card_congr ε.toEquiv, card_fixedSubfield hK]
  have hF3 : Nat.card F % 4 = 3 := by rw [hcardF]; exact hq3
  obtain ⟨G, Gi, hGGi, hGiG, hGiso, hy⟩ := hlin
  obtain ⟨α, hαmat, hα⟩ := exists_hom_of_linear (ψ := ψ) (τ := τ) hGiG hy
  set g : GL (Fin 4) K := ⟨G, Gi, hGGi, hGiG⟩ with hg
  have hmat : ∀ x, ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K) *
        (RingEquiv.refl K).mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := fun x => by
    have : (RingEquiv.refl K).mapMatrix ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      rfl
    rw [this]
    exact hαmat x
  obtain ⟨θ', hθ'inj, hθ'range, hequiv⟩ :=
    exists_chart_lift3 hK hp2 hqq ε ψ hker hcop hker1 θ hθ τ (-1) hθτ α hα
  have hα2 : ∀ x, α (α x) = x := by
    have := hom_eq_of_central_ker_perfect (G := Su K p f 4) (θ := ψ) hker
      (α.comp α) (MonoidHom.id _) (fun x => by
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
        rw [hα, hα, hτ])
    exact fun x => DFunLike.congr_fun this x
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hGsq : ∃ s : K, G * G = s • (1 : Matrix (Fin 4) (Fin 4) K) := by
    refine eq_smul_one_of_commute hUF hp2 (by norm_num : 3 ≤ 4) (G * G) fun y hy => ?_
    have hy' : y ∈ SUid σ 4 := by rw [SUid_eq_statedSU hK]; exact hy
    have h4 := hα2 ⟨y, hy'⟩
    have h5 : suMat (α (α ⟨y, hy'⟩)) = (G * G) * (y : Matrix (Fin 4) (Fin 4) K) * (Gi * Gi) := by
      rw [hαmat (α ⟨y, hy'⟩), hαmat ⟨y, hy'⟩]
      simp only [Matrix.mul_assoc]
      rfl
    rw [h4] at h5
    have h6 : (Gi * Gi) * (G * G) = 1 := by
      calc Gi * Gi * (G * G) = Gi * (Gi * G) * G := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hGiG, Matrix.mul_one, hGiG]
    calc G * G * (y : Matrix (Fin 4) (Fin 4) K)
        = (G * G * (y : Matrix (Fin 4) (Fin 4) K) * (Gi * Gi)) * (G * G) := by
          rw [Matrix.mul_assoc (G * G * (y : Matrix (Fin 4) (Fin 4) K)), h6, Matrix.mul_one]
      _ = (y : Matrix (Fin 4) (Fin 4) K) * (G * G) := by rw [← h5]; rfl
  have hRθ : ∀ A : Su K p f 2, ∃ s : SL(2, F), θ' s = blockEmb K p f 4 2 0 (by omega) A := by
    intro A
    have : blockEmb K p f 4 2 0 (by omega) A ∈ rootSU2 K p f hn := ⟨A, rfl⟩
    rw [← hθ'range] at this
    exact this
  have hRθ' : ∀ s : SL(2, F), ∃ A : Su K p f 2, blockEmb K p f 4 2 0 (by omega) A = θ' s := by
    intro s
    have : θ' s ∈ rootSU2 K p f hn := by rw [← hθ'range]; exact ⟨s, rfl⟩
    exact this
  have hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G := by
    intro A
    obtain ⟨s, hs⟩ := hRθ A
    have h1 : α (blockEmb K p f 4 2 0 (by omega) A) ∈ rootSU2 K p f hn := by
      rw [← hs, hequiv, ← hθ'range]
      exact ⟨_, rfl⟩
    obtain ⟨A'', hA''⟩ := h1
    refine ⟨suMat A'', ?_⟩
    have h2' := congrArg suMat hA''
    rw [hαmat] at h2'
    have e1 : suMat (blockEmb K p f 4 2 0 (by omega) A'') = blockMat 4 0 (suMat A'') := rfl
    have e2 : suMat (blockEmb K p f 4 2 0 (by omega) A) = blockMat 4 0 (suMat A) := rfl
    rw [e1, e2] at h2'
    calc G * blockMat 4 0 (suMat A) = G * blockMat 4 0 (suMat A) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * blockMat 4 0 (suMat A) * Gi) * G := by simp only [Matrix.mul_assoc]
      _ = blockMat 4 0 (suMat A'') * G := by rw [← h2']
  have hnon : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      G * blockMat 4 0 (suMat A) ≠ blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * G := by
    intro r
    by_contra hcon
    push Not at hcon
    have hαr : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by omega) A) =
        blockEmb K p f 4 2 0 (by omega) (r * A * r⁻¹) := by
      intro A
      apply suMat_injective
      rw [hαmat]
      show G * blockMat 4 0 (suMat A) * Gi = blockMat 4 0 (suMat (r * A * r⁻¹))
      rw [suMat_mul, suMat_mul, hcon A, Matrix.mul_assoc, hGGi, Matrix.mul_one]
    obtain ⟨s₀, hs₀⟩ := hRθ r
    refine not_inner_diagConj2 (F := F) hF3 ⟨s₀, fun s => ?_⟩
    apply hθ'inj
    obtain ⟨A, hA⟩ := hRθ' s
    rw [← hequiv, map_mul, map_mul, map_inv, hs₀, ← hA, hαr, map_mul, map_mul, map_inv]
  obtain ⟨a, H₁, H₂, hGform, ha, hiso₁, hsq₁, hn₁, hn₁', hiso₂, hsq₂, hn₂, hn₂'⟩ :=
    block_data_three3 hK hp2 hq hq3 hGiso hGsq hnorm hnon
  obtain ⟨Q, hQ, hsupp, heig⟩ :=
    exists_witt_eigenbasis σ hσσ h2 ha hiso₁ hsq₁ hn₁ hn₁' hiso₂ hsq₂ hn₂ hn₂'
  refine ⟨Q, hQ, hsupp, ?_⟩
  intro y M hM hy
  set Qm : Matrix (Fin 4) (Fin 4) K := (Q : Matrix (Fin 4) (Fin 4) K) with hQm
  set Qi : Matrix (Fin 4) (Fin 4) K := ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hQi
  have hQQi : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hD : Matrix.diagonal ![a, a, -a, -a] = a • (levi4 : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levi4]
  have hHeq : G = blockMat 4 0 H₁ * blockMat 4 2 H₂ := hGform
  have hGQ : G * Qm = Qm * (a • levi4) := by
    rw [hHeq, ← hD]
    exact heig
  have hQiG : Qi * G = (a • levi4) * Qi := by
    calc Qi * G = Qi * G * (Qm * Qi) := by rw [hQQi, Matrix.mul_one]
      _ = Qi * (G * Qm) * Qi := by simp only [Matrix.mul_assoc]
      _ = Qi * (Qm * (a • levi4)) * Qi := by rw [hGQ]
      _ = (a • levi4) * Qi := by simp only [← Matrix.mul_assoc, hQiQ, Matrix.one_mul]
  have hcm : (a • (levi4 : Matrix (Fin 4) (Fin 4) K)) * M = M * (a • levi4) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM]
  have hcommy : G * suMat y = suMat y * G := by
    have hy' : suMat y = Qm * M * Qi := hy
    rw [hy']
    calc G * (Qm * M * Qi) = (G * Qm) * M * Qi := by simp only [Matrix.mul_assoc]
      _ = Qm * ((a • levi4) * M) * Qi := by rw [hGQ]; simp only [Matrix.mul_assoc]
      _ = Qm * (M * (a • levi4)) * Qi := by rw [hcm]
      _ = Qm * M * ((a • levi4) * Qi) := by simp only [Matrix.mul_assoc]
      _ = Qm * M * (Qi * G) := by rw [hQiG]
      _ = Qm * M * Qi * G := by simp only [Matrix.mul_assoc]
  have hαy : α y = y := by
    apply suMat_injective
    rw [hαmat y, hcommy, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  calc τ (ψ y) = ψ (α y) := (hα y).symm
    _ = ψ y := by rw [hαy]

end Core

end CFSG.ClassicalInvolution.Q3.Q3P21
