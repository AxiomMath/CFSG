module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDeduce
import CFSG.RankThree.PartOne.S11c.Sec66Glue
public import CFSG.RankThree.PartOne.S11c.Sec66PSU

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Perm

variable {f : ℕ} {K : Type} [Field K]

@[expose] def swM3 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def cyM3 : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def cyIM3 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem swM3_mul_swM3 : (swM3 : Matrix (Fin 3) (Fin 3) K) * swM3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swM3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyM3_mul_cyIM3 : (cyM3 : Matrix (Fin 3) (Fin 3) K) * cyIM3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3, cyIM3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyIM3_mul_cyM3 : (cyIM3 : Matrix (Fin 3) (Fin 3) K) * cyM3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3, cyIM3, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swU3 : GL (Fin 3) K := ⟨swM3, swM3, swM3_mul_swM3, swM3_mul_swM3⟩

@[expose] def cyU3 : GL (Fin 3) K := ⟨cyM3, cyIM3, cyM3_mul_cyIM3, cyIM3_mul_cyM3⟩

theorem swM3_map_bar (hU : UnitaryFieldData 2 f K) :
    (swM3 : Matrix (Fin 3) (Fin 3) K).map hU.bar = swM3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swM3]

theorem cyM3_map_bar (hU : UnitaryFieldData 2 f K) :
    (cyM3 : Matrix (Fin 3) (Fin 3) K).map hU.bar = cyM3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3]

theorem swM3_transpose : (swM3 : Matrix (Fin 3) (Fin 3) K)ᵀ = swM3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swM3]

theorem cyM3_transpose : (cyM3 : Matrix (Fin 3) (Fin 3) K)ᵀ = cyIM3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3, cyIM3]

theorem swU3_mem (hU : UnitaryFieldData 2 f K) :
    (swU3 : GL (Fin 3) K) ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) K) := by
  have := hU.charP
  refine ⟨?_, ?_⟩
  · show (swM3.map hU.bar)ᵀ * 1 * swM3 = 1
    rw [swM3_map_bar, swM3_transpose, Matrix.mul_one, swM3_mul_swM3]
  · show (swM3 : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Matrix.det_fin_three]
    simp [swM3]
    exact CharTwo.neg_eq 1

theorem cyU3_mem (hU : UnitaryFieldData 2 f K) :
    (cyU3 : GL (Fin 3) K) ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) K) := by
  have := hU.charP
  refine ⟨?_, ?_⟩
  · show (cyM3.map hU.bar)ᵀ * 1 * cyM3 = 1
    rw [cyM3_map_bar, cyM3_transpose, Matrix.mul_one, cyIM3_mul_cyM3]
  · show (cyM3 : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Matrix.det_fin_three]
    simp [cyM3]

theorem glAut_swU3 (σ : K ≃+* K) : glAut σ (swU3 : GL (Fin 3) K) = swU3 := by
  apply Units.ext
  rw [coe_glAut]
  show (swM3 : Matrix (Fin 3) (Fin 3) K).map σ = swM3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swM3]

theorem glAut_cyU3 (σ : K ≃+* K) : glAut σ (cyU3 : GL (Fin 3) K) = cyU3 := by
  apply Units.ext
  rw [coe_glAut]
  show (cyM3 : Matrix (Fin 3) (Fin 3) K).map σ = cyM3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3]

theorem swU3_sq : (swU3 : GL (Fin 3) K) ^ 2 = 1 := by
  rw [pow_two]
  exact Units.ext swM3_mul_swM3

theorem cyU3_cube : (cyU3 : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_three, Units.val_one]
  show cyM3 * (cyM3 * cyM3) = (1 : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyM3, Matrix.mul_apply, Fin.sum_univ_three]

theorem swU3_conj : (swU3 : GL (Fin 3) K) * cyU3 * swU3⁻¹ = cyU3⁻¹ := by
  apply Units.ext
  show swM3 * cyM3 * swM3 = (cyIM3 : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swM3, cyM3, cyIM3, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_sThree_primeFormP (hU : UnitaryFieldData 2 f K) (σ : K ≃+* K) :
    ∃ t c : primeFormP hU (((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      primeFormFieldHom hU (isPrimeFormGram_one (n := 3)) σ t = t ∧
        primeFormFieldHom hU (isPrimeFormGram_one (n := 3)) σ c = c ∧ t ^ 2 = 1 ∧ c ^ 3 = 1 ∧
        c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ := by
  let s₀ : gramSU hU (((1 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := ⟨swU3, swU3_mem hU⟩
  let c₀ : gramSU hU (((1 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := ⟨cyU3, cyU3_mem hU⟩
  refine ⟨(s₀ : primeFormP hU _), (c₀ : primeFormP hU _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change primeFormFieldAut hU isPrimeFormGram_one σ
      (s₀ : primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = _
    rw [primeFormFieldAut_mk]
    congr 1
    exact Subtype.ext (glAut_swU3 σ)
  · change primeFormFieldAut hU isPrimeFormGram_one σ
      (c₀ : primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = _
    rw [primeFormFieldAut_mk]
    congr 1
    exact Subtype.ext (glAut_cyU3 σ)
  · rw [← QuotientGroup.mk_pow, show s₀ ^ 2 = 1 from Subtype.ext swU3_sq]
    rfl
  · rw [← QuotientGroup.mk_pow, show c₀ ^ 3 = 1 from Subtype.ext cyU3_cube]
    rfl
  · intro h
    obtain ⟨c', -, -, hc'⟩ := (QuotientGroup.eq_one_iff c₀).1 h
    have := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K) 0 1) hc'
    simp [c₀, cyU3, cyM3, GeneralLinearGroup.scalar] at this
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext swU3_conj

end Perm

theorem exists_fixed_sThree_psu_three {T : Type} [Group T] [Finite T] {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .PSU 3 2 f) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    ∃ t c : T, α t = t ∧ α c = c ∧ t ^ 2 = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hU, hn3, hq₁, ⟨e⟩⟩ := psu_prime_form_model hC
  have hC1 : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα'ord : orderOf α' = p := orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ one_mem _))
  have hdiag : ¬ p ∣ Nat.gcd 3 (2 ^ f + 1) := fun hd => by
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  have hσ1 : primeFormFieldFactor hU hC1 hn3 hq₁ α' ≠ 1 := by
    intro hσ1
    have hαD : α' ∈ primeFormD hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← ker_primeFormFieldFactor hU hC1 hn3 hq₁]
      exact hσ1
    exact hα'inn (mem_innerAut_of_mem_D hU hn3 hq₁ hp hdiag hαD hα'p)
  set σ := primeFormFieldFactor hU hC1 hn3 hq₁ α' with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hα'p, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hMconj⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hU hn3 hq₁ hp hp2 hp2
      α' hα'ord σ rfl hσord
  set β := primeFormFieldHom hU hC1 σ with hβ
  set ψ := (primeFormConjHom hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹ with hψ
  have hψα : ψ * α' * ψ⁻¹ = β := by
    rw [hψ, inv_inv]
    exact hMconj
  let φ : T ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := e.trans ψ
  have hφα : MulAut.congr φ α = β := by
    have : MulAut.congr φ α = ψ * α' * ψ⁻¹ := rfl
    rw [this, hψα]
  have hfix : ∀ y : primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      β y = y → α (φ.symm y) = φ.symm y := fun y hy => by
    have h1 : MulAut.congr φ α y = φ (α (φ.symm y)) := rfl
    rw [hφα, hy] at h1
    exact φ.injective (by rw [← h1, MulEquiv.apply_symm_apply])
  obtain ⟨t₀, c₀, ht₀, hc₀, ht2, hc3, hc1, htc⟩ := exists_sThree_primeFormP hU σ
  refine ⟨φ.symm t₀, φ.symm c₀, hfix _ ht₀, hfix _ hc₀, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ht2, map_one]
  · rw [← map_pow, hc3, map_one]
  · intro h
    exact hc1 (φ.symm.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_inv, ← map_inv, ← map_mul, htc]

theorem lieOutConcl_psu_three_p {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 p) : LieOutConcl L x := by
  have hαp := centerQuotientConj_pow hx hxp
  obtain ⟨t, c, htf, hcf, ht, hc, hcne, htc⟩ := exists_fixed_sThree_psu_three hp hp5 h hαp hαinn
  exact lieOutConcl_of_sThree hx hp hp5 hxp (borelMaximal_of_model_psu_three h) htf hcf ht hc hcne
    htc

end CFSG.AGLEmbedding.LieOut
