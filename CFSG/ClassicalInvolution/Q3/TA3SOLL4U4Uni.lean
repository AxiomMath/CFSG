module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniPairG

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatFactsL4U4
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem planeHom_eq_one {a : SL(2, h.fixedField)} (ha : planeHom h a = 1) : a = 1 := by
  ext i j
  have := congrFun (congrFun ha i) j
  rw [planeHom_apply, Matrix.map_apply] at this
  change h.fixedField.subtype _ = _
  rw [this]
  by_cases hij : i = j <;> simp [hij, one_apply]

theorem twoSL2Shape_of_t2 (hp : p ≠ 2) {A : hypSU h 2 0} {l : K}
    {v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => l) (fun _ => -l) i • v i) :
    TwoSL2Shape (hypPSU h 2 0) (hypProj h 2 0 A) h.fixedField := by
  obtain ⟨ψ, hψ1, hψA⟩ := InvClassU.exists_t2Hom h hp A.2.1 hv hAv
  set φ₁ := (hypProj h 2 0).comp (ψ.comp (MonoidHom.inl _ _)) with hφ₁
  set φ₂ := (hypProj h 2 0).comp (ψ.comp (MonoidHom.inr _ _)) with hφ₂
  have hscal : ∀ {a b : Matrix (Fin 2) (Fin 2) K} {c : K}, fromBlocks a 0 0 b = c • 1 →
      a = c • 1 ∧ b = c • 1 := fun hc => by
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero] at hc
    obtain ⟨h11, -, -, h22⟩ := fromBlocks_inj.mp hc
    exact ⟨h11, h22⟩
  have hc1 : ∀ {c : K}, (1 : Matrix (Fin 2) (Fin 2) K) = c • 1 → c = 1 := fun hc => by
    have := congrFun (congrFun hc 0) 0
    simpa using this.symm
  have hi₁ : Function.Injective φ₁ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨c, hc⟩ := (hψ1 (a, 1)).mp ha
    rw [InvClassU.bdPlane_apply, map_one] at hc
    obtain ⟨h11, h22⟩ := hscal hc
    rw [hc1 h22, one_smul] at h11
    exact planeHom_eq_one h h11
  have hi₂ : Function.Injective φ₂ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    obtain ⟨c, hc⟩ := (hψ1 (1, b)).mp hb
    rw [InvClassU.bdPlane_apply, map_one] at hc
    obtain ⟨h11, h22⟩ := hscal hc
    rw [hc1 h11, one_smul] at h22
    exact planeHom_eq_one h h22
  have hC : ∀ x, hypProj h 2 0 (ψ x) ∈
      Subgroup.centralizer ({hypProj h 2 0 A} : Set (hypPSU h 2 0)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact (hψA x).symm
  refine ⟨φ₁.range, φ₂.range, ?_, ?_, ?_, ⟨(MonoidHom.ofInjective hi₁).symm⟩,
    ⟨(MonoidHom.ofInjective hi₂).symm⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact hC (a, 1)
  · rintro _ ⟨b, rfl⟩
    exact hC (1, b)
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [hφ₁, hφ₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem false_of_D1 (hp : p ≠ 2) (h8 : p ^ f % 8 ≠ 7) {A : hypSU h 2 0} {d : K}
    (hd : h.norm d = 1) {v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => d) (fun _ => -d) i • v i) : False := by
  have hdA : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det =
      -d ^ 4 := by
    rw [InvClassU.det_of_eigen h (by simp) (G := 1) (Gi := 1)
      (by ext i j; simp [hv, one_apply]) (Matrix.one_mul 1) hAv]
    simp [Fintype.prod_sum_type]
    ring
  have hd4 : d ^ 4 = -1 := by
    rw [(mem_hypSU.mp A.2).2] at hdA
    linear_combination hdA
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf d = 2 ^ (2 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hd4]
      intro h1
      exact h2 (by linear_combination -h1)
    · rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hd4]
      norm_num
  have hN : d ^ (p ^ f + 1) = 1 := by rw [← h.norm_eq_pow]; exact hd
  have hdvd : 2 ^ (2 + 1) ∣ p ^ f + 1 := hord ▸ orderOf_dvd_of_pow_eq_one hN
  norm_num at hdvd
  omega

theorem orderOf_mk_eq_two {A : hypSU h 2 0} (hz : orderOf (hypProj h 2 0 A) = 2) :
    orderOf (QuotientGroup.mk ⟨A, A.2.1⟩ : hypUnitaryMod h 2 0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have hpow : hypProj h 2 0 A ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hz])
    have hA2 : A ^ 2 ∈ hypScalars h 2 0 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_pow]
      exact hpow
    obtain ⟨c, hc, -, hcA⟩ := mem_normOneScalars.1 hA2
    exact ⟨c, hc, pow_zero c, hcA⟩
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hc, -, hcA⟩ := mem_normOneScalars.1 h1
    have hc4 : c ^ (2 * 2 + 0) = 1 := by
      apply Units.ext
      have := congrArg (fun g : GL (HypIndex 2 0) K => (Units.val g).det) hcA
      simp only at this
      rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
        Finset.card_univ, InvClassU.card_hypIndex_two_zero] at this
      change ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = _
        at this
      rw [(mem_hypSU.mp A.2).2] at this
      rw [Units.val_pow_eq_pow_val, Units.val_one, this]
    have hmem : A ∈ hypScalars h 2 0 := ⟨c, hc, hc4, hcA⟩
    rw [← ker_hypProj, MonoidHom.mem_ker] at hmem
    rw [hmem, orderOf_one] at hz
    exact absurd hz (by norm_num)

theorem uni_shape (hp : p ≠ 2) (h8 : p ^ f % 8 ≠ 7) {z : hypPSU h 2 0} (hz : orderOf z = 2) :
    TwoSL2Shape (hypPSU h 2 0) z h.fixedField ∨ NormalSimpleShape (hypPSU h 2 0) z := by
  obtain ⟨A, rfl⟩ := hypProj_surjective h 2 0 z
  obtain ⟨l, hl0, hAA, hcases⟩ := InvClassU.classify_inv_U4 h hp A.2.1 (orderOf_mk_eq_two h hz)
  rcases hcases with ⟨-, ⟨v, hv, hAv⟩ | ⟨d, hd, v, hv, hAv⟩⟩ |
    ⟨-, e, g, hAe, hAg, hee, hgg, heg⟩
  · exact Or.inl (twoSL2Shape_of_t2 h hp hv hAv)
  · exact (false_of_D1 h hp h8 hd hv hAv).elim
  · exact Or.inr (normalSimpleShape_of_paired h hp hl0 hAA hAe hAg hee hgg heg)

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
