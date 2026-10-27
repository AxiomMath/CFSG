module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterAut
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Regular
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCycle

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix Module CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit
  CFSG.ComponentClassification

variable {K : Type} [Field K]

theorem map_eq_of_map_stabilizer [Finite K] [CharP K 2] {A : GL (Fin 3) K}
    {W : Submodule K (Fin 3 → K)} {d : ℕ} (hd : d = 1 ∨ d = 2) (hW : finrank K W = d)
    (h : (stabilizer W).map (CatalogueBHigherLinearAction.slConjugation 3 K A).toMonoidHom =
      stabilizer W) : W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinjA : Function.Injective (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
    intro v w hvw
    have hAA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
        = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1 := congrArg (fun x => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) hvw
    simp only [mulVecLin_apply, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h1
    exact h1
  have hW' : finrank K (W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) = d := by
    rw [← (Submodule.equivMapOfInjective _ hinjA W).finrank_eq, hW]
  have hbot : ∀ {U : Submodule K (Fin 3 → K)}, finrank K U = d → ⊥ < U ∧ U < ⊤ := by
    intro U hU
    refine ⟨bot_lt_iff_ne_bot.mpr fun h0 => ?_, lt_top_iff_ne_top.mpr fun h0 => ?_⟩
    · rw [h0, finrank_bot] at hU; omega
    · rw [h0, finrank_top, finrank_fin_fun] at hU; omega
  have hproj : (projStabilizer W) =
      (projStabilizer W).map (conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K) := by
    conv_lhs => rw [projStabilizer, ← h]
    rw [projStabilizer, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [(standard_automorphism_transport (K := K) (n := 3)).2.2.2.2.2.2.1 A W] at hproj
  exact ((maximal_parabolics (K := K) (n := 3) 2 (by norm_num)).2.1 (hbot hW) (hbot hW')
    hproj).symm

theorem three_pow_aut_diagonal [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card K = 2 ^ f) (h3 : ¬ 3 ∣ f) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {d : ℕ}
    (hd : d = 1 ∨ d = 2) {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2)
    (hsJ : s ∈ stabilizer (flagSpace 3 K d))
    {β : MulAut (SpecialLinearGroup (Fin 3) K)} {k : ℕ} (hβ : β ^ 3 ^ k = 1) {c : K}
    (hc3 : c ^ 3 = 1) (hβs : (β s : Matrix (Fin 3) (Fin 3) K) = c • (s : Matrix (Fin 3) (Fin 3) K))
    (hβJ : (stabilizer (flagSpace 3 K d)).map β.toMonoidHom = stabilizer (flagSpace 3 K d)) :
    ∃ (A : GL (Fin 3) K) (a : Fin 3 → K),
      β = CatalogueBHigherLinearAction.slConjugation 3 K A ∧
        ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i := by
  obtain ⟨A, hA⟩ := exists_slConjugation_of_three_pow hf hk h3 hβ
  subst hA
  set S : Matrix (Fin 3) (Fin 3) K := (s : Matrix (Fin 3) (Fin 3) K) with hS
  have hAA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAS : (A : Matrix (Fin 3) (Fin 3) K) * S = c • (S * (A : Matrix (Fin 3) (Fin 3) K)) := by
    have h := hβs
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, ← hS] at h
    calc (A : Matrix (Fin 3) (Fin 3) K) * S
        = ((A : Matrix (Fin 3) (Fin 3) K) * S * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
            * (A : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc ((A : Matrix (Fin 3) (Fin 3) K) * S), hAA, Matrix.mul_one]
      _ = c • (S * (A : Matrix (Fin 3) (Fin 3) K)) := by rw [h, Matrix.smul_mul]
  have hAinj : ∀ v, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = 0 → v = 0 := fun v hv => by
    have := congrArg (fun x => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) hv
    simpa [Matrix.mulVec_mulVec, hAA] using this
  let r : Fin 3 → K := ![1, ω, ω ^ 2]
  have hr : Function.Injective r := cubeRoots_injective hω1 hω3
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    have : ω ≠ 0 := fun h => by rw [h] at hω3; simp at hω3
    fin_cases i <;> simp [r, this]
  have hs : ∀ i, S *ᵥ b i = r i • b i := by
    refine forall_fin_three ?_ ?_ ?_
    · show S *ᵥ b 0 = (1 : K) • b 0
      rw [one_smul]; exact hb0
    · exact hb1
    · exact hb2
  have hWfin : Module.finrank K (flagSpace 3 K d) = d := by
    rcases hd with rfl | rfl <;> exact finrank_flagSpace (by norm_num)
  have hW0 : flagSpace 3 K d ≠ ⊥ := fun h0 => by
    rw [h0, finrank_bot] at hWfin; omega
  have hWt : flagSpace 3 K d ≠ ⊤ := fun h0 => by
    rw [h0, finrank_top, finrank_fin_fun] at hWfin; omega
  have hWS : ∀ v ∈ flagSpace 3 K d, S *ᵥ v ∈ flagSpace 3 K d := fun v hv => by
    have hmap := mem_stabilizer.mp hsJ
    have hmem : S *ᵥ v ∈ (flagSpace 3 K d).map (mulVecLin (s : Matrix (Fin 3) (Fin 3) K)) :=
      ⟨v, hv, rfl⟩
    rwa [hmap] at hmem
  have hWA := map_eq_of_map_stabilizer hd hWfin hβJ
  have hWA' : ∀ v ∈ flagSpace 3 K d, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ flagSpace 3 K d :=
    fun v hv => by
      have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈
          (flagSpace 3 K d).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := ⟨v, hv, rfl⟩
      rwa [hWA] at hmem
  have hc1 : c = 1 := eq_one_of_invariant hb hs hr hr0 hc3 hAS hAinj hW0 hWt hWS hWA'
  rw [hc1, one_smul] at hAS
  have hex := fun i => exists_mulVec_eq_smul_of_commute hb hs hr hAS i
  choose a ha using hex
  exact ⟨A, a, rfl, ha⟩

theorem not_nine_dvd_two_pow_sub_one {f : ℕ} (h3 : ¬ 3 ∣ f) : ¬ 9 ∣ 2 ^ f - 1 := by
  intro h9
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hmod : 2 ^ f % 9 = 1 := by omega
  have hr : 2 ^ f % 9 = 2 ^ (f % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod f 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [hr] at hmod
  have : f % 6 = 0 := by
    have hlt : f % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases hf : f % 6 <;> simp_all
  exact h3 (by omega)

theorem pow_three_eq_one_of_pow_three_pow {K : Type*} [Field K] [Finite K] {f : ℕ}
    (hk : Nat.card K = 2 ^ f) (h3 : ¬ 3 ∣ f) {x : K} (hx0 : x ≠ 0) {k : ℕ}
    (hx : x ^ 3 ^ k = 1) : x ^ 3 = 1 := by
  let u : Kˣ := Units.mk0 x hx0
  have hu : u ^ 3 ^ k = 1 := Units.ext (by simpa [u] using hx)
  have h1 : orderOf u ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ 2 ^ f - 1 := by
    rw [← hk, ← Nat.card_units]
    exact orderOf_dvd_natCard u
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    apply not_nine_dvd_two_pow_sub_one h3
    refine dvd_trans ?_ h2
    rw [hord]
    exact (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)
  have : orderOf u ∣ 3 := by
    rw [hord]
    interval_cases j <;> simp
  have h := orderOf_dvd_iff_pow_eq_one.mp this
  simpa [u] using congrArg Units.val h

section Cube

variable [Finite K]

omit [Finite K] in
theorem slConjugation_pow_matrix (A : GL (Fin 3) K) (m : ℕ) (g : SpecialLinearGroup (Fin 3) K) :
    (((CatalogueBHigherLinearAction.slConjugation 3 K A ^ m) g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      ((A ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
        (((A ^ m)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [← map_pow, CatalogueBHigherLinearAction.slConjugation_matrix]

theorem slConjugation_cube_eq_one {f : ℕ} (hk : Nat.card K = 2 ^ f) (h3 : ¬ 3 ∣ f) {ω : K}
    (hω3 : ω ^ 3 = 1) {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) {A : GL (Fin 3) K}
    {a : Fin 3 → K} (hAa : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i) {k : ℕ}
    (hk3 : CatalogueBHigherLinearAction.slConjugation 3 K A ^ 3 ^ k = 1) :
    CatalogueBHigherLinearAction.slConjugation 3 K A ^ 3 = 1 := by
  have hb0' : ∀ i, b i ≠ 0 := fun i => hb.ne_zero i
  have ha0 : ∀ i, a i ≠ 0 := fun i h0 => by
    have := hAa i
    rw [h0, zero_smul] at this
    have hAA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)
        = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrArg (fun x => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) this
    simp only [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact hb0' i h2
  obtain ⟨S, hSdet, hS0, hS1, hS2, -⟩ := exists_cycle hω3 hb hb0 hb1 hb2
  let σ : SpecialLinearGroup (Fin 3) K := ⟨S, hSdet⟩
  have hσ := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    (congrArg (fun φ => φ σ) hk3)
  simp only [MulAut.one_apply] at hσ
  rw [slConjugation_pow_matrix] at hσ
  have hcomm : ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S =
      S * ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have hAA : (((A ^ 3 ^ k)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S
        = (((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S *
            (((A ^ 3 ^ k)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc (((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S), hAA,
            Matrix.mul_one]
      _ = S * ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [show (((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S *
            (((A ^ 3 ^ k)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = S from hσ]
  have hApow : ∀ i, ((A ^ 3 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i =
      (a i) ^ 3 ^ k • b i := fun i => by
    rw [Units.val_pow_eq_pow_val]
    exact pow_mulVec_of_mulVec_eq_smul (hAa i) _
  have hcyc : ∀ (i j : Fin 3), S *ᵥ b i = b j → a j ^ 3 ^ k = a i ^ 3 ^ k := by
    intro i j hij
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ b i) hcomm
    simp only [← Matrix.mulVec_mulVec, hApow, Matrix.mulVec_smul, hij] at h
    exact smul_left_injective K (hb0' j) h
  have e01 := hcyc 0 1 hS0
  have e12 := hcyc 1 2 hS1
  have hall : ∀ i, a i ^ 3 = a 0 ^ 3 := by
    intro i
    have hi : a i ^ 3 ^ k = a 0 ^ 3 ^ k := by
      fin_cases i
      · rfl
      · exact e01
      · exact e12.trans e01
    have : (a i / a 0) ^ 3 = 1 := by
      refine pow_three_eq_one_of_pow_three_pow hk h3 (div_ne_zero (ha0 i) (ha0 0)) (k := k) ?_
      rw [div_pow, hi, div_self (pow_ne_zero _ (ha0 0))]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ (ha0 0))] at this
    exact this
  have hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (a 0 ^ 3)
      (pow_ne_zero _ (ha0 0))) := by
    apply Units.ext
    refine eq_of_mulVec_eq hb fun i => ?_
    rw [Units.val_pow_eq_pow_val, pow_mulVec_of_mulVec_eq_smul (hAa i), hall i,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [← map_pow, hA3, CatalogueBHigherLinearAction.slConjugation_scalar]

end Cube

theorem slConjugation_comm_of_diag {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    {A A' : GL (Fin 3) K} {a a' : Fin 3 → K}
    (hA : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i)
    (hA' : ∀ i, (A' : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a' i • b i) :
    CatalogueBHigherLinearAction.slConjugation 3 K A *
        CatalogueBHigherLinearAction.slConjugation 3 K A' =
      CatalogueBHigherLinearAction.slConjugation 3 K A' *
        CatalogueBHigherLinearAction.slConjugation 3 K A := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  refine eq_of_mulVec_eq hb fun i => ?_
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA', hA,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hA, hA', smul_smul, smul_smul, mul_comm]

end CFSG.HardMathSupport.Curtis.Coordinator
