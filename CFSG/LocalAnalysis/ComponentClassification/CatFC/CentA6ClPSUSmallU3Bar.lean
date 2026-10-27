module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallU3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallBase

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatalogueBOrthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)

section Dihedral

variable {k : Type} [Field k]

theorem psu_traceZero_dihedral (ζ : kˣ) (h8 : ζ ^ 8 = 1) (h4 : ζ ^ 4 ≠ 1) :
    ∃ o₁ o₂ : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm k),
      o₁ ^ 2 = 1 ∧ o₂ ^ 2 = 1 ∧ (o₁ * o₂) ^ 8 = 1 ∧ (o₁ * o₂) ^ 4 ≠ 1 := by
  let g₁ : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0]
    (by simp [Matrix.det_fin_two_of])
  let g₂ : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, (ζ : k); 1, 0]
    (by simp [Matrix.det_fin_two_of])
  let d : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (ζ : k)]
    (by simp [Matrix.det_fin_two_of])
  have hg₁ : g₁ ^ 2 = 1 := by
    apply Units.ext
    simp [g₁, pow_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  have hg₂ : g₂ ^ 2 = GeneralLinearGroup.scalar (Fin 2) ζ := by
    apply Units.ext
    simp [g₂, pow_two, Matrix.mul_fin_two, GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hg₁₂ : g₁ * g₂ = d := by
    apply Units.ext
    simp [g₁, g₂, d, Matrix.mul_fin_two]
  have hdpow : ∀ m : ℕ, ((d ^ m : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; 0, (ζ : k) ^ m] := by
    intro m
    induction m with
    | zero => simp [Matrix.one_fin_two]
    | succ m ih =>
      rw [pow_succ, Units.val_mul, ih]
      simp [d, Matrix.mul_fin_two, pow_succ]
  refine ⟨traceZeroOrthogonalAction g₁, traceZeroOrthogonalAction g₂, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hg₁, map_one]
  · rw [← map_pow, hg₂, traceZeroOrthogonalAction_scalar]
  · rw [← map_mul, ← map_pow, hg₁₂]
    have : d ^ 8 = 1 := by
      apply Units.ext
      rw [hdpow, Units.val_one, Matrix.one_fin_two]
      have h8' : (ζ : k) ^ 8 = 1 := by
        have := congrArg Units.val h8
        simpa using this
      rw [h8']
    rw [this, map_one]
  · rw [← map_mul, ← map_pow, hg₁₂]
    intro H
    obtain ⟨c, hc⟩ := (traceZeroOrthogonalAction_eq_one_iff _).mp H
    have h00 := congrArg (fun M : GL (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k) 0 0) hc
    have h11 := congrArg (fun M : GL (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k) 1 1) hc
    simp only [GeneralLinearGroup.coe_scalar, hdpow] at h00 h11
    simp at h00 h11
    apply h4
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← h11, h00, Units.val_one]

end Dihedral

section Zeta

theorem psu_exists_unit_order_eight {k : Type} [Field k] (hk : Nat.card k = 9) :
    ∃ ζ : kˣ, ζ ^ 8 = 1 ∧ ζ ^ 4 ≠ 1 := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hc : Nat.card kˣ = 8 := by rw [Nat.card_units, hk]
  rw [hc] at hζ
  refine ⟨ζ, ?_, fun h => ?_⟩
  · have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  · have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    omega

end Zeta

section SignPair

variable {G : Type} [Group G]

theorem psu_sign_pair (s : G) (hs : s ∈ Subgroup.center G) (hs2 : s ^ 2 = 1) {ε₁ ε₂ Y₁ Y₂ : G}
    (h₁ : ε₁ = 1 ∨ ε₁ = s) (h₂ : ε₂ = 1 ∨ ε₂ = s) (hY₁ : Y₁ ^ 2 = 1) (hY₂ : Y₂ ^ 2 = 1)
    (h8 : (Y₁ * Y₂) ^ 8 = 1) (h4 : (Y₁ * Y₂) ^ 4 ≠ 1) :
    (ε₁ * Y₁) ^ 2 = 1 ∧ (ε₂ * Y₂) ^ 2 = 1 ∧ ((ε₁ * Y₁) * (ε₂ * Y₂)) ^ 8 = 1 ∧
      ((ε₁ * Y₁) * (ε₂ * Y₂)) ^ 4 ≠ 1 := by
  have hc : ∀ x : G, Commute s x := fun x => (Subgroup.mem_center_iff.mp hs x).symm
  have hcen : ∀ ε : G, (ε = 1 ∨ ε = s) → (∀ x : G, Commute ε x) ∧ ε ^ 2 = 1 := by
    rintro ε (rfl | rfl)
    · exact ⟨fun x => Commute.one_left x, one_pow 2⟩
    · exact ⟨hc, hs2⟩
  obtain ⟨hε₁c, hε₁2⟩ := hcen ε₁ h₁
  obtain ⟨hε₂c, hε₂2⟩ := hcen ε₂ h₂
  have e : (ε₁ * Y₁) * (ε₂ * Y₂) = (ε₁ * ε₂) * (Y₁ * Y₂) := by
    have h3 : Y₁ * ε₂ = ε₂ * Y₁ := (hε₂c Y₁).symm.eq
    calc (ε₁ * Y₁) * (ε₂ * Y₂) = ε₁ * (Y₁ * ε₂) * Y₂ := by group
      _ = ε₁ * (ε₂ * Y₁) * Y₂ := by rw [h3]
      _ = (ε₁ * ε₂) * (Y₁ * Y₂) := by group
  have hcc : Commute (ε₁ * ε₂) (Y₁ * Y₂) := (hε₁c _).mul_left (hε₂c _)
  have hc2 : (ε₁ * ε₂) ^ 2 = 1 := by
    rw [(hε₁c ε₂).mul_pow, hε₁2, hε₂2, one_mul]
  have hc4 : (ε₁ * ε₂) ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hc2, one_pow]
  have hc8 : (ε₁ * ε₂) ^ 8 = 1 := by rw [show 8 = 2 * 4 from rfl, pow_mul, hc2, one_pow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(hε₁c Y₁).mul_pow, hε₁2, hY₁, one_mul]
  · rw [(hε₂c Y₂).mul_pow, hε₂2, hY₂, one_mul]
  · rw [e, hcc.mul_pow, hc8, h8, one_mul]
  · rw [e, hcc.mul_pow, hc4, one_mul]
    exact h4

end SignPair

section Adjust

variable {K : Type} [Field K] {p f n : ℕ} (h : UnitaryFieldData p f K)

theorem psu_negOne_mem (τ₀ : (Fin n → K) →ₛₗ[h.bar] (Fin n → K)) :
    (-1 : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈ commutingUnitary (idForm h n) τ₀ := by
  refine ⟨fun x y => ?_, fun v => ?_⟩
  · simp [Units.coe_neg_one, map_neg]
  · simp [Units.coe_neg_one, map_neg]

theorem psu_negOne_central :
    (-1 : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈
      Subgroup.center (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
  Subgroup.mem_center_iff.mpr fun g => Units.ext (by simp)

theorem psu_adjust_det (hn : Odd n) (τ₀ : (Fin n → K) →ₛₗ[h.bar] (Fin n → K))
    (Y : LinearMap.GeneralLinearGroup K (Fin n → K)) (hY : Y ∈ commutingUnitary (idForm h n) τ₀)
    (hY2 : Y ^ 2 = 1) :
    ∃ ε : LinearMap.GeneralLinearGroup K (Fin n → K), (ε = 1 ∨ ε = -1) ∧
      ε * Y ∈ commutingUnitary (idForm h n) τ₀ ∧ ε * Y ∈ sesqSpecialUnitaryGroup (idForm h n) := by
  have hd2 : LinearMap.det (Y : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.det (Y : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    have := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      LinearMap.det (u : (Fin n → K) →ₗ[K] (Fin n → K))) hY2
    simpa [pow_two, ← map_mul] using this
  rcases mul_self_eq_one_iff.mp hd2 with h1 | h1
  · refine ⟨1, Or.inl rfl, by simpa using hY, mem_sesqSpecialUnitaryGroup.mpr ⟨?_, ?_⟩⟩
    · simpa using hY.1
    · simpa using h1
  · have hmem := mul_mem (psu_negOne_mem h τ₀) hY
    refine ⟨-1, Or.inr rfl, hmem, mem_sesqSpecialUnitaryGroup.mpr ⟨hmem.1, ?_⟩⟩
    have hneg : LinearMap.det (((-1 : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K))) = -1 := by
      have e : (((-1 : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          (Fin n → K) →ₗ[K] (Fin n → K))) = (-1 : K) • (1 : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        refine LinearMap.ext fun v => ?_
        simp
      rw [e, LinearMap.det_smul, map_one, mul_one, Module.finrank_fin_fun, hn.neg_one_pow]
    rw [Units.val_mul, map_mul, hneg, h1]
    norm_num

end Adjust

section Descent

variable {K : Type} [Field K] (h : UnitaryFieldData 3 2 K)

theorem psu_graph_three_two_equiv (A : primeFormUnitary h (idGram K 3)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    Nonempty (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm h.fixedField) ≃*
      commutingUnitary (idForm h 3)
        (semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hn : 3 ≤ 3 := le_rfl
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    have h1 := pow_orderOf_eq_one (primeFormPsi h hC ⟨A, φ⟩)
    rw [hA] at h1
    rw [map_mul, ← pow_two]
    exact h1
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hx2
  have hmapA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin 3) K) * glAut φ (A : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ := CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h
    c.ne_zero hAc
  have hτ₀B := CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  have hfin : finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hnV : 1 ≤ finrank K (Fin 3 → K) := by omega
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hnV (idForm_isSymm h 3) (idForm_separatingLeft h 3) τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 3 ^ 2 := h.card_fixedField
  have hfinn : finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 3 := hfinW.trans hfin
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h (by norm_num) h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    let Φ' := Φ.trans (MulEquiv.subgroupCongr
      (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    have hodd9 : Odd (Nat.card h.fixedField) := by rw [hkc]; exact ⟨4, by norm_num⟩
    have hK3 : Nat.card h.fixedField ≠ 3 := by rw [hkc]; norm_num
    obtain ⟨d, ψ, e', -⟩ := orthogonal_three_derived hodd9 hK3 _ hQ hfinn
    exact ⟨e'.symm.trans Φ'.symm⟩
  · exfalso
    obtain ⟨B', -, halt, hnd, hEven, Φ, -⟩ := hB2 hμ1
    obtain ⟨r, hr⟩ := hEven
    omega

end Descent

section Lift

variable {K : Type} [Field K] {n p f : ℕ} (h : UnitaryFieldData p f K)

theorem psu_toLin_pow_eq_one_iff (g : ↥(gramSU h (idGram K n)))
    (w : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hg : Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) = w) (m : ℕ) :
    g ^ m = 1 ↔ w ^ m = 1 := by
  subst hg
  rw [← Subtype.coe_inj, Subgroup.coe_pow, OneMemClass.coe_one,
    ← MulEquiv.map_eq_one_iff Matrix.GeneralLinearGroup.toLin, map_pow]

theorem psu_toLin_mul (g₁ g₂ : ↥(gramSU h (idGram K n))) :
    Matrix.GeneralLinearGroup.toLin ((g₁ * g₂ : ↥(gramSU h (idGram K n))) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin n) K) *
        Matrix.GeneralLinearGroup.toLin (g₂ : GL (Fin n) K) := by
  rw [Subgroup.coe_mul, map_mul]

theorem psu_lift_relations (g₁ g₂ : ↥(gramSU h (idGram K n)))
    (w₁ w₂ : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hg₁ : Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin n) K) = w₁)
    (hg₂ : Matrix.GeneralLinearGroup.toLin (g₂ : GL (Fin n) K) = w₂)
    (h1 : w₁ ^ 2 = 1) (h2 : w₂ ^ 2 = 1) (h8 : (w₁ * w₂) ^ 8 = 1) (h4 : (w₁ * w₂) ^ 4 ≠ 1) :
    g₁ ^ 2 = 1 ∧ g₂ ^ 2 = 1 ∧ (g₁ * g₂) ^ 8 = 1 ∧ (g₁ * g₂) ^ 4 ≠ 1 := by
  have hm : Matrix.GeneralLinearGroup.toLin ((g₁ * g₂ : ↥(gramSU h (idGram K n))) :
      GL (Fin n) K) = w₁ * w₂ := by rw [psu_toLin_mul, hg₁, hg₂]
  exact ⟨(psu_toLin_pow_eq_one_iff h g₁ w₁ hg₁ 2).mpr h1, (psu_toLin_pow_eq_one_iff h g₂ w₂ hg₂ 2).mpr h2,
    (psu_toLin_pow_eq_one_iff h _ _ hm 8).mpr h8,
    fun H => h4 ((psu_toLin_pow_eq_one_iff h _ _ hm 4).mp H)⟩

end Lift

section Pair

variable {K : Type} [Field K] (h : UnitaryFieldData 3 2 K)

theorem psu_fixed_pair {σ : MulAut (primeFormP h (idGram K 3))} (g₁ g₂ : ↥(gramSU h (idGram K 3)))
    (hf₁ : (QuotientGroup.mk g₁ : primeFormP h (idGram K 3)) ∈ fixedSubgroup σ)
    (hf₂ : (QuotientGroup.mk g₂ : primeFormP h (idGram K 3)) ∈ fixedSubgroup σ)
    (e1 : g₁ ^ 2 = 1) (e2 : g₂ ^ 2 = 1) (e8 : (g₁ * g₂) ^ 8 = 1) (e4 : (g₁ * g₂) ^ 4 ≠ 1) :
    ∃ a₁ a₂ : ↥(fixedSubgroup σ), a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ (a₁ * a₂) ^ 8 = 1 ∧
      (a₁ * a₂) ^ 4 ≠ 1 := by
  refine ⟨⟨_, hf₁⟩, ⟨_, hf₂⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← QuotientGroup.mk_pow, e1, QuotientGroup.mk_one]
    rfl
  · apply Subtype.ext
    rw [Subgroup.coe_pow, ← QuotientGroup.mk_pow, e2, QuotientGroup.mk_one]
    rfl
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, e8,
      QuotientGroup.mk_one]
    rfl
  · intro H
    have H' : ((QuotientGroup.mk g₁ : primeFormP h (idGram K 3)) * QuotientGroup.mk g₂) ^ 4 = 1 :=
      congrArg Subtype.val H
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow] at H'
    exact e4 (psu_ker_three_two h _ H')

theorem psu_graph_three_two_pair (A : primeFormUnitary h (idGram K 3)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (Ψ : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm h.fixedField) ≃*
      commutingUnitary (idForm h 3)
        (semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :
    ∃ a₁ a₂ : ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
      a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ (a₁ * a₂) ^ 8 = 1 ∧ (a₁ * a₂) ^ 4 ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hτ₀
  obtain ⟨ζ, hζ8, hζ4⟩ := psu_exists_unit_order_eight (k := h.fixedField)
    (by rw [h.card_fixedField]; norm_num)
  obtain ⟨o₁, o₂, ho₁, ho₂, ho8, ho4⟩ := psu_traceZero_dihedral ζ hζ8 hζ4
  have hY₁ : ((Ψ o₁ : commutingUnitary (idForm h 3) τ₀) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, ho₁, map_one, OneMemClass.coe_one]
  have hY₂ : ((Ψ o₂ : commutingUnitary (idForm h 3) τ₀) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, ho₂, map_one, OneMemClass.coe_one]
  have hY8 : (((Ψ o₁ : commutingUnitary (idForm h 3) τ₀) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) * (Ψ o₂ : commutingUnitary (idForm h 3) τ₀)) ^ 8
      = 1 := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, ho8, map_one,
      OneMemClass.coe_one]
  have hY4 : (((Ψ o₁ : commutingUnitary (idForm h 3) τ₀) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) * (Ψ o₂ : commutingUnitary (idForm h 3) τ₀)) ^ 4
      ≠ 1 := by
    intro H
    apply ho4
    apply Ψ.injective
    apply Subtype.ext
    rw [map_pow, map_mul, map_one, Subgroup.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one]
    exact H
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨ε₁, hε₁, hw₁, hs₁⟩ := psu_adjust_det h hodd τ₀ _ (Ψ o₁).2 hY₁
  obtain ⟨ε₂, hε₂, hw₂, hs₂⟩ := psu_adjust_det h hodd τ₀ _ (Ψ o₂).2 hY₂
  have hneg2 : (-1 : LinearMap.GeneralLinearGroup K (Fin 3 → K)) ^ 2 = 1 := by
    rw [pow_two]
    exact Units.ext (by simp)
  obtain ⟨hw₁sq, hw₂sq, hw8, hw4⟩ := psu_sign_pair (-1) psu_negOne_central hneg2 hε₁ hε₂ hY₁ hY₂
    hY8 hY4
  obtain ⟨g₁, hg₁, hf₁⟩ := psu_exists_elt_fixed_graph h A φ hφ _ hs₁ (fun v => hw₁.2 v)
  obtain ⟨g₂, hg₂, hf₂⟩ := psu_exists_elt_fixed_graph h A φ hφ _ hs₂ (fun v => hw₂.2 v)
  obtain ⟨e1, e2, e8, e4⟩ := psu_lift_relations h g₁ g₂ _ _ hg₁ hg₂ hw₁sq hw₂sq hw8 hw4
  exact psu_fixed_pair h g₁ g₂ hf₁ hf₂ e1 e2 e8 e4

end Pair

section Class

variable {K : Type} [Field K] (h : UnitaryFieldData 3 2 K)

theorem psu_small_three_two (hO : LieOrderFormulasInput)
    (σ : MulAut (primeFormP h (idGram K 3))) (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hA : A6Hyp σ D) : A6SmallConcl .PSU 3 2 σ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 3 ^ 2 = 2) := by norm_num
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq σ
  have hff : primeFormFieldFactor h hC hn hq σ = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one σ
    rw [hσ] at h1
    rw [h1, map_one]
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · exfalso
    have hAσ : σ = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    subst hAσ
    exact psu_inner_three_two_false hO h A hσ hA
  · subst hAφ
    refine ⟨fun hin => absurd hin (psu_graph_not_inner h hn hq A φ hφ), fun _ hle => ?_⟩
    obtain ⟨Ψ⟩ := psu_graph_three_two_equiv h A φ hφ hσ
    obtain ⟨a₁, a₂, ha₁, ha₂, ha8, ha4⟩ := psu_graph_three_two_pair h A φ hφ Ψ
    have hone : ¬ (a₁ ∈ D ∧ a₂ ∈ D) := by
      rintro ⟨h1, h2⟩
      exact ha4 (hA.psu_pow_four _ (D.mul_mem h1 h2) ha8)
    obtain ⟨x, hx2, hxD⟩ : ∃ x : ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)),
        orderOf x = 2 ∧ x ∉ D := by
      by_cases h1 : a₁ ∈ D
      · have h2 : a₂ ∉ D := fun h2 => hone ⟨h1, h2⟩
        exact ⟨a₂, orderOf_eq_prime ha₂ (fun h0 => h2 (by rw [h0]; exact D.one_mem)), h2⟩
      · exact ⟨a₁, orderOf_eq_prime ha₁ (fun h0 => h1 (by rw [h0]; exact D.one_mem)), h1⟩
    refine ⟨?_, Or.inl ⟨x, hx2, hxD⟩⟩
    have hDne : D ≠ ⊤ := fun h0 => hxD (h0 ▸ Subgroup.mem_top x)
    have hidx : 2 ≤ D.index := by
      have h1 : D.index ≠ 1 := fun h1 => hDne (Subgroup.index_eq_one.mp h1)
      have h2 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have h3 := Subgroup.card_mul_index D
    rw [hA.card_D] at h3
    omega

end Class

end CFSG.ComponentClassification.CatFC
