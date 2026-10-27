module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionCentralizerRank
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_four_group_blockSwapJ {k : Type} [Field k] [CharP k 2] {n r : ℕ}
    (hnr : n = 2 * r) (hr : 2 ≤ r) :
    ∃ V : Subgroup (GL (Fin n) k),
      V ≤ matrixIsometryGroup (blockSwapJ n r : Matrix (Fin n) (Fin n) k) ∧
        IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  set J : Matrix (Fin n) (Fin n) k := blockSwapJ n r with hJdef
  have hJt : Jᵀ = J := blockSwapJ_transpose
  have hJ2 : J * J = 1 := blockSwapJ_mul_self (by omega)
  have hJapp : ∀ i j : Fin n, J i j = if (j : ℕ) = i + r ∨ (i : ℕ) = j + r then 1 else 0 :=
    fun _ _ => rfl
  have hJne : ∀ i j : Fin n, ¬((j : ℕ) = i + r ∨ (i : ℕ) = j + r) → J i j = 0 := by
    intro i j hij
    rw [hJapp]
    exact ite_eq_right_iff.2 fun hc => absurd hc hij
  set a : Fin n := ⟨r, by omega⟩ with ha
  set b : Fin n := ⟨r + 1, by omega⟩ with hb
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set u : Fin n → k := Pi.single a 1 with hu
  set v : Fin n → k := Pi.single b 1 with hv
  have hJu : J *ᵥ u = fun i => J i a := by rw [hu, mulVec_single_one]; rfl
  have hJv : J *ᵥ v = fun i => J i b := by rw [hv, mulVec_single_one]; rfl
  have huu : u ⬝ᵥ (J *ᵥ u) = 0 := by
    rw [hJu, hu, single_dotProduct, one_mul]
    exact hJne a a (by simp only [ha]; omega)
  have hvv : v ⬝ᵥ (J *ᵥ v) = 0 := by
    rw [hJv, hv, single_dotProduct, one_mul]
    exact hJne b b (by simp only [hb]; omega)
  have huv : u ⬝ᵥ (J *ᵥ v) = 0 := by
    rw [hJv, hu, single_dotProduct, one_mul]
    exact hJne a b (by simp only [ha, hb]; omega)
  have hvu : v ⬝ᵥ (J *ᵥ u) = 0 := by
    rw [hJu, hv, single_dotProduct, one_mul]
    exact hJne b a (by simp only [ha, hb]; omega)
  set N₁ := nilMatrix J 1 u with hN₁
  set N₂ := nilMatrix J 1 v with hN₂
  have h₁ : N₁ * N₁ = 0 := nilMatrix_mul_nilMatrix_eq_zero J 1 1 huu
  have h₂ : N₂ * N₂ = 0 := nilMatrix_mul_nilMatrix_eq_zero J 1 1 hvv
  have h₁₂ : N₁ * N₂ = N₂ * N₁ := by
    rw [nilMatrix_mul_nilMatrix_eq_zero J 1 1 huv, nilMatrix_mul_nilMatrix_eq_zero J 1 1 hvu]
  have hentry : ∀ (w : Fin n → k) (i j : Fin n),
      nilMatrix J 1 w i j = (J *ᵥ w) i * w j := fun w i j => by
    rw [nilMatrix, Matrix.smul_apply, vecMulVec_apply, one_smul]
  have hN₁e : N₁ i₀ a = 1 := by
    rw [hN₁, hentry, hJu, hu, Pi.single_eq_same, mul_one]
    show J i₀ a = 1
    rw [hJapp]
    split_ifs with hc
    · rfl
    · exact absurd (Or.inl (by simp only [ha, hi₀]; omega)) hc
  have hN₂e : N₂ i₀ a = 0 := by
    rw [hN₂, hentry, hv, Pi.single_eq_of_ne, mul_zero]
    intro hab
    have := congrArg Fin.val hab
    simp only [ha, hb] at this
    omega
  have hN₂e' : N₂ i₁ b = 1 := by
    rw [hN₂, hentry, hJv, hv, Pi.single_eq_same, mul_one]
    show J i₁ b = 1
    rw [hJapp]
    split_ifs with hc
    · rfl
    · exact absurd (Or.inl (by simp only [hb, hi₁]; omega)) hc
  have hN₁0 : N₁ ≠ 0 := fun h0 => by
    have := hN₁e
    rw [h0, Matrix.zero_apply] at this
    exact zero_ne_one this
  have hN₂0 : N₂ ≠ 0 := fun h0 => by
    have := hN₂e'
    rw [h0, Matrix.zero_apply] at this
    exact zero_ne_one this
  have hne : N₁ ≠ N₂ := fun h12 => by
    have := hN₁e
    rw [h12, hN₂e] at this
    exact zero_ne_one this
  exact exists_four_of_nil h₁ h₂ h₁₂ hN₁0 hN₂0 hne (unipotentGL_mem hJt hJ2 huu 1)
    (unipotentGL_mem hJt hJ2 hvv 1)

section Fixed

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
  {Cl : GL (Fin n) h.fixedField}
  (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)

include hCl in
theorem map_mem_gramSU_of_mem {g : GL (Fin n) h.fixedField}
    (hg : g ∈ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    GeneralLinearGroup.map h.fixedField.subtype g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) := by
  have := UnitaryFieldTransfer.fixedField_charP h
  refine ⟨UnitaryFieldTransfer.map_mem_primeFormUnitary h hCl hg, ?_⟩
  have hdet : (g : Matrix (Fin n) (Fin n) h.fixedField).det = 1 :=
    det_eq_one_of_mem ((Matrix.isUnit_iff_isUnit_det _).mp Cl.isUnit).ne_zero hg
  change ((g : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype).det = 1
  rw [show (g : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
    (h.fixedField.subtype : h.fixedField →+* K).mapMatrix (g : Matrix (Fin n) (Fin n) _) from rfl,
    ← RingHom.map_det, hdet, map_one]

@[expose] def fixedIsometrySU :
    matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) →*
      gramSU h (C : Matrix (Fin n) (Fin n) K) where
  toFun g := ⟨GeneralLinearGroup.map h.fixedField.subtype g, map_mem_gramSU_of_mem h hCl g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ (a : GL (Fin n) h.fixedField) b)

@[expose] def fixedIsometryProj :
    matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) →*
      primeFormP h (C : Matrix (Fin n) (Fin n) K) :=
  (QuotientGroup.mk' _).comp (fixedIsometrySU h hCl)

theorem fixedIsometryProj_injective (hn : 3 ≤ n) :
    Function.Injective (fixedIsometryProj h hCl) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [fixedIsometryProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hg
  obtain ⟨c, -, -, hc⟩ := hg
  exact UnitaryFieldTransfer.eq_one_of_map_eq_scalar h hn hc

theorem primeFormFieldAut_fixedIsometryProj (hC : IsPrimeFormGram C) {φ : K ≃+* K}
    (hφ : ∀ x, φ x = h.bar x)
    (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) :
    primeFormFieldAut h hC φ (fixedIsometryProj h hCl g) = fixedIsometryProj h hCl g := by
  change primeFormFieldAut h hC φ ((fixedIsometrySU h hCl g : gramSU h _) : primeFormP h _) = _
  rw [primeFormFieldAut_mk]
  congr 1
  exact Subtype.ext (UnitaryFieldTransfer.glAut_map_subtype h hφ (g : GL (Fin n) h.fixedField))

end Fixed

theorem exists_fixed_four_group_of_inner {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) (g : L) (hα : MulAut.conj g ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup (MulAut.conj g) ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have hZ := center_eq_bot_of_isSimpleGroup hL
  have hg2 : g ^ 2 = 1 := by
    have hmem : g ^ 2 ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut L => φ y) hα
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g ^ 2 = g ^ 2 * y * (g ^ 2)⁻¹ * g ^ 2 := by rw [h1]
        _ = g ^ 2 * y := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hrank : 2 ≤ CFSG.pRank 2 L := two_le_pRank_of_isQuasisimple_of_odd_center
    (isQuasisimple_of_isSimpleGroup hL) (by rw [hZ, Subgroup.card_bot]; exact odd_one)
  have hC := involution_centralizer_contains_four_group hrank hg2
  obtain ⟨A, hA, hAcard⟩ := exists_four_group_of_two_le_pRank hC
  have hA' : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 x x.2) }
  refine ⟨A.map (Subgroup.centralizer ({g} : Set L)).subtype, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    change MulAut.conj g (x : L) = x
    rw [MulAut.conj_apply, (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm,
      mul_inv_cancel_right]
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hAcard

theorem even_unitary_all_involution_fixed_four_group (L : Type) [Group L] [Finite L]
    [IsSimpleGroup L] (hLnab : ∃ a b : L, a * b ≠ b * a) {f n : ℕ}
    (hL : StatedClassicalModel L .PSU n 2 f) (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  by_cases hin : ∃ g : L, α = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hin
    exact exists_fixed_four_group_of_inner hLnab g hα
  obtain ⟨⟨hprime, hf, hn, hq⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have hq' : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => hq (by rw [h3.1, h3.2])
  have h : UnitaryFieldData 2 f K := ⟨hprime, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set P := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv h hC
  set ψ : L ≃* P := e.trans ((unitaryPSUEquiv h (by omega)).symm.trans χ.symm) with hψ
  set β : MulAut P := MulAut.congr ψ α with hβdef
  have hβapp : ∀ y, β y = ψ (α (ψ.symm y)) := fun y => rfl
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβin : β ∉ inner P := by
    rintro ⟨y, hy⟩
    apply hin
    refine ⟨ψ.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ : MulAut P => φ (ψ x)) hy
    simp only [MulAut.conj_apply, hβapp, MulEquiv.symm_apply_apply] at h1
    rw [MulAut.conj_apply]
    apply ψ.injective
    rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hβ1 : β ≠ 1 := fun h1 => hβin (h1 ▸ (inner P).one_mem)
  have hord : orderOf β = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hβ2 hβ1
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq' β hord
  rcases hcases with hid | hbar
  · exfalso
    apply hβin
    refine hDinner β ?_ hord
    rw [← ker_primeFormFieldFactor h hC hn hq', MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq' β hord hbar
  set φ := primeFormFieldFactor h hC hn hq' β with hφ
  have := UnitaryFieldTransfer.fixedField_charP h
  have := UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨Cl, hCl, V₀, hV₀le, hV₀ab, hV₀card⟩ : ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C₀ ∧
      ∃ V : Subgroup (GL (Fin n) h.fixedField),
        V ≤ matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ∧
        IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
    rcases hcase₀ with h1 | ⟨r, hr, hJ⟩
    · refine ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1], ?_⟩
      have hnk : (n, Nat.card h.fixedField) ≠ (3, 2) := by
        rw [UnitaryFieldData.card_fixedField h]
        exact hq
      obtain ⟨V, hVle, hVab, hVcard⟩ := (even_canonical_identity_isometry_four_group hn hnk).1
      exact ⟨V, by rw [Units.val_one]; exact hVle, hVab, hVcard⟩
    · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_, ?_⟩
      · rw [coe_blockSwapGL, hJ]
        ext i j
        simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
        split_ifs <;> simp
      · rw [coe_blockSwapGL]
        exact exists_four_group_blockSwapJ hr (by omega)
  set ι := fixedIsometryProj h hCl with hιdef
  set V₁ := (V₀.subgroupOf (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))).map ι
    with hV₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 V₀ := hV₀ab
  have hV₀' : IsElementaryAbelian 2 (V₀.subgroupOf
      (matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))) :=
    IsElementaryAbelian.subgroupOf hV₀le
  have hV₁card : Nat.card V₁ = 4 := by
    rw [hV₁, Subgroup.card_map_of_injective (fixedIsometryProj_injective h hCl hn),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀le).toEquiv]
    exact hV₀card
  have hV₁ab : IsElementaryAbelian 2 V₁ := IsElementaryAbelian.map ι
  have hV₁fix : ∀ y ∈ V₁, primeFormFieldAut h hC₀ φ y = y := by
    rintro _ ⟨g, -, rfl⟩
    exact primeFormFieldAut_fixedIsometryProj h hCl hC₀ hbar g
  set V₂ := V₁.map θ.toMonoidHom with hV₂
  have hV₂ab : IsElementaryAbelian 2 V₂ := IsElementaryAbelian.map _
  refine ⟨V₂.map ψ.symm.toMonoidHom, ?_, IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    change α (ψ.symm (θ y)) = ψ.symm (θ y)
    have h1 : β (θ y) = θ y := by
      rw [hθβ, MulEquiv.symm_apply_apply, hV₁fix y hy]
    rw [hβapp] at h1
    have h2 := congrArg ψ.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  · rw [Subgroup.card_map_of_injective ψ.symm.injective,
      Subgroup.card_map_of_injective θ.injective]
    exact hV₁card

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
