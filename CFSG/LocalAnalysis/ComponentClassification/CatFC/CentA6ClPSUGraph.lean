module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUInner

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

section Principles

variable {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K)
  (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)

include hφ in
theorem psu_graph_has27_false
    {D : Subgroup ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hD : A6Hyp (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) D) {G : Type} [Group G]
    (ι₀ : G →* LinearMap.GeneralLinearGroup K (Fin n → K)) (hι₀ : Function.Injective ι₀)
    (hmem : ∀ g, ι₀ g ∈ commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (h27 : PSUHas27Sub G) : False := by
  haveI : Finite K := h.finite
  obtain ⟨Q, _, j, hj, hperf, hd⟩ := h27
  obtain ⟨ρ, -, hρ⟩ := psu_exists_hom_fixed_graph h A φ hφ (ι₀.comp j) (hι₀.comp hj)
    (fun x => mem_sesqSpecialUnitaryGroup.mpr ⟨(hmem (j x)).1,
      psu_det_eq_one_of_commutator_eq_top hperf (ι₀.comp j) x⟩)
    (fun x v => (hmem (j x)).2 v)
  have h1 := hD.psu_central_quotient_dvd ρ hperf hρ
  exact (by decide : ¬ (27 ∣ 360)) (hd.trans h1)

include hφ in
theorem psu_graph_pair_false
    {D : Subgroup ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hD : A6Hyp (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) D) {G : Type} [Group G]
    (ι₀ : G →* LinearMap.GeneralLinearGroup K (Fin n → K)) (hι₀ : Function.Injective ι₀)
    (hmem : ∀ g, ι₀ g ∈ commutingUnitary (idForm h n)
      (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hp : PSUHasPair360 G) : False := by
  haveI : Finite K := h.finite
  obtain ⟨Q₁, Q₂, _, _, j₁, j₂, hj₁, hj₂, hQ₁, hQ₂, hc₁, hc₂, hcomm⟩ := hp
  obtain ⟨ρ₁, hρ₁, hk₁⟩ := psu_exists_hom_fixed_graph h A φ hφ (ι₀.comp j₁) (hι₀.comp hj₁)
    (fun x => mem_sesqSpecialUnitaryGroup.mpr ⟨(hmem (j₁ x)).1,
      psu_det_eq_one_of_commutator_eq_top hQ₁ (ι₀.comp j₁) x⟩)
    (fun x v => (hmem (j₁ x)).2 v)
  obtain ⟨ρ₂, hρ₂, hk₂⟩ := psu_exists_hom_fixed_graph h A φ hφ (ι₀.comp j₂) (hι₀.comp hj₂)
    (fun x => mem_sesqSpecialUnitaryGroup.mpr ⟨(hmem (j₂ x)).1,
      psu_det_eq_one_of_commutator_eq_top hQ₂ (ι₀.comp j₂) x⟩)
    (fun x v => (hmem (j₂ x)).2 v)
  refine hD.psu_commuting_pair_false ρ₁ ρ₂ hQ₁ hQ₂ hk₁ hk₂ hc₁ hc₂ ?_
  exact PSUIsTransfer.commute h hρ₁ hρ₂ (fun x y => by
    change ι₀ (j₁ x) * ι₀ (j₂ y) = ι₀ (j₂ y) * ι₀ (j₁ x)
    rw [← map_mul, ← map_mul, hcomm])

end Principles

theorem psuGraph_false (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n)
    (hnot : ¬ ((n = 3 ∧ f = 1) ∨ (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1)))
    (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2)
    {D : Subgroup ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hD : A6Hyp (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) D) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hfpos := h.one_le
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hx2
  have hmapA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ := CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h
    c.ne_zero hAc
  have hτ₀B := CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hnV : 1 ≤ finrank K (Fin n → K) := by omega
  have hno27 : ∀ {G : Type} [Group G]
      (ι₀ : G →* LinearMap.GeneralLinearGroup K (Fin n → K)), Function.Injective ι₀ →
      (∀ g, ι₀ g ∈ commutingUnitary (idForm h n) τ₀) → PSUHas27Sub G → False :=
    fun ι₀ hι₀ hmem h27 => psu_graph_has27_false h A φ hφ hD ι₀ hι₀ hmem h27
  have hnopair : ∀ {G : Type} [Group G]
      (ι₀ : G →* LinearMap.GeneralLinearGroup K (Fin n → K)), Function.Injective ι₀ →
      (∀ g, ι₀ g ∈ commutingUnitary (idForm h n) τ₀) → PSUHasPair360 G → False :=
    fun ι₀ hι₀ hmem hp => psu_graph_pair_false h A φ hφ hD ι₀ hι₀ hmem hp
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hnV (idForm_isSymm h n) (idForm_separatingLeft h n) τ₀ hτ₀ hτ₀B c hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 3 ^ f := h.card_fixedField
  have hfinn : finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = n := hfinW.trans hfin
  have hι₀inj : Function.Injective
      ((commutingUnitary (idForm h n) τ₀).subtype) := Subgroup.subtype_injective _
  rcases hμ1 with hμ1 | hμ1
  ·
    obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h (by norm_num) h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    let Φ' := Φ.trans (MulEquiv.subgroupCongr
      (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    have hnum : 5 ≤ n ∨ (n = 3 ∧ 3 ≤ f) ∨ (n = 4 ∧ 3 ≤ f) ∨ (n = 4 ∧ f = 2) := by omega
    rcases hnum with h5 | ⟨h3, hf3⟩ | ⟨h4, hf3⟩ | ⟨h4, hf2⟩
    · exact hno27 _ hι₀inj (fun g => g.2) ((psu_orth_has27 hO hfpos hkc _ hQ
        (Or.inl (by omega))).of_mulEquiv Φ'.symm)
    · exact hno27 _ hι₀inj (fun g => g.2) ((psu_orth_has27 hO hfpos hkc _ hQ
        (Or.inr (Or.inl ⟨by omega, hf3⟩))).of_mulEquiv Φ'.symm)
    · exact hno27 _ hι₀inj (fun g => g.2) ((psu_orth_has27 hO hfpos hkc _ hQ
        (Or.inr (Or.inr (Or.inl ⟨by omega, hf3⟩)))).of_mulEquiv Φ'.symm)
    · by_cases hS : ∃ S : Submodule h.fixedField (conjFixed h ((b : K) • τ₀)),
          finrank h.fixedField S = 2 ∧ ∀ x ∈ S,
            CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
      · refine hnopair _ hι₀inj (fun g => g.2) ((psu_orth_hasPair hO ?_ _ hQ (by omega)
          hS).of_mulEquiv Φ'.symm)
        rw [hkc, hf2]
      · exact hno27 _ hι₀inj (fun g => g.2) ((psu_orth_has27 hO hfpos hkc _ hQ
          (Or.inr (Or.inr (Or.inr ⟨by omega, hf2, hS⟩)))).of_mulEquiv Φ'.symm)
  ·
    obtain ⟨B', -, halt, hnd, hEven, Φ, -⟩ := hB2 hμ1
    have hn4 : 4 ≤ finrank h.fixedField (conjFixed h ((b : K) • τ₀)) := by
      obtain ⟨r, hr⟩ := hEven
      omega
    exact hno27 _ hι₀inj (fun g => g.2) ((psu_symp_has27 hO hfpos hkc B' halt hnd hn4).of_mulEquiv
      Φ.symm)

end CFSG.ComponentClassification.CatFC
