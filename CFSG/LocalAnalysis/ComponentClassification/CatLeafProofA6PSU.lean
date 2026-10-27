module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6PSUInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

theorem a6_graph_psu_fixedSU
    {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) (c : Kˣ)
    (hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (c : K) • 1) :
    A6CentreForm (fixedSubgroup (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h isPrimeFormGram_one φ)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  set ψ : MulAut (gramSU h (idGram K n)) :=
    primeFormConjSU h (idGram K n) A * primeFormFieldSU h isPrimeFormGram_one φ with hψdef
  intro M hM
  show A6Safe M
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ := OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := OddInner.semilinearMatrixMap_sq_of h hAc
  let φS : gramSU h (idGram K n) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
        (gramSU h (idGram K n)).subtype
  have hφS : Function.Injective φS := fun x y hxy =>
    Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hxy)
  have hfixg : ∀ g : gramSU h (idGram K n), g ∈ fixedSubgroup ψ ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := by
    intro g
    change ψ g = g ↔ _
    rw [Subtype.ext_iff]
    change (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g ↔ _
    rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut]
    have hmap : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := Matrix.ext fun i j => hφ _
    rw [hmap]
    exact eq_comm
  have htoLin : ∀ (g : GL (Fin n) K) (v : Fin n → K),
      ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) v = (g : Matrix (Fin n) (Fin n) K) *ᵥ v := fun g v => by
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  have hmap : (fixedSubgroup ψ).map φS =
      commutingUnitary (idForm h n) τ₀ ⊓ sesqSpecialUnitaryGroup (idForm h n) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hS : φS g ∈ sesqSpecialUnitaryGroup (idForm h n) :=
        (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) g).mpr g.2
      refine Subgroup.mem_inf.mpr ⟨⟨sesqSpecialUnitaryGroup_le _ hS, fun v => ?_⟩, hS⟩
      change ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K))
            (τ₀ v) = τ₀ (((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) K) :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) v)
      rw [htoLin, htoLin]
      exact (OddInner.commute_semilinearMatrixMap_iff h _ _).mpr ((hfixg g).mp hg) v
    · intro hy
      obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
      set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K n) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hyS
      refine ⟨⟨g, hg⟩, (hfixg _).mpr ((OddInner.commute_semilinearMatrixMap_iff h _ _).mp
        fun v => ?_), hgy⟩
      have h1 := hyC.2 v
      rw [← hgy, htoLin, htoLin] at h1
      exact h1
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hMF φS hφS
  rw [hmap] at h1
  have hnormal : ((commutingUnitary (idForm h n) τ₀ ⊓
      sesqSpecialUnitaryGroup (idForm h n)).subgroupOf (commutingUnitary (idForm h n) τ₀)).Normal
      := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    rw [sesqSpecialUnitaryGroup] at hxS ⊢
    obtain ⟨hxU, hxD⟩ := Subgroup.mem_inf.mp hxS
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        mul_mem (mul_mem g.2.1 hxU) (inv_mem g.2.1)
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (MonoidHom.normal_ker _).conj_mem _ hxD (g : LinearMap.GeneralLinearGroup K (Fin n → K))
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  have hdim : 1 ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hO' := a6_commutingUnitary h hp2 hdim (idForm_isSymm h n)
    (idForm_separatingLeft h n) τ₀ hτ₀ hτ₀B c hμ _ h3
  exact
    a6Safe_of_mulEquiv
      ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
        ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective φS hφS))
      (a6Safe_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2.1).symm hO')

theorem a6_graph_psu
    {n : ℕ} {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (A : primeFormUnitary h (idGram K n))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    A6CentreForm (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) := by
  intro L hL
  show A6Safe L
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hx2 : primeFormPsi h hC (⟨A, φ⟩ * ⟨A, φ⟩) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hx2
  have hmapA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := Matrix.ext fun i j => hφ _
  have hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = (c : K) • 1 := by
    have h1 : (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmapA] at h2
    rw [h2, Matrix.smul_one_eq_diagonal]
    rfl
  set ψ : MulAut (gramSU h (idGram K n)) :=
    primeFormConjSU h (idGram K n) A * primeFormFieldSU h hC φ with hψdef
  have hinv : (normOneScalars h (gramSU h (idGram K n)) n).map ψ.toMonoidHom =
      normOneScalars h (gramSU h (idGram K n)) n := by
    have e1 : ψ.toMonoidHom = (primeFormConjSU h (idGram K n) A).toMonoidHom.comp
        (primeFormFieldSU h hC φ).toMonoidHom := rfl
    rw [e1, ← Subgroup.map_map, map_normOneScalars_field, map_normOneScalars_conj]
  have hZc : normOneScalars h (gramSU h (idGram K n)) n ≤ center (gramSU h (idGram K n)) := by
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  have heq : primeFormPsi h hC ⟨A, φ⟩ = CatalogueBFixedCentralQuotient.onQuotient
      (normOneScalars h (gramSU h (idGram K n)) n) ψ hinv := by
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : primeFormP h (idGram K n))) =
          QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk, primeFormPsi_apply, MulAut.mul_apply]
      change primeFormConjAut h _ A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
      rw [primeFormFieldAut_mk, primeFormConjAut_mk]
      rfl
  let eF := MulEquiv.subgroupCongr (congrArg fixedSubgroup heq)
  have hL' := LocalCores.isComponent_map_mulEquiv eF hL
  obtain ⟨M, hM, σ, hσ, hker⟩ := exists_component_cover_of_quotientFixed _ hZc ψ hinv hL'
  exact a6Safe_of_mulEquiv (L.equivMapOfInjective eF.toMonoidHom eF.injective)
    (a6Safe_of_cover hM.1 σ hσ hker (a6_graph_psu_fixedSU h hp2 hn A φ hφ c hAc M hM))


theorem oddLieA6CentreFor_PSU
    : OddLieA6CentreFor .PSU := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  refine a6CentreForm_of_mulEquiv (fixedSubgroupCongrEquiv ψ α) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact a6CentreForm_of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (a6_inner_psu h hp2 hadm A hord)
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact a6CentreForm_of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (a6_graph_psu h hp2 hadm A φ hφ hord)

end CFSG.ComponentClassification.CatLeafProof
