module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft
  toLin_mem_sesqUnitaryGroup_iff)

@[expose] def LFiveSevenU47GraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] (f : ℕ) (h : UnitaryFieldData 7 f K), n = 4 → f = 1 →
    ∀ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      (∀ x, φ x = h.bar x) → orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 →
        ¬ SevenL3Group (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))

section Graph


theorem SevenList.seven_commutingUnitary {f : ℕ} {E V : Type}
    [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : UnitaryFieldData 7 f E) (hn : 3 ≤ Module.finrank E V)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) {L : Subgroup (commutingUnitary B τ₀)}
    (hL : IsComponent L) (hLm : LieModel (L ⧸ center L) .PSL 3 2 1) :
    f = 1 ∧ (Module.finrank E V = 3 ∨ Module.finrank E V = 4) := by
  have hp2 : (7 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd 7 := by decide
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = 7 ^ f := h.card_fixedField
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp2 h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    let Ψ := Φ.trans (MulEquiv.subgroupCongr
      (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    have hL' := LocalCores.isComponent_map_mulEquiv Ψ hL
    have hL'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hLm
    obtain ⟨hf1, hd⟩ := sevenOrthComponentInput_holds h.fixedField
      (conjFixed h ((b : E) • τ₀)) f h.one_le hkc _ hQ (by rw [hfinW]; exact hn) _ hL' hL'm
    rw [hfinW] at hd
    exact ⟨hf1, hd⟩
  · exfalso
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B' halt hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B' halt hnd hdm
    let Ψ := Φ.trans eS
    have hL' := LocalCores.isComponent_map_mulEquiv Ψ hL
    have hL'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
      (L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hLm
    obtain ⟨hadmS, hmodS⟩ :=
      RankOne.FiveList.lieModel_of_isComponent_statedSp h.prime hp2 h.one_le hkc (by omega) hL'
    obtain ⟨h1, -, -⟩ := eq_seven_of_lieModel_PSL_three_two hL'm hp2 hadmS hmodS
    exact absurd h1 (by decide)

theorem lFiveSevenPSUGraphInput_of_U47 (h47 : LFiveSevenU47GraphInput) :
    LFiveSevenPSUGraphInput := by
  intro n K _ f h hadm A φ hφ hA hF
  obtain ⟨L, hL, hLm⟩ := hF.1
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact (7 : ℕ).Prime := ⟨h.prime⟩
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
  obtain ⟨M, hM, ⟨eLM⟩⟩ := CatLeafProof.exists_component_of_quotientFixed _ hZc ψ hinv hL'
  set τ₀ := semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hτ₀def
  have hτ₀ : Function.Bijective τ₀ :=
    CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, τ₀ (τ₀ v) = (c : K) • v := CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
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
      exact (CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mpr ((hfixg g).mp hg) v
    · intro hy
      obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
      set g := Matrix.GeneralLinearGroup.toLin.symm y with hgdef
      have hgy : Matrix.GeneralLinearGroup.toLin g = y := MulEquiv.apply_symm_apply _ _
      have hg : g ∈ gramSU h (idGram K n) := by
        rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, hgy]
        exact hyS
      refine ⟨⟨g, hg⟩, (hfixg _).mpr
        ((CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h _ _).mp
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
  have hdim : 3 ≤ Module.finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    exact hn
  have hL'm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective eF.toMonoidHom eF.injective) hLm
  have hMm : LieModel (M ⧸ center M) .PSL 3 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eLM hL'm
  let eMN := ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
      ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective φS hφS)).trans
    (Subgroup.subgroupOfEquivOfLe h2.1).symm
  have hNm := RankOne.FiveList.lieModel_centerQuotient_of_mulEquiv eMN hMm
  obtain ⟨hf1, hn34⟩ := SevenList.seven_commutingUnitary h hdim (idForm_isSymm h n)
    (idForm_separatingLeft h n) τ₀ hτ₀ hτ₀B c hμ h3 hNm
  rw [Module.finrank_fin_fun] at hn34
  rcases hn34 with h3' | h4'
  · exact ⟨h3', hf1⟩
  · exact (h47 n K f h h4' hf1 A φ hφ hA hF).elim

end Graph

end CFSG.SeitzReduction.LinearPilot
