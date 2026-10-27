module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.OddBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallU3Bar

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)
open CFSG.ComponentClassification.CatLeafProof.OddInner

theorem psu_graph_card_fixed_le {K : Type} [Field K] (h : UnitaryFieldData 3 2 K)
    (A : primeFormUnitary h (idGram K 3)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    Nat.card ↥(fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) ≤ 720 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  let τ₀ : (Fin 3 → K) →ₛₗ[h.bar] (Fin 3 → K) :=
    semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let Cτ : Subgroup (LinearMap.GeneralLinearGroup K (Fin 3 → K)) :=
    commutingUnitary (idForm h 3) τ₀
  let Csu : Subgroup ↥Cτ := (sesqSpecialUnitaryGroup (idForm h 3)).subgroupOf Cτ
  set σ : MulAut (primeFormP h (idGram K 3)) :=
    primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩ with hσdef
  have hk : Nat.card h.fixedField = 9 := by
    rw [h.card_fixedField]; norm_num
  have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h (by norm_num) h1
  have hroots : Nat.card (rootsOfUnity 2 h.fixedField) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : rootsOfUnity 2 h.fixedField)]
    refine ⟨traceZeroNegSign h.fixedField, ?_, fun y hy => ?_⟩
    · intro hh
      have h2 := congrArg (fun x : rootsOfUnity 2 h.fixedField => (x : h.fixedFieldˣ)) hh
      have h1 : (-1 : h.fixedField) = 1 :=
        congrArg Units.val (by simpa [traceZeroNegSign] using h2)
      have h20 : (2 : h.fixedField) = 0 := by
        rw [show (2 : h.fixedField) = 1 - (-1) from by ring, h1]; ring
      exact h2k h20
    · rcases traceZeroSign_eq_one_or_neg y with hy1 | hy2
      · exact absurd hy1 hy
      · exact hy2
  have hpgl : Nat.card (Matrix.ProjGenLinGroup (Fin 2) h.fixedField) = 720 := by
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hk]; norm_num
  obtain ⟨e1⟩ := psu_graph_three_two_equiv h A φ hφ hA
  have hcardCτ : Nat.card ↥Cτ = 1440 := by
    calc Nat.card ↥Cτ =
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm h.fixedField)) :=
          (Nat.card_congr e1.toEquiv).symm
      _ = Nat.card (Matrix.ProjGenLinGroup (Fin 2) h.fixedField × rootsOfUnity 2 h.fixedField) :=
          (Nat.card_congr (traceZeroProjectiveEquiv (K := h.fixedField) h2k).toEquiv).symm
      _ = Nat.card (Matrix.ProjGenLinGroup (Fin 2) h.fixedField) *
            Nat.card (rootsOfUnity 2 h.fixedField) := Nat.card_prod _ _
      _ = 1440 := by rw [hpgl, hroots]
  have hC3 : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  let ψ : ↥(gramSU h (idGram K 3)) ≃* ↥(gramSU h (idGram K 3)) :=
    primeFormConjSU h (idGram K 3) A * primeFormFieldSU h hC3 φ
  have hlift : ∀ x : ↥(fixedSubgroup σ), ∃ g : ↥(gramSU h (idGram K 3)),
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) ∈ sesqSpecialUnitaryGroup (idForm h 3) ∧
      (∀ v, ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) (τ₀ v) =
        τ₀ (((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v)) ∧
      (QuotientGroup.mk g : primeFormP h (idGram K 3)) =
        (x : primeFormP h (idGram K 3)) := by
    intro x
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (x : primeFormP h (idGram K 3))
    have hσmk : σ (QuotientGroup.mk g₀ : primeFormP h (idGram K 3)) = QuotientGroup.mk g₀ := by
      rw [hg₀]; exact x.2
    have hσmk' : (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)
        (QuotientGroup.mk g₀ : primeFormP h (idGram K 3)) = QuotientGroup.mk g₀ := by
      rw [← hσdef]; exact hσmk
    have hmk : (QuotientGroup.mk (ψ g₀) : primeFormP h (idGram K 3)) =
        QuotientGroup.mk g₀ := (psu_graph_hψ h A φ g₀).symm.trans hσmk'
    have hker : (QuotientGroup.mk ((ψ g₀)⁻¹ * g₀) : primeFormP h (idGram K 3)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, inv_mul_cancel]
    have hψg : ψ g₀ = g₀ := by
      have h1 : (ψ g₀)⁻¹ * g₀ = 1 := psu_ker_three_two h _ hker
      have h2 : g₀ = ψ g₀ := by
        have h3 := congrArg (fun z => ψ g₀ * z) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    have hψg' : (primeFormConjSU h (idGram K 3) A)
        ((primeFormFieldSU h hC3 φ) g₀) = g₀ := hψg
    have hval : (A : GL (Fin 3) K) * glAut φ (g₀ : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
        (g₀ : GL (Fin 3) K) := by
      have h1 := congrArg Subtype.val hψg'
      change (A : GL (Fin 3) K) * glAut φ (g₀ : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
        (g₀ : GL (Fin 3) K) at h1
      exact h1
    have h2 : (A : GL (Fin 3) K) * glAut φ (g₀ : GL (Fin 3) K) =
        (g₀ : GL (Fin 3) K) * A := by
      rw [mul_inv_eq_iff_eq_mul] at hval
      exact hval
    have hmat : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar) =
        ((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have h3 := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h2
      rw [Units.val_mul, Units.val_mul, coe_glAut] at h3
      rw [show (((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ) =
          (((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar) from
        Matrix.ext (fun i j => hφ _)] at h3
      exact h3
    have hcomm : ∀ v, ((Matrix.GeneralLinearGroup.toLin (g₀ : GL (Fin 3) K) :
        LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) (τ₀ v) =
        τ₀ (((Matrix.GeneralLinearGroup.toLin (g₀ : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v) := by
      have hmat' := (commute_semilinearMatrixMap_iff h
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ((g₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).mpr hmat.symm
      intro v
      simpa only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] using hmat' v
    exact ⟨g₀, (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K 3) (g₀ : GL (Fin 3) K)).mpr
      g₀.2, hcomm, hg₀⟩
  let gOf : ↥(fixedSubgroup σ) → ↥(gramSU h (idGram K 3)) := fun x => Classical.choose (hlift x)
  have gOf_spec : ∀ x, Matrix.GeneralLinearGroup.toLin (gOf x : GL (Fin 3) K) ∈
        sesqSpecialUnitaryGroup (idForm h 3) ∧
      (∀ v, ((Matrix.GeneralLinearGroup.toLin (gOf x : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) (τ₀ v) =
        τ₀ (((Matrix.GeneralLinearGroup.toLin (gOf x : GL (Fin 3) K) :
          LinearMap.GeneralLinearGroup K (Fin 3 → K)) : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v)) ∧
      (QuotientGroup.mk (gOf x) : primeFormP h (idGram K 3)) =
        (x : primeFormP h (idGram K 3)) := fun x => Classical.choose_spec (hlift x)
  let f : ↥(fixedSubgroup σ) → ↥Csu := fun x =>
    ⟨⟨Matrix.GeneralLinearGroup.toLin (gOf x : GL (Fin 3) K),
        mem_commutingUnitary.mpr ⟨(mem_sesqSpecialUnitaryGroup.mp (gOf_spec x).1).1,
          (gOf_spec x).2.1⟩⟩,
      Subgroup.mem_subgroupOf.mpr (gOf_spec x).1⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : ((f x : ↥Csu) : ↥Cτ) = ((f y : ↥Csu) : ↥Cτ) := congrArg Subtype.val hxy
    have h2 : Matrix.GeneralLinearGroup.toLin (gOf x : GL (Fin 3) K) =
        Matrix.GeneralLinearGroup.toLin (gOf y : GL (Fin 3) K) := congrArg Subtype.val h1
    have h3 : (gOf x : GL (Fin 3) K) = (gOf y : GL (Fin 3) K) :=
      Matrix.GeneralLinearGroup.toLin.injective h2
    have h4 : gOf x = gOf y := Subtype.ext h3
    apply Subtype.ext
    calc (x : primeFormP h (idGram K 3)) =
          (QuotientGroup.mk (gOf x) : primeFormP h (idGram K 3)) := (gOf_spec x).2.2.symm
      _ = (QuotientGroup.mk (gOf y) : primeFormP h (idGram K 3)) := by rw [h4]
      _ = (y : primeFormP h (idGram K 3)) := (gOf_spec y).2.2
  have hF_le : Nat.card ↥(fixedSubgroup σ) ≤ Nat.card ↥Csu :=
    Nat.card_le_card_of_injective f hf_inj
  have hneg : LinearMap.det (((-1 : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
      (Fin 3 → K) →ₗ[K] (Fin 3 → K))) = -1 := by
    have hodd : Odd 3 := ⟨1, by norm_num⟩
    have e : (((-1 : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        (Fin 3 → K) →ₗ[K] (Fin 3 → K))) =
        (-1 : K) • (1 : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) := by
      refine LinearMap.ext fun v => ?_
      simp
    rw [e, LinearMap.det_smul, map_one, mul_one, Module.finrank_fin_fun, hodd.neg_one_pow]
  have hzmem : (⟨(-1 : LinearMap.GeneralLinearGroup K (Fin 3 → K)),
      psu_negOne_mem h τ₀⟩ : ↥Cτ) ∉ Csu := by
    intro hz
    have hSU := Subgroup.mem_subgroupOf.mp hz
    have hdet := (mem_sesqSpecialUnitaryGroup.mp hSU).2
    have hneg1 : (-1 : K) = 1 := by
      have hd : LinearMap.det (((-1 : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          (Fin 3 → K) →ₗ[K] (Fin 3 → K))) = 1 := by
        simpa using hdet
      rw [hneg] at hd
      exact hd
    have h20 : (2 : K) = 0 := by
      rw [show (2 : K) = 1 - (-1) from by ring, hneg1]; ring
    exact two_ne_zero_of_odd h (by norm_num) h20
  have hidx : 2 ≤ Csu.index := by
    have h1 : Csu.index ≠ 1 := fun h1 =>
      hzmem (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top _)
    have h2 : Csu.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hCsu_le : Nat.card ↥Csu ≤ 720 := by
    have hmul := Subgroup.card_mul_index Csu
    have hstep : Nat.card ↥Csu * 2 ≤ Nat.card ↥Csu * Csu.index :=
      mul_le_mul_right hidx (Nat.card ↥Csu)
    rw [hmul, hcardCτ] at hstep
    omega
  calc Nat.card ↥(fixedSubgroup σ) ≤ Nat.card ↥Csu := hF_le
    _ ≤ 720 := hCsu_le

theorem harrisOddSharp_PSU_three_two (hO : LieOrderFormulasInput) : HarrisOddSharp .PSU 3 2 := by
  apply harrisOddSharp_of_concrete
  intro S _ _ hm
  have hadm : StatedLieAdmissible .PSU 3 3 2 :=
    ⟨Nat.prime_three, by norm_num, by norm_num, by decide⟩
  obtain ⟨K, _, h, ⟨ψ⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  haveI : Finite K := h.finite
  refine ⟨primeFormP h (idGram K 3), inferInstance, inferInstance, ψ, ?_⟩
  intro σ hσ D hD
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
    have hAσ : σ = primeFormConjHom h (idGram K 3) A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    subst hAσ
    exact psu_inner_three_two_false hO h A hσ hD
  · subst hAφ
    have hle := psu_graph_card_fixed_le h A φ hφ hσ
    exact ⟨Nat.ne_of_lt (lt_of_le_of_lt hle (by norm_num)),
      fun _ => Nat.ne_of_lt (lt_of_le_of_lt hle (by norm_num))⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
