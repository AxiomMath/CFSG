module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup det_eq_one_of_mem eq_one_of_mem_of_scalar)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section OddModel

@[expose] noncomputable def isoOneToSL {k : Type} [Field k] [CharP k 2] (N : ℕ) :
    matrixIsometryGroup (1 : Matrix (Fin N) (Fin N) k) →* SpecialLinearGroup (Fin N) k where
  toFun g := ⟨((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k),
    det_eq_one_of_mem (by rw [det_one]; exact one_ne_zero) g.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

variable {f N : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin N) K'}

theorem isoOne_mem (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1)
    (g : matrixIsometryGroup (1 : Matrix (Fin N) (Fin N) h.fixedField)) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map h.fixedField.subtype (isoOneToSL N g)) ∈
      gramSU h (C₀ : Matrix (Fin N) (Fin N) K') := by
  have h1 := F4Pilot.toGL_map_mem_gramSU h (C := (1 : Matrix (Fin N) (Fin N) h.fixedField))
    (g := isoOneToSL N g) g.2
  rwa [Matrix.map_one _ (map_zero _) (map_one _), ← hC₀] at h1

@[expose] noncomputable def isoOneToSU (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1) :
    matrixIsometryGroup (1 : Matrix (Fin N) (Fin N) h.fixedField) →*
      gramSU h (C₀ : Matrix (Fin N) (Fin N) K') :=
  (SpecialLinearGroup.toGL.comp ((SpecialLinearGroup.map h.fixedField.subtype).comp
    (isoOneToSL N))).codRestrict _ (isoOne_mem h hC₀)

variable {h}

theorem coe_isoOneToSU (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1)
    (g : matrixIsometryGroup (1 : Matrix (Fin N) (Fin N) h.fixedField)) :
    (((isoOneToSU h hC₀ g : gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) : GL (Fin N) K') :
        Matrix (Fin N) (Fin N) K') =
      ((g : GL (Fin N) h.fixedField) : Matrix (Fin N) (Fin N) h.fixedField).map
        h.fixedField.subtype :=
  rfl

theorem proj_isoOneToSU_injective (hN : 1 ≤ N) (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1) :
    Function.Injective ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) N)).comp (isoOneToSU h hC₀)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  obtain ⟨c, -, -, hc⟩ := hg
  have hmat := congrArg (fun x : GL (Fin N) K' => (x : Matrix (Fin N) (Fin N) K')) hc
  simp only [coe_isoOneToSU, GeneralLinearGroup.coe_scalar] at hmat
  set i₀ : Fin N := ⟨0, hN⟩
  have hscal : ((g : GL (Fin N) h.fixedField) : Matrix (Fin N) (Fin N) h.fixedField) =
      Matrix.scalar (Fin N) (((g : GL (Fin N) h.fixedField) :
        Matrix (Fin N) (Fin N) h.fixedField) i₀ i₀) := by
    ext i j
    have hij := congrFun (congrFun hmat i) j
    have h00 := congrFun (congrFun hmat i₀) i₀
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ite_true] at hij h00
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hij' : i = j
    · subst hij'
      rw [ite_eq_left rfl] at hij ⊢
      exact hij.trans h00.symm
    · rw [ite_eq_right hij'] at hij ⊢
      exact hij
  have h1 := eq_one_of_mem_of_scalar (C := (1 : Matrix (Fin N) (Fin N) h.fixedField))
    one_ne_zero g.2 hscal
  exact Subtype.ext h1

theorem fieldBar_proj_isoOneToSU (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1)
    (g : matrixIsometryGroup (1 : Matrix (Fin N) (Fin N) h.fixedField)) :
    primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)
        ((isoOneToSU h hC₀ g : gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) :
          primeFormP h (C₀ : Matrix (Fin N) (Fin N) K')) =
      ((isoOneToSU h hC₀ g : gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) :
        primeFormP h (C₀ : Matrix (Fin N) (Fin N) K')) := by
  change primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h) _ = _
  rw [primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU, coe_isoOneToSU]
  ext i j
  simp only [Matrix.map_apply, UnitaryPilot.barRingEquiv_apply]
  exact (((g : GL (Fin N) h.fixedField) : Matrix (Fin N) (Fin N) h.fixedField) i j).2

theorem range_proj_isoOneToSU (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ 2 ^ f = 2)) (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1) :
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) N)).comp
      (isoOneToSU h hC₀)).range =
        fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
  have : Finite K' := h.finite
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have hle : ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) N)).comp (isoOneToSU h hC₀)).range ≤
        fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
    rintro _ ⟨g, rfl⟩
    exact fieldBar_proj_isoOneToSU hC hC₀ g
  obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h (by omega) hq hC
    (Or.inl hC₀) _ (fun x => UnitaryPilot.barRingEquiv_apply h x)
  have hCl1 : (Cl : Matrix (Fin N) (Fin N) h.fixedField) = 1 := by
    apply
      CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.map_subtype_injective h
    beta_reduce
    rw [hCl, hC₀, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr Φ.toEquiv, hCl1,
    ← Nat.card_congr (MonoidHom.ofInjective (proj_isoOneToSU_injective (by omega) hC₀)).toEquiv]

end OddModel

theorem nonempty_statedSp_mulEquiv_isometryOne (k : Type) [Field k] [CharP k 2] (m : ℕ) :
    Nonempty (StatedSp m k ≃* matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1))
      (Fin (2 * m + 1)) k)) := by
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_isAlt (k := k) (n := 2 * m + 1))
    (CFSG.ComponentClassification.OutcomeLocal.dotForm_restrict_nondegenerate (r := m) rfl)
    (CFSG.ComponentClassification.OutcomeLocal.finrank_dotForm_ker (r := m) rfl)
  exact ⟨((CFSG.ComponentClassification.OutcomeLocal.oneRestrictEquiv (k := k)
    (n := 2 * m + 1) (r := m) rfl).trans e₁).symm⟩

section Closed

variable {f N : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') {C₀ : GL (Fin N) K'}

@[expose] def gramSUOneEquiv (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1) :
    gramSU h (C₀ : Matrix (Fin N) (Fin N) K') ≃* StatedSU N (2 ^ f) K' :=
  MulEquiv.subgroupCongr (by rw [hC₀, ← unitarySU_eq_gramSU h N])

theorem isPerfect_gramSU_one (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1) (hN : 3 ≤ N)
    (hq : (N, 2 ^ f) ≠ (3, 2)) : Group.IsPerfect (gramSU h (C₀ : Matrix (Fin N) (Fin N) K')) := by
  have : Finite K' := h.finite
  have := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) (K := K')
    (by rw [h.card, ← pow_mul, mul_comm]) hN hq
  exact Group.IsPerfect.ofSurjective (f := (gramSUOneEquiv h hC₀).symm.toMonoidHom)
    (gramSUOneEquiv h hC₀).symm.surjective

theorem gramSU_one_exists_section_of_central (hC₀ : (C₀ : Matrix (Fin N) (Fin N) K') = 1)
    (hN : 3 ≤ N) (ho : ¬ Even N) (hf : 2 ≤ f) :
    ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h (C₀ : Matrix (Fin N) (Fin N) K')),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : gramSU h (C₀ : Matrix (Fin N) (Fin N) K') →* E', ∀ g, π' (s g) = g := by
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  exact F4Pilot.forall_exists_section_of_mulEquiv (gramSUOneEquiv h hC₀)
    (F4Pilot.statedSU_odd_split (by rw [h.card, ← pow_mul, mul_comm]) (by omega) hN ho
      (four_le_two_pow hf))

end Closed

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀] {m f : ℕ}
  {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * m + 1)) K'}

structure UnitaryOddNeighbourParam (e : L ≃* StatedSp (m + 1) K₀) (t : G) (k : Fin (m + 1))
    (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1)
    (β : StatedSp m h.fixedField ≃*
      matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField))
    (ι : K₀ ≃+* h.fixedField) where
  Φ : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') →* G
  range_eq : Φ.range = neighbourCore e k
  ker_le : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K'))
  N1 : ∀ x : StatedSp m K₀,
    Φ (isoOneToSU h hC₀ (β (statedSpMap (ι : K₀ →+* h.fixedField) m x))) =
      ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) : L) : G)
  N3 : ∀ x : gramSU h (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K'),
    t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x)

end Param

section Construct

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₀ : Type} [Field K₀]

theorem nonempty_unitaryOddNeighbourParam {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K₀)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (hk : RootKindSp e t f k .unitaryOdd) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m + 1)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1),
      ∀ β : StatedSp m h.fixedField ≃*
          matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField),
        ∃ ι : K₀ ≃+* h.fixedField, Nonempty (UnitaryOddNeighbourParam h e t k hC hC₀ β ι) := by
  have : Finite K₀ := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K₀ 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, -, hρt⟩ :=
    exists_surjective_primeFormP_neighbourCore_unitary' hset hKc hf (by omega : 2 ≤ m) e htC ht
      k rfl rfl (Or.inr rfl) hk hN
  obtain ⟨-, rfl, h1⟩ : Sp2mKind.unitaryOdd = .unitaryOdd ∧ r = 2 * m + 1 ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = 1 := by
    rcases hcase with ⟨h2, -⟩ | h1
    · exact absurd h2 (by decide)
    · exact h1
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * m + 1 = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  refine ⟨K', inferInstance, h', hk2, C₀, hC, h1, fun β => ?_⟩
  have hμ : Function.Injective ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) (2 * m + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)) :=
    (proj_isoOneToSU_injective (by omega) h1).comp β.injective
  have hμr : ((QuotientGroup.mk' (normOneScalars h'
      (gramSU h' (C₀ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K')) (2 * m + 1))).comp
        ((isoOneToSU h' h1).comp β.toMonoidHom)).range =
      fixedSubgroup (primeFormFieldHom h' hC (UnitaryPilot.barRingEquiv h')) := by
    rw [← MonoidHom.comp_assoc, MonoidHom.range_comp, MonoidHom.range_eq_top.2 β.surjective,
      ← MonoidHom.range_eq_map]
    exact range_proj_isoOneToSU (by omega) hq hC h1
  obtain ⟨ι, Φ, hrange, hker, hN1, hN3⟩ := exists_param_of_proj e hKc hf hm htC k h' hC
    (gramSU_one_exists_section_of_central h' h1 (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m) hf)
    (isPerfect_gramSU_one h' h1 (by omega) (fun h3 => by
      have := (Prod.mk.inj h3).1
      omega))
    ((isoOneToSU h' h1).comp β.toMonoidHom) hμ hμr hN ρ' hρs hρker hρt
  exact ⟨ι, ⟨{ Φ := Φ, range_eq := hrange, ker_le := hker, N1 := hN1, N3 := hN3 }⟩⟩

end Construct

end CFSG.SeitzReduction.SymplecticPilot
