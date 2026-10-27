module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusNormal
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K]

theorem isCharacteristicP_fixedSubgroup_fieldBar_one (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) (hev : Even n) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    IsCharacteristicP 2 (fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  obtain ⟨hcent, -, hinjU, hNinn, hNC, -, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC (Or.inl Units.val_one) 1 hCl σ hσ
  have hcj := UnbalancingLocal.EvenUnitaryComponents.conj_injective_primeFormP h hC hn
  have heq : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h hC σ} =
        ((primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    refine le_antisymm ?_ (le_inf hNinn hNC)
    rintro x ⟨hxI, hxC⟩
    obtain ⟨g, φ, rfl⟩ := (hcent x).mp hxC
    have h1 := primeFormFieldFactor_psi h hC hn hq ⟨fixedIsometryHom h hCl g, φ⟩
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxI
    have h2 := primeFormFieldFactor_apply h hC hn hq ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one, ← hs, h1] at h2
    change φ = 1 at h2
    subst h2
    refine ⟨g, ?_⟩
    rw [primeFormPsi_apply, map_one, mul_one]
    rfl
  let Φ : fixedSubgroup (primeFormFieldHom h hC σ) ≃*
      matrixIsometryGroup ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) :=
    (CatLeafProof.fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr heq).trans
      (MonoidHom.ofInjective hinjU).symm)
  have hch := CatLeafProof.isCharacteristicP_matrixIsometryGroup_one (k := h.fixedField) hev hn
  rw [← Units.val_one] at hch
  exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Φ.symm hch

section Descent

variable (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def centerQuotientEquivPrimeFormP (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⧸
        center (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.quotientMulEquivOfEq (center_gramSU_eq_normOneScalars h isPrimeFormGram_one hn hq)

theorem congr_centerQuotientAut_primeFormP_mk (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (β : MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    MulAut.congr (centerQuotientEquivPrimeFormP h hn hq) (centerQuotientAut β)
        (y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      ((β y : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rw [MulAut.congr_apply]
  have e1 : (centerQuotientEquivPrimeFormP h hn hq).symm
      (y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        QuotientGroup.mk' _ y := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e1, centerQuotientAut_mk]
  rfl


theorem exists_unitary_normal_form (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (β : MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉ (MulAut.conj : _ ⧸ center (gramSU h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) →* MulAut _).range)
    {f' : ℕ} (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ (H C₀ : GL (Fin n) K) (hC₀ : IsPrimeFormGram C₀)
      (hH : ((H : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * H = C₀),
      (((C₀ : Matrix (Fin n) (Fin n) K) = 1 ∧ ¬ Even n) ∨
        ∃ r, n = 2 * r ∧ (C₀ : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) ∧
      ∀ g, β (gramTransportSU h hH g) =
        gramTransportSU h hH (primeFormFieldSU h hC₀ h.barEquiv g) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set E := centerQuotientEquivPrimeFormP h hn hq
  set α := MulAut.congr E (centerQuotientAut β) with hαdef
  have hαmk := congr_centerQuotientAut_primeFormP_mk h hn hq β
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hβ2, map_one]
  have hαo : α ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [hαdef, FixedFourGroup.congr_mem_inner_iff]
    exact hβo
  have hα1 : α ≠ 1 := fun h1 => hαo (h1 ▸ one_mem _)
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hαfix : LieModel (fixedSubgroup α) .PSp 3 2 f' :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv E _) hfix
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq α hαord
  have hbar : ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x := by
    rcases hcases with hid | hbar
    · exfalso
      apply hαo
      refine hDinner _ ?_ hαord
      rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
      exact hid
    · exact hbar
  have hφ : primeFormFieldFactor h hC hn hq α = h.barEquiv := RingEquiv.ext hbar
  obtain ⟨-, H, C₀, hC₀, hcase₀, -, -, hHC, -, ⟨θ, hθ, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq α hαord hbar
  rw [hφ] at hθα
  have hc : MulAut.congr θ (primeFormFieldHom h hC₀ h.barEquiv) = α :=
    MulEquiv.ext fun x => (hθα x).symm
  refine ⟨H, C₀, hC₀, hHC, ?_, ?_⟩
  · rcases hcase₀ with h1 | h2
    · refine Or.inl ⟨h1, fun hev => ?_⟩
      have hC1 : C₀ = 1 := Units.ext h1
      subst hC1
      have hch := isCharacteristicP_fixedSubgroup_fieldBar_one h hn hq hev h.barEquiv
        (fun _ => rfl)
      have e1 : fixedSubgroup (primeFormFieldHom h hC₀ h.barEquiv) ≃* fixedSubgroup α :=
        (fixedSubgroupCongrEquiv θ _).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))
      exact graphNormal_false_of_notSp6Components
        (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e1.symm hαfix)
        (notSp6Components_of_isCharacteristicP hch)
    · exact Or.inr h2
  · set ψ := gramTransportSU h hHC with hψ
    have : Group.IsPerfect (gramSU h (C₀ : Matrix (Fin n) (Fin n) K)) := by
      have := CFSG.RankThree.Classical.isPerfect_gramSU_one h hn hq
      exact Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) (MulEquiv.surjective _)
    have hθψ : ∀ g : gramSU h (C₀ : Matrix (Fin n) (Fin n) K),
        θ (g : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) =
          ((ψ g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
            primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      fun g => hθ g (ψ g) rfl
    set γ : MulAut (gramSU h (C₀ : Matrix (Fin n) (Fin n) K)) := (ψ.trans β).trans ψ.symm
      with hγdef
    have hγ : γ = primeFormFieldSU h hC₀ h.barEquiv := by
      refine graphTorus_mulAut_eq_of_inv_mul_mem_center fun g => ?_
      apply normOneScalars_le_center h _ n
      rw [← QuotientGroup.eq]
      apply θ.injective
      have e1 : ψ (γ g) = β (ψ g) := by
        rw [hγdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        rfl
      calc θ ((γ g : gramSU h (C₀ : Matrix (Fin n) (Fin n) K)) :
            primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) =
          ((ψ (γ g) : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
            primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hθψ _
        _ = ((β (ψ g) : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
            primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [e1]
        _ = α ((ψ g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
            primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := (hαmk _).symm
        _ = α (θ (g : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K))) := by rw [hθψ]
        _ = θ (primeFormFieldAut h hC₀ h.barEquiv
            (g : primeFormP h (C₀ : Matrix (Fin n) (Fin n) K))) := by
          rw [hθα, MulEquiv.symm_apply_apply]
        _ = θ ((primeFormFieldSU h hC₀ h.barEquiv g : gramSU h (C₀ : Matrix (Fin n) (Fin n) K)) :
            primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) := by rw [primeFormFieldAut_mk]
    intro g
    rw [← hγ, hγdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl

theorem primeFormFieldSU_gramTransportSU {C C' : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hC' : IsPrimeFormGram C') {P : GL (Fin n) K}
    (hPbar : (P : Matrix (Fin n) (Fin n) K).map h.bar = P)
    (hP : ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * P = C')
    (g : gramSU h (C' : Matrix (Fin n) (Fin n) K)) :
    primeFormFieldSU h hC h.barEquiv (gramTransportSU h hP g) =
      gramTransportSU h hP (primeFormFieldSU h hC' h.barEquiv g) := by
  have hP' : glAut h.barEquiv P = P := Units.ext (by rw [coe_glAut]; exact hPbar)
  apply Subtype.ext
  change glAut h.barEquiv (P * (g : GL (Fin n) K) * P⁻¹) =
    P * glAut h.barEquiv (g : GL (Fin n) K) * P⁻¹
  rw [map_mul, map_mul, map_inv, hP']

end Descent

section Six

variable (h : UnitaryFieldData 2 f K)

theorem exists_unitary6_normal_form
    (β : MulAut (gramSU h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)))
    (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉ (MulAut.conj : _ ⧸ center (gramSU h ((1 : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) →* MulAut _).range)
    {f' : ℕ} (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ Ψ : uGroup6 h ≃* gramSU h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K),
      ∀ g, β (Ψ g) = Ψ (primeFormFieldSU h (isPrimeFormGram_graphGram6 K) h.barEquiv g) := by
  obtain ⟨H, C₀, hC₀, hH, hcase, hint⟩ :=
    exists_unitary_normal_form h (by norm_num) (by omega) β hβ2 hβo hfix
  have hC6 : C₀ = graphGram6 K := by
    rcases hcase with ⟨-, hodd⟩ | ⟨r, hr, hJ⟩
    · exact absurd (by decide : Even 6) hodd
    · obtain rfl : r = 3 := by omega
      exact Units.ext hJ
  subst hC6
  exact ⟨gramTransportSU h hH, hint⟩

end Six

section Gram7

@[expose] def gram7ChangeMat : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 0, 1;
     1, 0, 1, 1, 0, 0, 1;
     0, 0, 1, 1, 0, 0, 1;
     0, 1, 0, 0, 0, 1, 1;
     0, 1, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1, 1;
     0, 0, 1, 0, 0, 1, 1]

set_option maxRecDepth 10000 in
theorem gram7ChangeMat_transpose_mul : gram7ChangeMatᵀ * gram7ChangeMat = gram7 (ZMod 2) := by
  decide

set_option maxRecDepth 10000 in
theorem gram7ChangeMat_mul_inv : gram7ChangeMat * (gram7 (ZMod 2) * gram7ChangeMatᵀ) = 1 := by
  decide

set_option maxRecDepth 10000 in
theorem gram7ChangeMat_inv_mul : gram7 (ZMod 2) * gram7ChangeMatᵀ * gram7ChangeMat = 1 := by
  decide

variable (K) [CharP K 2]

theorem map_gram7_zmod :
    (gram7 (ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) = gram7 K := by
  ext i j
  simp only [Matrix.map_apply, gram7, of_apply]
  split_ifs <;> simp

@[expose] def gram7Change : GL (Fin 7) K where
  val := gram7ChangeMat.map (ZMod.castHom (dvd_refl 2) K)
  inv := (gram7 (ZMod 2) * gram7ChangeMatᵀ).map (ZMod.castHom (dvd_refl 2) K)
  val_inv := by
    rw [← Matrix.map_mul, gram7ChangeMat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  inv_val := by
    rw [← Matrix.map_mul, gram7ChangeMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

variable {K}

theorem gram7Change_map_bar {p f : ℕ} (h : UnitaryFieldData p f K) :
    ((gram7Change K : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).map h.bar = gram7Change K := by
  change (gram7ChangeMat.map (ZMod.castHom (dvd_refl 2) K)).map h.bar =
    gram7ChangeMat.map (ZMod.castHom (dvd_refl 2) K)
  rw [Matrix.map_map]
  congr 1
  funext x
  exact ringHom_apply_of_mem_bot h.bar (by
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective x
    rw [map_intCast]
    exact intCast_mem _ y)

theorem gram7Change_gram {p f : ℕ} (h : UnitaryFieldData p f K) :
    (((gram7Change K : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).map h.bar)ᵀ *
        ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (gram7Change K : GL (Fin 7) K) =
      gram7 K := by
  rw [gram7Change_map_bar, Units.val_one, Matrix.mul_one]
  change (gram7ChangeMat.map (ZMod.castHom (dvd_refl 2) K))ᵀ *
    gram7ChangeMat.map (ZMod.castHom (dvd_refl 2) K) = gram7 K
  rw [← transpose_map, ← Matrix.map_mul, gram7ChangeMat_transpose_mul, map_gram7_zmod]

end Gram7

section Seven

variable (h : UnitaryFieldData 2 f K)

theorem exists_unitary7_normal_form
    (β : MulAut (gramSU h ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)))
    (hβ2 : centerQuotientAut β * centerQuotientAut β = 1)
    (hβo : centerQuotientAut β ∉ (MulAut.conj : _ ⧸ center (gramSU h ((1 : GL (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K)) →* MulAut _).range)
    {f' : ℕ} (hfix : LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f') :
    ∃ Ψ : uGroup7 h ≃* gramSU h ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K),
      ∀ g, β (Ψ g) = Ψ (primeFormFieldSU h (isPrimeFormGram_graphGram7 K) h.barEquiv g) := by
  have : CharP K 2 := h.charP
  obtain ⟨H, C₀, hC₀, hH, hcase, hint⟩ :=
    exists_unitary_normal_form h (by norm_num) (by omega) β hβ2 hβo hfix
  have hC1 : C₀ = 1 := by
    rcases hcase with ⟨h1, -⟩ | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  subst hC1
  have hP : (((gram7Change K : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).map h.bar)ᵀ *
      ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * (gram7Change K : GL (Fin 7) K) =
        ((graphGram7 K : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := gram7Change_gram h
  refine ⟨(gramTransportSU h hP).trans (gramTransportSU h hH), fun g => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hint,
    primeFormFieldSU_gramTransportSU h hC₀ (isPrimeFormGram_graphGram7 K) (gram7Change_map_bar h)
      hP]

end Seven

end CFSG.SeitzReduction.F4Pilot
