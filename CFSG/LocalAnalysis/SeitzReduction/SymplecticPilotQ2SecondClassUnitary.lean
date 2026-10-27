module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassQuot
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuotRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

section Coset

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_unitary_coords_nsQuot {m : ℕ} (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hglob : NsRowGlobalQuot e t .unitaryEven)
    (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 1 K')
      (C₀ : GL (Fin (2 * (m + 1))) K') (hC₀ : IsPrimeFormGram C₀)
      (_ : ¬(2 * (m + 1) = 3 ∧ 2 ^ 1 = 2))
      (ε : nsGlobal e ⧸ center (nsGlobal e) ≃*
        primeFormP h (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K')),
      (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K') =
        blockSwapJ (2 * (m + 1)) (m + 1) ∧
      MulAut.congr ε (centerQuotAction (nsGlobal e) ⟨t, htN⟩) =
        primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h) := by
  have hS : LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU (2 * (m + 1)) 2 1 := hglob.1.2.2
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  obtain ⟨K', _, h, C₀, hC₀, -, hq, φ, ε, hcase, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU' hS (centerQuotAction_mul_self ht htN) hout hfix
  have hφ' : φ = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hφ, UnitaryPilot.barRingEquiv_apply]
  rcases hcase with ⟨hodd, -⟩ | ⟨r, hr, hJ⟩
  · exact absurd (even_two_mul (m + 1)) (Nat.not_even_iff_odd.2 hodd)
  · obtain rfl : r = m + 1 := by omega
    exact ⟨K', inferInstance, h, C₀, hC₀, hq, ε, hJ, hε.trans (by rw [hφ'])⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem cosetInnConjInput_nsUnitaryQuot {m : ℕ} (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K)
    {t : G} (ht : orderOf t = 2) (hglob : NsRowGlobalQuot e t .unitaryEven)
    (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    CosetInnConjInput (centerQuotAction (nsGlobal e) ⟨t, htN⟩) := by
  obtain ⟨K', _, h, C₀, hC₀, hq, ε, -, hε⟩ := exists_unitary_coords_nsQuot e ht hglob htN
  apply cosetInnConjInput_of_congr ε
  rw [hε]
  exact cosetInnConjInput_fieldBar h C₀ hC₀ (by omega) hq

omit [Finite G] [CharP K 2] in
theorem spCosetCardOn_nsUnitaryQuot (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hglob : NsRowGlobalQuot e t .unitaryEven) (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    SpCosetCardOn (m + 1) K (centerQuotAction (nsGlobal e) ⟨t, htN⟩) := by
  intro y hy2
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨K', _, h, C₀, hC₀, hq, ε, hJ₀, hε⟩ := exists_unitary_coords_nsQuot e ht hglob htN
  have : CharP K' 2 := h.charP
  have : Finite K' := h.finite
  set θt := centerQuotAction (nsGlobal e) ⟨t, htN⟩ with hθt
  set fb := primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h) with hfb
  set α := MulAut.congr ε (MulAut.conj y * θt) with hαdef
  have hα : α = MulAut.conj (ε y) * fb := by
    rw [hαdef, map_mul, congr_conj_eq_conj_apply, hε]
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hy2, map_one]
  have hm' : 3 ≤ 2 * (m + 1) := by omega
  have hα1 : α ≠ 1 := by
    intro h1
    apply (hglob.2 htN).1
    have h2 : MulAut.conj y * θt = 1 :=
      (MulAut.congr ε).injective (by rw [← hαdef, h1, map_one])
    refine ⟨y⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hαo : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ε y)
  have hαψ : α = primeFormPsi h hC₀ ⟨⟨s, s.2.1⟩, UnitaryPilot.barRingEquiv h⟩ := by
    rw [hα, primeFormPsi_apply, primeFormConjHom_eq_conj, ← hs]
  have hfac : ∀ x, primeFormFieldFactor h hC₀ hm' hq α x = h.bar x := by
    intro x
    rw [hαψ, primeFormFieldFactor_psi]
    rfl
  obtain ⟨-, -, C₁, hC₁, hcase₁, -, -, -, -, ⟨θ', -, hθ'α⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC₀ hm' hq α hαo hfac
  have hφ : primeFormFieldFactor h hC₀ hm' hq α = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hfac, UnitaryPilot.barRingEquiv_apply]
  have hαθ : α = MulAut.congr θ' (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hθ'α x, hφ]
    rfl
  rcases hcase₁ with h1 | ⟨r, hr, hJ⟩
  · right
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [← LinearPilot.card_fixedSubgroup_congr ε, ← hαdef, hαθ,
      LinearPilot.card_fixedSubgroup_congr]
    have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
    have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
    obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h hm' hq hC₁
      (Or.inl h1) _ (fun x => UnitaryPilot.barRingEquiv_apply h x)
    obtain rfl : Cl = 1 := by
      apply Units.ext
      apply Matrix.map_injective h.fixedField.subtype_injective
      change (Cl : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) h.fixedField).map
          h.fixedField.subtype =
        ((1 : GL (Fin (2 * (m + 1))) h.fixedField) : Matrix (Fin (2 * (m + 1)))
          (Fin (2 * (m + 1))) h.fixedField).map h.fixedField.subtype
      rw [hCl, h1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Nat.card_congr Φ.toEquiv, card_matrixIsometryGroup_one_eq (F := h.fixedField)
      (by omega) h.card_fixedField (by omega) ⟨0, by omega⟩]
    have : Fintype K := Fintype.ofFinite K
    have : Fintype h.fixedField := Fintype.ofFinite h.fixedField
    set σ : K ≃+* h.fixedField := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h.card_fixedField])
      with hσ
    rw [← map_statedSpMap_centralizer_siegDiag σ,
      Subgroup.card_map_of_injective
        (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1))]
  · left
    obtain rfl : r = m + 1 := by omega
    obtain rfl : C₁ = C₀ := Units.ext (hJ.trans hJ₀.symm)
    refine exists_mulAut_mul_eq_of_congr ε (γ := θ') ?_
    rw [hε, ← hαdef, hαθ, LinearPilot.mulAut_congr_eq_mul, hfb]
    group

end Coset

section Shape

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] in
theorem nsPartnerShapeOn_of_iType_quot (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hglob : NsRowGlobalQuot e t .unitaryEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    {α : MulAut (nsGlobal e ⧸ center (nsGlobal e))} {K'' : Type} [Field K'']
    (h'' : UnitaryFieldData 2 1 K'')
    (ψ : nsGlobal e ⧸ center (nsGlobal e) ≃* primeFormP h'' ((1 : GL (Fin (2 * (m + 1))) K'') :
      Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K''))
    (θ : MulAut (primeFormP h'' ((1 : GL (Fin (2 * (m + 1))) K'') :
      Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K'')))
    (he : MulAut.congr ψ α =
      θ * primeFormFieldHom h'' isPrimeFormGram_one (UnitaryPilot.barRingEquiv h'') * θ⁻¹) :
    NsPartnerShapeOn (m + 1) K (centerQuotAction (nsGlobal e) ⟨t, htN⟩) α := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨K', _, h, C₀, hC, hq, ε, hJ₀, hε⟩ := exists_unitary_coords_nsQuot e ht hglob htN
  have : CharP K' 2 := h.charP
  have : Finite K' := h.finite
  have : CharP h.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  have : Finite h.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have : CharP K'' 2 := h''.charP
  have : Finite K'' := h''.finite
  have : CharP h''.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h''
  have : Finite h''.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h''
  have hm' : 3 ≤ 2 * (m + 1) := by omega
  have hq'' : ¬(2 * (m + 1) = 3 ∧ 2 ^ 1 = 2) := by omega
  have hC1 : IsPrimeFormGram (1 : GL (Fin (2 * (m + 1))) K'') := isPrimeFormGram_one
  set fI := primeFormFieldHom h'' hC1 (UnitaryPilot.barRingEquiv h'') with hfI
  set fJ := primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) with hfJ
  have hαout : α ∉ (MulAut.conj : nsGlobal e ⧸ center (nsGlobal e) →* MulAut _).range := by
    rintro ⟨y, rfl⟩
    rw [congr_conj_eq_conj_apply] at he
    have h1 : fI = MulAut.conj (θ⁻¹ (ψ y)) := by
      calc fI = θ⁻¹ * (θ * fI * θ⁻¹) * θ := by group
        _ = θ⁻¹ * MulAut.conj (ψ y) * θ := by rw [← he]
        _ = MulAut.conj (θ⁻¹ (ψ y)) := by
            ext x
            simp [MulAut.conj_apply]
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (θ⁻¹ (ψ y))
    have h3 := primeFormFieldFactor_apply h'' hC1 hm' hq'' 1 (UnitaryPilot.barRingEquiv h'')
    rw [map_one, one_mul, ← hfI, h1, ← hs, ← primeFormConjHom_eq_conj] at h3
    have h4 := primeFormFieldFactor_apply h'' hC1 hm' hq'' ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one] at h4
    exact barRingEquiv_ne_one (h := h'') (h3.symm.trans h4)
  have hα2 : α * α = 1 := by
    apply (MulAut.congr ψ).injective
    rw [map_mul, he, map_one]
    calc θ * fI * θ⁻¹ * (θ * fI * θ⁻¹) = θ * (fI * fI) * θ⁻¹ := by group
      _ = 1 := by rw [hfI, fieldBar_mul_self, mul_one, mul_inv_cancel]
  set β := MulAut.congr ε α with hβdef
  have hβ2 : β * β = 1 := by rw [hβdef, ← map_mul, hα2, map_one]
  have hβout : β ∉ (MulAut.conj : primeFormP h (C₀ : Matrix (Fin (2 * (m + 1)))
      (Fin (2 * (m + 1))) K') →* MulAut _).range := by
    rintro ⟨y, hy⟩
    apply hαout
    refine ⟨ε.symm y, ?_⟩
    rw [← congr_conj_eq_conj_apply, hy, hβdef, mulAut_congr_symm_congr_apply]
  have hβ1 : β ≠ 1 := fun h1 => hβout ⟨1, by rw [map_one, h1]⟩
  have hβo : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨hcases, hinn, -, -⟩ := even_unitary_involution_matrix_lifts h hC hm' hq β hβo
  have hfacβ : ∀ x, primeFormFieldFactor h hC hm' hq β x = h.bar x := by
    refine hcases.resolve_left fun hid => ?_
    obtain ⟨s, -, -, hs⟩ := hinn hid
    exact hβout ⟨_, ((primeFormConjHom_eq_conj h _ s).symm.trans hs.symm)⟩
  obtain ⟨-, -, C₁, hC₁, hcase₁, -, -, -, -, ⟨θ₁, -, hθ₁β⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hm' hq β hβo hfacβ
  have hφ : primeFormFieldFactor h hC hm' hq β = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hfacβ, UnitaryPilot.barRingEquiv_apply]
  have hβθ : β = MulAut.congr θ₁ (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hθ₁β x, hφ]
    rfl
  have : Fintype K := Fintype.ofFinite K
  have : Fintype h.fixedField := Fintype.ofFinite h.fixedField
  have : Fintype h''.fixedField := Fintype.ofFinite h''.fixedField
  set σ : K ≃+* h.fixedField := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h.card_fixedField]) with hσ
  set σ'' : K ≃+* h''.fixedField := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h''.card_fixedField])
    with hσ''
  have hp0 : 0 < m + 1 := by omega
  have hcardα : Nat.card (fixedSubgroup α) =
      Nat.card (centralizer ({siegDiag K ⟨0, hp0⟩ 1} : Set (StatedSp (m + 1) K))) := by
    rw [← LinearPilot.card_fixedSubgroup_congr ψ, he, ← LinearPilot.mulAut_congr_eq_mul,
      LinearPilot.card_fixedSubgroup_congr]
    obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h'' hm' hq'' hC1
      (Or.inl (by rw [Units.val_one])) _ (fun x => UnitaryPilot.barRingEquiv_apply h'' x)
    obtain rfl : Cl = 1 := by
      apply Units.ext
      apply Matrix.map_injective h''.fixedField.subtype_injective
      change (Cl : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) h''.fixedField).map
          h''.fixedField.subtype =
        ((1 : GL (Fin (2 * (m + 1))) h''.fixedField) : Matrix (Fin (2 * (m + 1)))
          (Fin (2 * (m + 1))) h''.fixedField).map h''.fixedField.subtype
      rw [hCl, Units.val_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Nat.card_congr Φ.toEquiv, card_matrixIsometryGroup_one_eq (F := h''.fixedField)
      (by omega) h''.card_fixedField (by omega) ⟨0, hp0⟩,
      ← map_statedSpMap_centralizer_siegDiag σ'',
      Subgroup.card_map_of_injective (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1))]
  rcases hcase₁ with h1 | ⟨r, hr, hJ⟩
  swap
  · exfalso
    have hrn : m + 1 = r := by omega
    subst hrn
    obtain rfl : C₁ = C₀ := Units.ext (hJ.trans hJ₀.symm)
    have h2 : Nat.card (fixedSubgroup α) = Nat.card (StatedSp (m + 1) K) := by
      rw [← LinearPilot.card_fixedSubgroup_congr ε, ← hβdef, hβθ,
        LinearPilot.card_fixedSubgroup_congr, ← range_uModelP (by omega) hq hC₁ hJ₀,
        ← Nat.card_congr (MonoidHom.ofInjective (uModelP_injective (by omega) hJ₀)).toEquiv,
        card_statedSp_eq_of_ringEquiv σ]
    have h3 := card_centralizer_siegDiag_lt (K := K) (⟨0, hp0⟩ : Fin (m + 1))
    omega
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 1), p = ⟨0, hp0⟩ := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂, θ', h2, hθ'⟩ :=
    exists_iType_conj_uModel_siegDiag (h := h) (by omega) hq hC hJ₀ p
  obtain rfl : C₂ = C₁ := Units.ext (h2.trans h1.symm)
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : MulAut (primeFormP h (C₀ : Matrix (Fin (2 * (m + 1)))
      (Fin (2 * (m + 1))) K')), Γ = θ'.symm.trans θ₁ := ⟨_, rfl⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : primeFormP h (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K') ≃*
      nsGlobal e ⧸ center (nsGlobal e), Ξ = Γ.trans ε.symm := ⟨_, rfl⟩
  obtain ⟨Zp, hZp⟩ : ∃ Zp, Zp = uModelP h hJ₀ (siegDiag h.fixedField p 1) := ⟨_, rfl⟩
  have hβΓ : β = MulAut.congr Γ (MulAut.conj Zp * fJ) := by
    rw [hβθ, hZp, hfJ, hθ', hΓ, mulAut_congr_trans_apply, mulAut_congr_symm_congr_apply]
  have hαΞ : α = MulAut.congr Ξ (MulAut.conj Zp * fJ) := by
    rw [hΞ, mulAut_congr_trans_apply, ← hβΓ, hβdef, mulAut_congr_symm_congr_apply]
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : StatedSp (m + 1) K →* nsGlobal e ⧸ center (nsGlobal e), ψ₀ =
    Ξ.toMonoidHom.comp ((uModelP h hJ₀).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* h.fixedField) (m + 1))) := ⟨_, rfl⟩
  have hψ₀inj : Function.Injective ψ₀ := by
    rw [hψ₀]
    exact Ξ.injective.comp ((uModelP_injective (by omega) hJ₀).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1)))
  have hψ₀z : ψ₀ (siegDiag K p 1) = Ξ Zp := by
    rw [hψ₀, hZp]
    change Ξ (uModelP h hJ₀ (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* h.fixedField)
      (m + 1) (siegDiag K p 1))) = _
    rw [statedSpMap_siegDiag]
  obtain ⟨η, hη⟩ : ∃ η : MulAut (nsGlobal e ⧸ center (nsGlobal e)), η = MulAut.congr Ξ fJ :=
    ⟨_, rfl⟩
  refine ⟨ψ₀, η, p, hψ₀inj, ?_, ?_, ?_, ?_⟩
  · rw [hψ₀z, hαΞ, map_mul, congr_conj_eq_conj_apply, hη]
  · intro y
    rw [hη, hψ₀]
    change Ξ (fJ (Ξ.symm (Ξ (uModelP h hJ₀ (CFSG.SeitzReduction.F4Pilot.statedSpMap
      (σ : K →+* h.fixedField) (m + 1) y))))) = Ξ (uModelP h hJ₀
        (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* h.fixedField) (m + 1) y))
    rw [MulEquiv.symm_apply_apply, hfJ, fieldBar_uModelP hC hJ₀]
  · refine exists_mulAut_mul_eq_of_congr ε (γ := Γ) ?_
    rw [hε, hη, hΞ, mulAut_congr_trans_apply, mulAut_congr_congr_symm_apply,
      LinearPilot.mulAut_congr_eq_mul]
    group
  · rw [hαΞ, LinearPilot.fixedSubgroup_congr_eq_map, hZp, hfJ,
      fixedSubgroup_conj_uModel_siegDiag_mul_fieldBar (by omega) hC hJ₀ p, hψ₀,
      ← Subgroup.map_map, ← Subgroup.map_map, map_statedSpMap_centralizer_siegDiag σ p]

theorem spTwoUnitaryEvenSecondClassQuotInput_holds : SpTwoUnitaryEvenSecondClassQuotInput := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt _ hglob g hg hchar
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hm : 3 ≤ n := by omega
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  have hperf : Group.IsPerfect (nsGlobal e) := hglob.1.1.1
  have hZ : Odd (Nat.card (center (nsGlobal e))) := hglob.1.2.1
  have hty' : LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU (2 * (n + 1)) 2 1 := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSU (2 * (n + 1)) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hq : ¬(2 * (n + 1) = 3 ∧ 2 ^ 1 = 2) := by omega
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * (n + 1))) K') :
      Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K'), orderOf y = 2 →
      1 * (n + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * (n + 1))) K') :
          Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K'))))).factorization 2 := by
    intro y hy
    set φ := CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h (2 * (n + 1))
    have h1 := unitaryEvenInnerTwoPart_holds 1 K' h (n + 1) (by omega) (φ y)
      (by rw [MulEquiv.orderOf_eq, hy])
    rw [card_centralizer_map_mulEquiv] at h1
    have h0 : (1 : ℕ).factorization 2 = 0 := by simp
    rw [h0]
    simp only [one_mul] at h1 ⊢
    omega
  have hy0 := exists_orderOf_eq_two_quot_nsGlobal hK hm e ht hKt hZ ψ
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  have hαw : MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
      MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
    rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
  have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ
      (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩)))).factorization 2 ≤
        1 * (n + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
      (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
  obtain ⟨C₀, hC₀, hc, θ, he⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
  rcases hc with h1 | ⟨r, hr, hJ⟩
  ·
    have hC1 : C₀ = 1 := Units.ext h1
    subst hC1
    rw [LinearPilot.mulAut_congr_eq_mul] at he
    have hsh := nsPartnerShapeOn_of_iType_quot hK hm e ht hglob htN h ψ θ he
    have htZ : t ∉ centralizer (nsGlobal e : Set G) := by
      intro htZ
      apply (hglob.2 htN).1
      refine ⟨1, MulEquiv.ext fun q => ?_⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center (nsGlobal e)) q
      rw [map_one, MulAut.one_apply, centerQuotAction_apply_mk]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← mem_centralizer_iff.1 htZ y y.2,
        mul_inv_cancel_right]
    have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
    exact false_of_nsPartnerShapeQuot hset hK hm e ht hKt hLS hZ htN hodd
      (fun h' hh γ hγ =>
        mem_normalizer_nsGlobal_of_conj_centerQuotAction hset hK hm e ht hKt hperf hZ htN hh γ hγ)
      (fun k P hP hPc => (F4Pilot.le_centralizerPerfectCore hP hPc).trans
        (centralizerPerfectCore_nsTorusSp_le_nsGlobal e k))
      (cosetInnConjInput_nsUnitaryQuot hm e ht hglob htN)
      (spCosetCardOn_nsUnitaryQuot hK hm e ht hglob htN) hg hsh
  ·
    obtain rfl : r = n + 1 := by omega
    have : CharP h.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
    have : Finite h.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
    have hF2 : Nat.card h.fixedField = 2 := by rw [h.card_fixedField, pow_one]
    have Φ := (fixedSubgroupCongrEquiv ψ _).trans ((MulEquiv.subgroupCongr
      (congrArg fixedSubgroup he)).trans (fixedSubgroupCongrEquiv θ _).symm)
    have hrange := range_uModelP (by omega) hq hC₀ hJ
    set E := (MonoidHom.ofInjective (uModelP_injective (by omega) hJ)).trans
      (MulEquiv.subgroupCongr hrange) with hE
    have : IsSimpleGroup (StatedSp (n + 1) h.fixedField) :=
      isSimpleGroup_statedSp_two hF2 (by omega)
    have : IsSimpleGroup (fixedSubgroup (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h))) :=
      E.symm.isSimpleGroup_congr.2 this
    have hy : orderOf (E (nsElt (K := h.fixedField) (⟨0, by omega⟩ : Fin (n + 1)))) = 3 := by
      rw [MulEquiv.orderOf_eq, orderOf_nsElt]
    exact not_isCharacteristicP_two_of_isSimpleGroup hy (isCharacteristicP_of_mulEquiv Φ hchar)

end Shape

end CFSG.SeitzReduction.SymplecticPilot
