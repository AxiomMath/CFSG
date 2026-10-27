module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose, reducible] def J5GL : GL (Fin 5) F4 := ⟨J5, J5, J5_mul_J5, J5_mul_J5⟩

@[simp] theorem coe_J5GL : ((J5GL : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) = J5 := rfl

theorem isPrimeFormGram_J5GL : IsPrimeFormGram J5GL where
  symm := J5_transpose
  prime i j := by
    change J5 i j ∈ (⊥ : Subfield F4)
    rw [J5, Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem F4_eq_one_of_pow_five : ∀ x : F4, x ^ 5 = 1 → x = 1 := by decide

theorem normOneScalars_SU52_eq_bot : normOneScalars hF4 (gramSU hF4 J5) 5 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  obtain ⟨c, -, hc5, hg⟩ := hg
  have hc : c = 1 := Units.ext (F4_eq_one_of_pow_five _ (by
    rw [← Units.val_pow_eq_pow_val, hc5, Units.val_one]))
  apply Subtype.ext
  rw [hg, hc, map_one]
  rfl

@[expose] def toJ : SU52 ≃* gramSU hF4 J5 := MulEquiv.subgroupCongr rfl

@[simp] theorem coe_toJ (g : SU52) : ((toJ g : gramSU hF4 J5) : GL (Fin 5) F4) = g := rfl

@[simp] theorem coe_toJ_symm (g : gramSU hF4 J5) :
    ((toJ.symm g : SU52) : GL (Fin 5) F4) = g := rfl

@[expose] def toU (s : SU52) : primeFormUnitary hF4 J5 := ⟨toJ s, (toJ s).2.1⟩

@[simp] theorem coe_toU (s : SU52) : ((toU s : primeFormUnitary hF4 J5) : GL (Fin 5) F4) = s :=
  rfl

@[expose] def projEquiv : SU52 ≃* primeFormP hF4 J5 :=
  toJ.trans ((QuotientGroup.quotientBot (G := gramSU hF4 J5)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq normOneScalars_SU52_eq_bot.symm))

theorem projEquiv_apply (g : SU52) :
    projEquiv g = ((toJ g : gramSU hF4 J5) : primeFormP hF4 J5) := rfl

theorem projEquiv_symm_mk (g : gramSU hF4 J5) :
    projEquiv.symm (g : primeFormP hF4 J5) = toJ.symm g := by
  rw [MulEquiv.symm_apply_eq, projEquiv_apply, MulEquiv.apply_symm_apply]

@[expose] def fieldAut (φ : F4 ≃+* F4) : MulAut SU52 :=
  primeFormFieldSU hF4 (C := J5GL) isPrimeFormGram_J5GL φ

@[simp] theorem coe_fieldAut_apply (φ : F4 ≃+* F4) (g : SU52) :
    ((fieldAut φ g : SU52) : GL (Fin 5) F4) = glAut φ (g : GL (Fin 5) F4) :=
  rfl

theorem mat_fieldAut (φ : F4 ≃+* F4) (g : SU52) : mat (fieldAut φ g) = (mat g).map φ := rfl

@[expose] def fieldHom : (F4 ≃+* F4) →* MulAut SU52 where
  toFun := fieldAut
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_fieldAut_apply, map_one]
    rfl)
  map_mul' φ ψ := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, coe_fieldAut_apply, coe_fieldAut_apply, coe_fieldAut_apply, map_mul]
    rfl)

@[simp] theorem fieldHom_apply (φ : F4 ≃+* F4) : fieldHom φ = fieldAut φ := rfl

theorem fieldAut_mul_conj_mul_inv (φ : F4 ≃+* F4) (s : SU52) :
    fieldAut φ * MulAut.conj s * (fieldAut φ)⁻¹ = MulAut.conj (fieldAut φ s) := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem congr_conj_mul_fieldAut (s : SU52) (φ : F4 ≃+* F4) :
    MulAut.congr projEquiv (MulAut.conj s * fieldAut φ) =
      primeFormConjHom hF4 J5 (toU s) *
        primeFormFieldHom hF4 (C := J5GL) isPrimeFormGram_J5GL φ := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, projEquiv_symm_mk,
    projEquiv_apply, MulAut.mul_apply]
  change _ = primeFormConjHom hF4 J5 (toU s)
    (primeFormFieldAut hF4 isPrimeFormGram_J5GL φ (g : primeFormP hF4 _))
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem three_le_five : 3 ≤ 5 := by norm_num

theorem not_five_three : ¬(5 = 3 ∧ 2 ^ 1 = 2) := fun e => absurd e.1 (by norm_num)

@[expose] def fieldFactor : MulAut SU52 →* (F4 ≃+* F4) :=
  (primeFormFieldFactor hF4 (C := J5GL) isPrimeFormGram_J5GL three_le_five
    not_five_three).comp (MulAut.congr projEquiv).toMonoidHom

theorem fieldFactor_apply (α : MulAut SU52) :
    fieldFactor α = primeFormFieldFactor hF4 (C := J5GL) isPrimeFormGram_J5GL three_le_five
      not_five_three (MulAut.congr projEquiv α) :=
  rfl

@[simp] theorem fieldFactor_conj_mul (s : SU52) (φ : F4 ≃+* F4) :
    fieldFactor (MulAut.conj s * fieldAut φ) = φ := by
  rw [fieldFactor_apply, congr_conj_mul_fieldAut, primeFormFieldFactor_apply]

@[simp] theorem fieldFactor_fieldAut (φ : F4 ≃+* F4) : fieldFactor (fieldAut φ) = φ := by
  simpa using fieldFactor_conj_mul 1 φ

@[simp] theorem fieldFactor_conj (s : SU52) : fieldFactor (MulAut.conj s) = 1 := by
  have e := fieldFactor_conj_mul s 1
  rwa [← fieldHom_apply, map_one, mul_one] at e

theorem exists_pow_five_eq_of_norm_eq_one {μ : F4} (hμ : hF4.norm μ = 1) :
    ∃ l : F4, l ^ 5 = μ ∧ hF4.norm l = 1 := by
  have key : ∀ μ : F4, μ * μ ^ 2 = 1 → ∃ l : F4, l ^ 5 = μ ∧ l * l ^ 2 = 1 := by decide
  have hn : ∀ c : F4, hF4.norm c = c * c ^ 2 := fun c => by
    rw [UnitaryFieldData.norm, hF4_bar, bar_apply]
  obtain ⟨l, hl, hl'⟩ := key μ (by rw [← hn]; exact hμ)
  exact ⟨l, hl, by rw [hn]; exact hl'⟩

theorem det_scalar_five (c : F4) : (Matrix.scalar (Fin 5) c).det = c ^ 5 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp

theorem exists_mem_SU52_conj_eq {A : GL (Fin 5) F4} (hA : A ∈ primeFormUnitary hF4 J5) :
    ∃ s : SU52, ∀ g : GL (Fin 5) F4, A * g * A⁻¹ = s * g * (s : GL (Fin 5) F4)⁻¹ := by
  obtain ⟨l, hl5, hlN⟩ := exists_pow_five_eq_of_norm_eq_one (norm_det_eq_one hF4 J5GL hA)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl5
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hl5.symm
  set u : F4ˣ := (Units.mk0 l hl0)⁻¹ with hu
  have huN : hF4.norm (u : F4) = 1 := by
    rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv_eq hF4, hlN, inv_one]
  have hsU : GeneralLinearGroup.scalar (Fin 5) u * A ∈ primeFormUnitary hF4 J5 := by
    refine mul_mem ?_ hA
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, huN,
      one_smul]
  have hsdet : ((GeneralLinearGroup.scalar (Fin 5) u * A : GL (Fin 5) F4) :
      Matrix (Fin 5) (Fin 5) F4).det = 1 := by
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, det_scalar_five, ← hl5, hu,
      Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_pow, inv_mul_cancel₀ hl0, one_pow]
  refine ⟨⟨_, hsU, hsdet⟩, fun g => ?_⟩
  change A * g * A⁻¹ = GeneralLinearGroup.scalar (Fin 5) u * A * g *
    (GeneralLinearGroup.scalar (Fin 5) u * A)⁻¹
  have hc := (commute_scalar u (A * g * A⁻¹)).eq
  calc A * g * A⁻¹ = A * g * A⁻¹ * GeneralLinearGroup.scalar (Fin 5) u *
        (GeneralLinearGroup.scalar (Fin 5) u)⁻¹ := by group
    _ = _ := by rw [hc]; group

theorem exists_eq_conj_mul_fieldAut (α : MulAut SU52) :
    ∃ s : SU52, α = MulAut.conj s * fieldAut (fieldFactor α) := by
  set hC := isPrimeFormGram_J5GL
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective hF4 hC three_le_five not_five_three
    (MulAut.congr projEquiv α)
  have hφ : fieldFactor α = φ := by
    rw [fieldFactor_apply, ← hAφ, primeFormFieldFactor_psi]
  obtain ⟨s, hs⟩ := exists_mem_SU52_conj_eq A.2
  refine ⟨s, MulEquiv.ext fun g => projEquiv.injective ?_⟩
  rw [hφ]
  have e1 : projEquiv (α g) = MulAut.congr projEquiv α (projEquiv g) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  rw [e1, ← hAφ, primeFormPsi_apply, MulAut.mul_apply, projEquiv_apply, projEquiv_apply]
  change primeFormConjHom hF4 J5 A (primeFormFieldAut hF4 hC φ
    ((toJ g : gramSU hF4 J5) : primeFormP hF4 _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin 5) F4) * glAut φ (g : GL (Fin 5) F4) * (A : GL (Fin 5) F4)⁻¹ =
    s * glAut φ (g : GL (Fin 5) F4) * (s : GL (Fin 5) F4)⁻¹
  exact hs _

theorem conj_eq_one_iff (s : SU52) : MulAut.conj s = 1 ↔ s = 1 := by
  refine ⟨fun hs => ?_, fun hs => by rw [hs, map_one]⟩
  set hC := isPrimeFormGram_J5GL
  have h1 : primeFormPsi hF4 hC ⟨toU s, 1⟩ = 1 := by
    have e := congr_conj_mul_fieldAut s 1
    rw [← fieldHom_apply, map_one, mul_one, hs, map_one, map_one, mul_one] at e
    rw [primeFormPsi_apply, map_one, mul_one, ← e]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff hF4 hC three_le_five _).mp h1
  have hc1 : c = 1 := by
    refine Units.ext (F4_eq_one_of_pow_five _ ?_)
    have hdet := s.2.2
    change (((toU s : primeFormUnitary hF4 J5) : GL (Fin 5) F4) :
      Matrix (Fin 5) (Fin 5) F4).det = 1 at hdet
    rw [hc, GeneralLinearGroup.coe_scalar, det_scalar_five] at hdet
    exact hdet
  apply Subtype.ext
  change ((toU s : primeFormUnitary hF4 J5) : GL (Fin 5) F4) = 1
  rw [hc, hc1, map_one]

theorem conj_inj {s t : SU52} : MulAut.conj s = MulAut.conj t ↔ s = t := by
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, conj_eq_one_iff, mul_inv_eq_one] at e
  exact e

theorem conj_injective : Function.Injective (MulAut.conj : SU52 →* MulAut SU52) :=
  fun _ _ e => conj_inj.mp e

theorem center_SU52_eq_bot : center SU52 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => (conj_eq_one_iff z).1 ?_
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.conj_apply, MulAut.one_apply, ← mem_center_iff.1 hz g, mul_inv_cancel_right]

theorem conj_mul_fieldAut_inj {s t : SU52} {φ ψ : F4 ≃+* F4} :
    MulAut.conj s * fieldAut φ = MulAut.conj t * fieldAut ψ ↔ s = t ∧ φ = ψ := by
  refine ⟨fun e => ?_, fun e => by rw [e.1, e.2]⟩
  have hφ : φ = ψ := by
    rw [← fieldFactor_conj_mul s φ, e, fieldFactor_conj_mul]
  subst hφ
  exact ⟨conj_inj.mp (mul_right_cancel e), rfl⟩

theorem fieldFactor_eq_one_iff (α : MulAut SU52) :
    fieldFactor α = 1 ↔ ∃ s : SU52, α = MulAut.conj s := by
  constructor
  · intro hα
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut α
    rw [hα, ← fieldHom_apply, map_one, mul_one] at hs
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    exact fieldFactor_conj s

@[expose] def autPsi : SU52 ⋊[fieldHom] (F4 ≃+* F4) →* MulAut SU52 :=
  SemidirectProduct.lift MulAut.conj fieldHom fun φ => MonoidHom.ext fun s => by
    change MulAut.conj (fieldAut φ s) = fieldAut φ * MulAut.conj s * (fieldAut φ)⁻¹
    rw [fieldAut_mul_conj_mul_inv]

theorem autPsi_apply (s : SU52) (φ : F4 ≃+* F4) :
    autPsi ⟨s, φ⟩ = MulAut.conj s * fieldAut φ := by
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul, autPsi, SemidirectProduct.lift_inl,
    SemidirectProduct.lift_inr, fieldHom_apply]

@[expose] def autEquiv : SU52 ⋊[fieldHom] (F4 ≃+* F4) ≃* MulAut SU52 :=
  MulEquiv.ofBijective autPsi ⟨fun x y e => by
    obtain ⟨s, φ⟩ := x
    obtain ⟨t, ψ⟩ := y
    rw [autPsi_apply, autPsi_apply, conj_mul_fieldAut_inj] at e
    rw [e.1, e.2], fun α => by
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut α
    exact ⟨⟨s, fieldFactor α⟩, by rw [autPsi_apply, ← hs]⟩⟩

@[expose] def barEquiv : F4 ≃+* F4 :=
  { bar with
    invFun := bar
    left_inv := bar_bar
    right_inv := bar_bar }

@[simp] theorem barEquiv_apply (c : F4) : barEquiv c = bar c := rfl

theorem barEquiv_ne_one : barEquiv ≠ 1 := fun h => by
  have := congrArg (fun φ : F4 ≃+* F4 => φ F4.ω) h
  simp only [barEquiv_apply, RingAut.one_apply] at this
  exact absurd this (by decide)

theorem ringEquiv_eq_one_or_eq_barEquiv (φ : F4 ≃+* F4) : φ = 1 ∨ φ = barEquiv := by
  have hω : φ F4.ω * φ F4.ω + φ F4.ω + 1 = 0 := by
    rw [← map_mul, ← map_add, ← map_one φ, ← map_add,
      show F4.ω * F4.ω + F4.ω + 1 = 0 by decide, map_zero]
  have hroots : ∀ x : F4, x * x + x + 1 = 0 → x = F4.ω ∨ x = F4.ω + 1 := by decide
  have hall : ∀ c : F4, c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = F4.ω + 1 := by decide
  have hφ : ∀ c, φ c = c ∨ φ c = bar c → ∀ x, (φ F4.ω = F4.ω → φ x = x) := by
    intro _ _ x hx
    rcases hall x with rfl | rfl | rfl | rfl
    · exact map_zero φ
    · exact map_one φ
    · exact hx
    · rw [map_add, map_one, hx]
  rcases hroots _ hω with h | h
  · left
    refine RingEquiv.ext fun x => ?_
    rw [RingAut.one_apply]
    exact hφ 0 (Or.inl (map_zero φ)) x h
  · right
    refine RingEquiv.ext fun x => ?_
    rw [barEquiv_apply]
    rcases hall x with rfl | rfl | rfl | rfl
    · rw [map_zero, map_zero]
    · rw [map_one, map_one]
    · rw [h]
      decide
    · rw [map_add, map_one, h]
      decide

instance finite_ringEquiv_F4 : Finite (F4 ≃+* F4) :=
  Finite.of_injective (fun φ : F4 ≃+* F4 => (φ : F4 → F4)) DFunLike.coe_injective

instance finite_mulAut_SU52 : Finite (MulAut SU52) :=
  Finite.of_injective (fun α : MulAut SU52 => (α : SU52 → SU52)) DFunLike.coe_injective

theorem card_ringEquiv_F4 : Nat.card (F4 ≃+* F4) = 2 := by
  have e : (Set.univ : Set (F4 ≃+* F4)) = {1, barEquiv} := by
    ext φ
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    exact ringEquiv_eq_one_or_eq_barEquiv φ
  rw [← Set.ncard_univ, e, Set.ncard_pair barEquiv_ne_one.symm]

theorem fieldAut_barEquiv : fieldAut barEquiv = fld :=
  MulEquiv.ext fun g => ext_mat (by
    rw [mat_fieldAut, mat_fld]
    rfl)

theorem fieldFactor_fld : fieldFactor fld = barEquiv := by
  rw [← fieldAut_barEquiv, fieldFactor_fieldAut]

theorem exists_eq_conj_or_eq_conj_mul_fld (α : MulAut SU52) :
    ∃ s : SU52, α = MulAut.conj s ∨ α = MulAut.conj s * fld := by
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut α
  refine ⟨s, ?_⟩
  rcases ringEquiv_eq_one_or_eq_barEquiv (fieldFactor α) with h | h
  · left
    rw [hs, h, ← fieldHom_apply, map_one, mul_one]
  · right
    rw [hs, h, fieldAut_barEquiv]

theorem exists_eq_conj_mul_fld {α : MulAut SU52} (hα : fieldFactor α ≠ 1) :
    ∃ s : SU52, α = MulAut.conj s * fld := by
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut α
  rcases ringEquiv_eq_one_or_eq_barEquiv (fieldFactor α) with h | h
  · exact absurd h hα
  · exact ⟨s, by rw [hs, h, fieldAut_barEquiv]⟩

theorem card_mulAut_SU52 : Nat.card (MulAut SU52) = Nat.card SU52 * 2 := by
  rw [← Nat.card_congr autEquiv.toEquiv, SemidirectProduct.card, card_ringEquiv_F4]

section Ambient

variable {G : Type} [Group G] (L₀ : Subgroup G) (η : L₀ ≃* SU52)

@[expose] def act : normalizer (L₀ : Set G) →* MulAut SU52 :=
  (MulAut.congr η).toMonoidHom.comp L₀.normalizerMonoidHom

theorem coe_symm_act_apply (x : normalizer (L₀ : Set G)) (g : SU52) :
    ((η.symm (act L₀ η x g) : L₀) : G) = x * (η.symm g : G) * (x : G)⁻¹ := by
  simp [act, MulAut.congr_apply]

theorem act_eq_one_iff (x : normalizer (L₀ : Set G)) :
    act L₀ η x = 1 ↔ (x : G) ∈ centralizer (L₀ : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro y hy
    have h2 := coe_symm_act_apply L₀ η x (η ⟨y, hy⟩)
    rw [h1, MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
    change y = x * y * (x : G)⁻¹ at h2
    calc y * x = x * y * (x : G)⁻¹ * x := by rw [← h2]
      _ = x * y := by group
  · intro h1
    refine MulEquiv.ext fun g => η.symm.injective (Subtype.ext ?_)
    rw [coe_symm_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 h1 _ (η.symm g).2]
    group

theorem act_mem (l : L₀) : act L₀ η ⟨l, le_normalizer l.2⟩ = MulAut.conj (η l) := by
  refine MulEquiv.ext fun g => η.symm.injective (Subtype.ext ?_)
  rw [coe_symm_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

@[expose] def fieldFactorG : normalizer (L₀ : Set G) →* (F4 ≃+* F4) :=
  fieldFactor.comp (act L₀ η)

theorem exists_eq_mul_of_act_eq_conj (x : normalizer (L₀ : Set G)) (s : SU52)
    (hx : act L₀ η x = MulAut.conj s) :
    ∃ c ∈ centralizer (L₀ : Set G), (x : G) = (η.symm s : G) * c := by
  set l : L₀ := η.symm s with hl
  refine ⟨(l : G)⁻¹ * x, ?_, by group⟩
  have hmem : (l : G)⁻¹ * x ∈ normalizer (L₀ : Set G) :=
    mul_mem (inv_mem (le_normalizer l.2)) x.2
  have e : act L₀ η ⟨(l : G)⁻¹ * x, hmem⟩ = 1 := by
    have e1 : (⟨(l : G)⁻¹ * x, hmem⟩ : normalizer (L₀ : Set G)) =
        (⟨l, le_normalizer l.2⟩ : normalizer (L₀ : Set G))⁻¹ * x := Subtype.ext rfl
    rw [e1, map_mul, map_inv, act_mem, hl, MulEquiv.apply_symm_apply, hx, inv_mul_cancel]
  exact (act_eq_one_iff L₀ η _).mp e

theorem fieldFactorG_eq_one_iff (x : normalizer (L₀ : Set G)) :
    fieldFactorG L₀ η x = 1 ↔ ∃ l ∈ L₀, ∃ c ∈ centralizer (L₀ : Set G), (x : G) = l * c := by
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := (fieldFactor_eq_one_iff _).mp hx
    obtain ⟨c, hc, e⟩ := exists_eq_mul_of_act_eq_conj L₀ η x s hs
    exact ⟨_, (η.symm s).2, c, hc, e⟩
  · rintro ⟨l, hl, c, hc, hx⟩
    have hcN : c ∈ normalizer (L₀ : Set G) := Subgroup.centralizer_le_normalizer (L₀ : Set G) hc
    have e : x = (⟨l, le_normalizer hl⟩ : normalizer (L₀ : Set G)) * ⟨c, hcN⟩ := Subtype.ext hx
    have hc1 : act L₀ η ⟨c, hcN⟩ = 1 := (act_eq_one_iff L₀ η _).mpr hc
    rw [e, map_mul, fieldFactorG, MonoidHom.comp_apply, MonoidHom.comp_apply,
      show (⟨l, le_normalizer hl⟩ : normalizer (L₀ : Set G)) =
        ⟨((⟨l, hl⟩ : L₀) : G), le_normalizer (⟨l, hl⟩ : L₀).2⟩ from rfl, act_mem, hc1,
      map_one, fieldFactor_conj, one_mul]

end Ambient

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
