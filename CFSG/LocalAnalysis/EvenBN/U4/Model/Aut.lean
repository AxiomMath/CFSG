module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Gram

@[expose, reducible] def miyamotoJ4GL (K : Type) [Field K] : GL (Fin 4) K where
  val := miyamotoJ4 K
  inv := miyamotoJ4 K
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four]

@[simp] theorem coe_miyamotoJ4GL : ((miyamotoJ4GL K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    miyamotoJ4 K :=
  rfl

theorem isPrimeFormGram_miyamotoJ4GL : IsPrimeFormGram (miyamotoJ4GL K) where
  symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  prime i j := by
    fin_cases i <;> fin_cases j <;> simp [miyamotoJ4]

end Gram

section Scalars

theorem eq_one_of_pow_four_eq_one [CharP K 2] {x : K} (hx : x ^ 4 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (x - 1) ^ 2 ^ 2 = x ^ 2 ^ 2 - 1 ^ 2 ^ 2 := sub_pow_char_pow x 1 2
  norm_num at h1
  rw [hx, sub_self] at h1
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)

theorem normOneScalars_miyamoto_eq_bot :
    normOneScalars h (gramSU h (miyamotoJ4 K)) 4 = ⊥ := by
  have : CharP K 2 := h.charP
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  obtain ⟨c, -, hc4, hg⟩ := hg
  have hc : c = 1 := Units.ext (eq_one_of_pow_four_eq_one (by
    rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]))
  apply Subtype.ext
  rw [hg, hc, map_one]
  rfl

@[expose] def miyamotoProjEquiv : gramSU h (miyamotoJ4 K) ≃* primeFormP h (miyamotoJ4 K) :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (normOneScalars_miyamoto_eq_bot h).symm)

theorem miyamotoProjEquiv_apply (g : gramSU h (miyamotoJ4 K)) :
    miyamotoProjEquiv h g = (g : primeFormP h (miyamotoJ4 K)) :=
  rfl

theorem miyamotoProjEquiv_symm_mk (g : gramSU h (miyamotoJ4 K)) :
    (miyamotoProjEquiv h).symm (g : primeFormP h (miyamotoJ4 K)) = g := by
  rw [← miyamotoProjEquiv_apply, MulEquiv.symm_apply_apply]

theorem mk_injective_miyamoto {g g' : gramSU h (miyamotoJ4 K)}
    (e : (g : primeFormP h (miyamotoJ4 K)) = g') : g = g' :=
  (miyamotoProjEquiv h).injective e

end Scalars

section Model

@[expose] def miyamotoFieldAut (φ : K ≃+* K) : MulAut (gramSU h (miyamotoJ4 K)) :=
  primeFormFieldSU h (C := miyamotoJ4GL K) (isPrimeFormGram_miyamotoJ4GL (K := K)) φ

@[simp] theorem coe_miyamotoFieldAut_apply (φ : K ≃+* K) (g : gramSU h (miyamotoJ4 K)) :
    ((miyamotoFieldAut h φ g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      glAut φ (g : GL (Fin 4) K) :=
  rfl

@[expose] def miyamotoFieldHom : (K ≃+* K) →* MulAut (gramSU h (miyamotoJ4 K)) where
  toFun := miyamotoFieldAut h
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_miyamotoFieldAut_apply, map_one]
    rfl)
  map_mul' φ ψ := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, coe_miyamotoFieldAut_apply, coe_miyamotoFieldAut_apply,
      coe_miyamotoFieldAut_apply, map_mul]
    rfl)

@[simp] theorem miyamotoFieldHom_apply (φ : K ≃+* K) :
    miyamotoFieldHom h φ = miyamotoFieldAut h φ :=
  rfl

theorem miyamotoFieldAut_mul_conj_mul_inv (φ : K ≃+* K) (s : gramSU h (miyamotoJ4 K)) :
    miyamotoFieldAut h φ * MulAut.conj s * (miyamotoFieldAut h φ)⁻¹ =
      MulAut.conj (miyamotoFieldAut h φ s) := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem congr_conj_mul_miyamotoFieldAut (s : gramSU h (miyamotoJ4 K)) (φ : K ≃+* K) :
    MulAut.congr (miyamotoProjEquiv h) (MulAut.conj s * miyamotoFieldAut h φ) =
      primeFormConjHom h (miyamotoJ4 K) ⟨s, s.2.1⟩ *
        primeFormFieldHom h (C := miyamotoJ4GL K) (isPrimeFormGram_miyamotoJ4GL (K := K)) φ := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, miyamotoProjEquiv_symm_mk,
    MulAut.mul_apply, MulAut.mul_apply, miyamotoProjEquiv_apply]
  change _ = primeFormConjHom h (miyamotoJ4 K) ⟨s, s.2.1⟩
    (primeFormFieldAut h (isPrimeFormGram_miyamotoJ4GL (K := K)) φ (g : primeFormP h _))
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

@[expose] def miyamotoFieldFactor : MulAut (gramSU h (miyamotoJ4 K)) →* (K ≃+* K) :=
  (primeFormFieldFactor h (C := miyamotoJ4GL K) (isPrimeFormGram_miyamotoJ4GL (K := K))
    (by norm_num) (fun e => absurd e.1 (by norm_num))).comp
      (MulAut.congr (miyamotoProjEquiv h)).toMonoidHom

theorem miyamotoFieldFactor_apply (α : MulAut (gramSU h (miyamotoJ4 K))) :
    miyamotoFieldFactor h α = primeFormFieldFactor h (C := miyamotoJ4GL K)
      (isPrimeFormGram_miyamotoJ4GL (K := K)) (by norm_num) (fun e => absurd e.1 (by norm_num))
      (MulAut.congr (miyamotoProjEquiv h) α) :=
  rfl

@[simp] theorem miyamotoFieldFactor_conj_mul (s : gramSU h (miyamotoJ4 K)) (φ : K ≃+* K) :
    miyamotoFieldFactor h (MulAut.conj s * miyamotoFieldAut h φ) = φ := by
  rw [miyamotoFieldFactor_apply, congr_conj_mul_miyamotoFieldAut, primeFormFieldFactor_apply]

@[simp] theorem miyamotoFieldFactor_fieldAut (φ : K ≃+* K) :
    miyamotoFieldFactor h (miyamotoFieldAut h φ) = φ := by
  simpa using miyamotoFieldFactor_conj_mul h 1 φ

@[simp] theorem miyamotoFieldFactor_conj (s : gramSU h (miyamotoJ4 K)) :
    miyamotoFieldFactor h (MulAut.conj s) = 1 := by
  have e := miyamotoFieldFactor_conj_mul h s 1
  rwa [← miyamotoFieldHom_apply, map_one, mul_one] at e

theorem exists_pow_four_eq_of_norm_eq_one {μ : K} (hμ : h.norm μ = 1) :
    ∃ l : K, l ^ 4 = μ ∧ h.norm l = 1 := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨ν, hν⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) ν
  have hl4 : l ^ 4 = μ := by rw [hν, hl]; ring
  refine ⟨l, hl4, eq_one_of_pow_four_eq_one ?_⟩
  have e : h.norm l ^ 4 = h.norm (l ^ 4) := by
    simp only [pow_succ, pow_zero, one_mul, norm_mul_eq]
  rw [e, hl4, hμ]

theorem det_scalar_four (c : K) : (Matrix.scalar (Fin 4) c).det = c ^ 4 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp

theorem exists_mem_gramSU_conj_eq {A : GL (Fin 4) K}
    (hA : A ∈ primeFormUnitary h (miyamotoJ4 K)) :
    ∃ s : gramSU h (miyamotoJ4 K), ∀ g : GL (Fin 4) K,
      A * g * A⁻¹ = s * g * (s : GL (Fin 4) K)⁻¹ := by
  obtain ⟨l, hl4, hlN⟩ := exists_pow_four_eq_of_norm_eq_one h
    (norm_det_eq_one h (miyamotoJ4GL K) hA)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl4
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hl4.symm
  set u : Kˣ := (Units.mk0 l hl0)⁻¹ with hu
  have huN : h.norm (u : K) = 1 := by
    rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv_eq h, hlN, inv_one]
  have hsU : GeneralLinearGroup.scalar (Fin 4) u * A ∈ primeFormUnitary h (miyamotoJ4 K) := by
    refine mul_mem ?_ hA
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, huN,
      one_smul]
  have hsdet : ((GeneralLinearGroup.scalar (Fin 4) u * A : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, det_scalar_four, ← hl4, hu,
      Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_pow, inv_mul_cancel₀ hl0, one_pow]
  refine ⟨⟨_, hsU, hsdet⟩, fun g => ?_⟩
  change A * g * A⁻¹ = GeneralLinearGroup.scalar (Fin 4) u * A * g *
    (GeneralLinearGroup.scalar (Fin 4) u * A)⁻¹
  have hc := (commute_scalar u (A * g * A⁻¹)).eq
  calc A * g * A⁻¹ = A * g * A⁻¹ * GeneralLinearGroup.scalar (Fin 4) u *
        (GeneralLinearGroup.scalar (Fin 4) u)⁻¹ := by group
    _ = _ := by rw [hc]; group

theorem exists_eq_conj_mul_fieldAut (α : MulAut (gramSU h (miyamotoJ4 K))) :
    ∃ s : gramSU h (miyamotoJ4 K),
      α = MulAut.conj s * miyamotoFieldAut h (miyamotoFieldFactor h α) := by
  set hC := isPrimeFormGram_miyamotoJ4GL (K := K)
  have hn : 3 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ 2 ^ f = 2) := fun e => absurd e.1 (by norm_num)
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq
    (MulAut.congr (miyamotoProjEquiv h) α)
  have hφ : miyamotoFieldFactor h α = φ := by
    rw [miyamotoFieldFactor_apply, ← hAφ, primeFormFieldFactor_psi]
  obtain ⟨s, hs⟩ := exists_mem_gramSU_conj_eq h A.2
  refine ⟨s, MulEquiv.ext fun g => mk_injective_miyamoto h ?_⟩
  rw [hφ]
  have e1 : ((α g : gramSU h (miyamotoJ4 K)) : primeFormP h (miyamotoJ4 K)) =
      MulAut.congr (miyamotoProjEquiv h) α (g : primeFormP h (miyamotoJ4 K)) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      miyamotoProjEquiv_symm_mk, miyamotoProjEquiv_apply]
  rw [e1, ← hAφ, primeFormPsi_apply, MulAut.mul_apply]
  change primeFormConjHom h (miyamotoJ4 K) A (primeFormFieldAut h hC φ (g : primeFormP h _)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin 4) K) * glAut φ (g : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ =
    s * glAut φ (g : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹
  exact hs _

theorem conj_eq_one_iff (s : gramSU h (miyamotoJ4 K)) : MulAut.conj s = 1 ↔ s = 1 := by
  refine ⟨fun hs => ?_, fun hs => by rw [hs, map_one]⟩
  have : CharP K 2 := h.charP
  set hC := isPrimeFormGram_miyamotoJ4GL (K := K)
  have h1 : primeFormPsi h hC ⟨⟨s, s.2.1⟩, 1⟩ = 1 := by
    have e := congr_conj_mul_miyamotoFieldAut h s 1
    rw [← miyamotoFieldHom_apply, map_one, mul_one, hs, map_one, map_one, mul_one] at e
    rw [primeFormPsi_apply, map_one, mul_one, ← e]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC (by norm_num) _).mp h1
  have hc1 : c = 1 := by
    refine Units.ext (eq_one_of_pow_four_eq_one ?_)
    have hdet := s.2.2
    change (((⟨s, s.2.1⟩ : primeFormUnitary h (miyamotoJ4 K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 at hdet
    rw [hc, GeneralLinearGroup.coe_scalar, det_scalar_four] at hdet
    exact hdet
  apply Subtype.ext
  change ((⟨s, s.2.1⟩ : primeFormUnitary h (miyamotoJ4 K)) : GL (Fin 4) K) = 1
  rw [hc, hc1, map_one]

theorem conj_inj {s t : gramSU h (miyamotoJ4 K)} : MulAut.conj s = MulAut.conj t ↔ s = t := by
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, conj_eq_one_iff, mul_inv_eq_one] at e
  exact e

theorem conj_mul_fieldAut_inj {s t : gramSU h (miyamotoJ4 K)} {φ ψ : K ≃+* K} :
    MulAut.conj s * miyamotoFieldAut h φ = MulAut.conj t * miyamotoFieldAut h ψ ↔
      s = t ∧ φ = ψ := by
  refine ⟨fun e => ?_, fun e => by rw [e.1, e.2]⟩
  have hφ : φ = ψ := by
    rw [← miyamotoFieldFactor_conj_mul h s φ, e, miyamotoFieldFactor_conj_mul]
  subst hφ
  exact ⟨(conj_inj h).mp (mul_right_cancel e), rfl⟩

theorem miyamotoFieldFactor_eq_one_iff (α : MulAut (gramSU h (miyamotoJ4 K))) :
    miyamotoFieldFactor h α = 1 ↔ ∃ s : gramSU h (miyamotoJ4 K), α = MulAut.conj s := by
  constructor
  · intro hα
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    rw [hα, ← miyamotoFieldHom_apply, map_one, mul_one] at hs
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    exact miyamotoFieldFactor_conj h s

theorem miyamotoFieldFactor_surjective : Function.Surjective (miyamotoFieldFactor h) :=
  fun φ => ⟨miyamotoFieldAut h φ, miyamotoFieldFactor_fieldAut h φ⟩

@[expose] def miyamotoPsi : gramSU h (miyamotoJ4 K) ⋊[miyamotoFieldHom h] (K ≃+* K) →*
    MulAut (gramSU h (miyamotoJ4 K)) :=
  SemidirectProduct.lift MulAut.conj (miyamotoFieldHom h) fun φ => MonoidHom.ext fun s => by
    change MulAut.conj (miyamotoFieldAut h φ s) =
      miyamotoFieldAut h φ * MulAut.conj s * (miyamotoFieldAut h φ)⁻¹
    rw [miyamotoFieldAut_mul_conj_mul_inv]

theorem miyamotoPsi_apply (s : gramSU h (miyamotoJ4 K)) (φ : K ≃+* K) :
    miyamotoPsi h ⟨s, φ⟩ = MulAut.conj s * miyamotoFieldAut h φ := by
  rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul, miyamotoPsi, SemidirectProduct.lift_inl,
    SemidirectProduct.lift_inr, miyamotoFieldHom_apply]

@[expose] def miyamotoAutEquiv : gramSU h (miyamotoJ4 K) ⋊[miyamotoFieldHom h] (K ≃+* K) ≃*
    MulAut (gramSU h (miyamotoJ4 K)) :=
  MulEquiv.ofBijective (miyamotoPsi h) ⟨fun x y e => by
    obtain ⟨s, φ⟩ := x
    obtain ⟨t, ψ⟩ := y
    rw [miyamotoPsi_apply, miyamotoPsi_apply, conj_mul_fieldAut_inj] at e
    rw [e.1, e.2], fun α => by
    obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h α
    exact ⟨⟨s, miyamotoFieldFactor h α⟩, by rw [miyamotoPsi_apply, ← hs]⟩⟩

theorem miyamotoAutEquiv_apply (s : gramSU h (miyamotoJ4 K)) (φ : K ≃+* K) :
    miyamotoAutEquiv h ⟨s, φ⟩ = MulAut.conj s * miyamotoFieldAut h φ :=
  miyamotoPsi_apply h s φ

include h in
theorem card_ringAut : Nat.card (K ≃+* K) = 2 * f := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (by have := h.one_le; omega) h.card
  exact hcard

theorem card_mulAut_miyamoto :
    Nat.card (MulAut (gramSU h (miyamotoJ4 K))) = Nat.card (gramSU h (miyamotoJ4 K)) * (2 * f) := by
  rw [← Nat.card_congr (miyamotoAutEquiv h).toEquiv, SemidirectProduct.card, card_ringAut h]

end Model

section Ambient

variable {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

@[expose] def miyamotoAct : normalizer (L : Set G) →* MulAut (gramSU h (miyamotoJ4 K)) :=
  (MulAut.congr η).toMonoidHom.comp L.normalizerMonoidHom

theorem coe_symm_miyamotoAct_apply (x : normalizer (L : Set G)) (g : gramSU h (miyamotoJ4 K)) :
    ((η.symm (miyamotoAct h L η x g) : L) : G) = x * (η.symm g : G) * (x : G)⁻¹ := by
  simp [miyamotoAct, MulAut.congr_apply]

theorem miyamotoAct_apply_eq (x : normalizer (L : Set G)) (l : L) :
    miyamotoAct h L η x (η l) = η ⟨x * l * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 l).mp l.2⟩ := by
  apply η.symm.injective
  apply Subtype.ext
  rw [coe_symm_miyamotoAct_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem miyamotoAct_eq_one_iff (x : normalizer (L : Set G)) :
    miyamotoAct h L η x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro y hy
    have h2 := coe_symm_miyamotoAct_apply h L η x (η ⟨y, hy⟩)
    rw [h1, MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
    change y = x * y * (x : G)⁻¹ at h2
    calc y * x = x * y * (x : G)⁻¹ * x := by rw [← h2]
      _ = x * y := by group
  · intro h1
    refine MulEquiv.ext fun g => η.symm.injective (Subtype.ext ?_)
    rw [coe_symm_miyamotoAct_apply, MulAut.one_apply, ← mem_centralizer_iff.1 h1 _ (η.symm g).2]
    group

theorem miyamotoAct_mem (l : L) :
    miyamotoAct h L η ⟨l, le_normalizer l.2⟩ = MulAut.conj (η l) := by
  refine MulEquiv.ext fun g => η.symm.injective (Subtype.ext ?_)
  rw [coe_symm_miyamotoAct_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

@[expose] def miyamotoFieldFactorG : normalizer (L : Set G) →* (K ≃+* K) :=
  (miyamotoFieldFactor h).comp (miyamotoAct h L η)

theorem exists_eq_mul_of_miyamotoAct_eq_conj (x : normalizer (L : Set G))
    (s : gramSU h (miyamotoJ4 K)) (hx : miyamotoAct h L η x = MulAut.conj s) :
    ∃ c ∈ centralizer (L : Set G), (x : G) = (η.symm s : G) * c := by
  set l : L := η.symm s with hl
  refine ⟨(l : G)⁻¹ * x, ?_, by group⟩
  have hmem : (l : G)⁻¹ * x ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (le_normalizer l.2)) x.2
  have e : miyamotoAct h L η ⟨(l : G)⁻¹ * x, hmem⟩ = 1 := by
    have e1 : (⟨(l : G)⁻¹ * x, hmem⟩ : normalizer (L : Set G)) =
        (⟨l, le_normalizer l.2⟩ : normalizer (L : Set G))⁻¹ * x := Subtype.ext rfl
    rw [e1, map_mul, map_inv, miyamotoAct_mem, hl, MulEquiv.apply_symm_apply, hx,
      inv_mul_cancel]
  exact (miyamotoAct_eq_one_iff h L η _).mp e

theorem miyamotoFieldFactorG_eq_one_iff (x : normalizer (L : Set G)) :
    miyamotoFieldFactorG h L η x = 1 ↔
      ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), (x : G) = l * c := by
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := (miyamotoFieldFactor_eq_one_iff h _).mp hx
    obtain ⟨c, hc, e⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η x s hs
    exact ⟨_, (η.symm s).2, c, hc, e⟩
  · rintro ⟨l, hl, c, hc, hx⟩
    have hcN : c ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hc
    have e : x = (⟨l, le_normalizer hl⟩ : normalizer (L : Set G)) * ⟨c, hcN⟩ := Subtype.ext hx
    have hc1 : miyamotoAct h L η ⟨c, hcN⟩ = 1 := (miyamotoAct_eq_one_iff h L η _).mpr hc
    rw [e, map_mul, miyamotoFieldFactorG, MonoidHom.comp_apply, MonoidHom.comp_apply,
      show (⟨l, le_normalizer hl⟩ : normalizer (L : Set G)) =
        ⟨((⟨l, hl⟩ : L) : G), le_normalizer (⟨l, hl⟩ : L).2⟩ from rfl, miyamotoAct_mem, hc1,
      map_one, miyamotoFieldFactor_conj, one_mul]

theorem miyamotoAct_apply_of_mem_centralizer {M : Subgroup (GL (Fin 4) K)}
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ centralizer (miyamotoPull h L η M : Set G))
    {g : gramSU h (miyamotoJ4 K)} (hg : (g : GL (Fin 4) K) ∈ M) :
    miyamotoAct h L η x g = g := by
  apply η.symm.injective
  apply Subtype.ext
  rw [coe_symm_miyamotoAct_apply]
  have hc := mem_centralizer_iff.mp hx _ ((symm_mem_miyamotoPull_iff h L η).mpr hg)
  rw [← hc]
  group

theorem miyamotoAct_mem_iff_of_mem_normalizer {M : Subgroup (GL (Fin 4) K)}
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ normalizer (miyamotoPull h L η M : Set G))
    (g : gramSU h (miyamotoJ4 K)) :
    ((miyamotoAct h L η x g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ M ↔
      (g : GL (Fin 4) K) ∈ M := by
  rw [← symm_mem_miyamotoPull_iff h L η, coe_symm_miyamotoAct_apply,
    ← symm_mem_miyamotoPull_iff h L η]
  exact (mem_normalizer_iff.mp hx _).symm

theorem miyamotoAct_mem_of_mem_normalizer {M : Subgroup (GL (Fin 4) K)}
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ normalizer (miyamotoPull h L η M : Set G))
    {g : gramSU h (miyamotoJ4 K)} (hg : (g : GL (Fin 4) K) ∈ M) :
    ((miyamotoAct h L η x g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ M := by
  rw [← symm_mem_miyamotoPull_iff h L η, coe_symm_miyamotoAct_apply]
  exact (mem_normalizer_iff.mp hx _).mp ((symm_mem_miyamotoPull_iff h L η).mpr hg)

end Ambient

end CFSG.LocalAnalysis.EvenBN.U4
