module

public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

universe u

namespace LinearTwistComplement

variable {E : Type*} [Group E] [Fintype E]

theorem linear_value_mem (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime]
    (τ : E →* ℂˣ) (g : E) : ((τ g : ℂˣ) : ℂ) ∈ localizedComplexIntegerRing ideal :=
  rootOfUnity_mem_localizedComplexIntegerRing ideal (Nat.card E) Nat.card_pos _
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one])

theorem residue_linear_value_ne_zero (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (τ : E →* ℂˣ) (g : E) :
    localizedComplexIntegerResidue ideal ⟨_, linear_value_mem ideal τ g⟩ ≠ 0 := by
  intro h0
  have hone : (⟨_, linear_value_mem ideal τ g⟩ : localizedComplexIntegerRing ideal) *
      ⟨_, linear_value_mem ideal τ g⁻¹⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  have h := congrArg (localizedComplexIntegerResidue ideal) hone
  rw [map_mul, h0, zero_mul, map_one] at h
  exact zero_ne_one h

theorem localCentralCharacterHom_twist (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (τ : E →* ℂˣ) (χ ψ : basis.index)
    (hψ : ∀ w, (basis.representation ψ).character w = τ w * (basis.representation χ).character w)
    (K : ConjClasses E) :
    localCentralCharacterHom basis ideal ψ
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) =
      ⟨_, linear_value_mem ideal τ (conjugacyClassRepresentative K)⟩ *
        localCentralCharacterHom basis ideal χ
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) := by
  have hclass : ∀ g c : E, IsConj g c → (τ g : ℂ) = τ c := fun g c hgc => by
    obtain ⟨x, rfl⟩ := isConj_iff.mp hgc
    rw [map_mul, map_mul, map_inv, mul_comm (τ x), mul_inv_cancel_right]
  apply Subtype.ext
  rw [Subring.coe_mul, localCentralCharacterHom_coe, localCentralCharacterHom_coe]
  change centralCharacterScalar basis (conjugacyClassSum K) ψ =
    (τ (conjugacyClassRepresentative K) : ℂ) * centralCharacterScalar basis (conjugacyClassSum K) χ
  rw [centralCharacterScalar_conjugacyClassSum, centralCharacterScalar_conjugacyClassSum,
    hψ 1, map_one, Units.val_one, one_mul, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs with hg
  · rw [hψ g, hclass g _ (ConjClasses.mk_eq_mk_iff_isConj.mp
      (hg.trans (conjugacyClassRepresentative_spec K).symm))]
  · rw [mul_zero]

theorem sameCoefficientBlock_twist_iff (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (τ : E →* ℂˣ)
    (χ ψ χ' ψ' : basis.index)
    (hχ' : ∀ w, (basis.representation χ').character w = τ w * (basis.representation χ).character w)
    (hψ' : ∀ w, (basis.representation ψ').character w =
      τ w * (basis.representation ψ).character w) :
    sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ ψ ↔
      sameCoefficientBlock basis (localizedComplexIntegerRing ideal) χ' ψ' := by
  rw [sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
    sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
  constructor
  · intro h
    apply centralCharacterResidueHom_eq_of_class_values
    intro K
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ' _) =
      localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ψ' _)
    rw [localCentralCharacterHom_twist basis ideal τ χ χ' hχ',
      localCentralCharacterHom_twist basis ideal τ ψ ψ' hψ', map_mul, map_mul]
    congr 1
    exact congrFun (congrArg DFunLike.coe h) _
  · intro h
    apply centralCharacterResidueHom_eq_of_class_values
    intro K
    have hK := congrFun (congrArg DFunLike.coe h)
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K)
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ' _) =
      localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal ψ' _) at hK
    rw [localCentralCharacterHom_twist basis ideal τ χ χ' hχ',
      localCentralCharacterHom_twist basis ideal τ ψ ψ' hψ', map_mul, map_mul] at hK
    exact mul_left_cancel₀ (residue_linear_value_ne_zero ideal τ _) hK

theorem exists_twist_label (basis : FiniteIrreducibleCharacterBasis E) (τ : E →* ℂˣ)
    (χ : basis.index) :
    ∃ ψ : basis.index,
      ∀ w, (basis.representation ψ).character w = τ w * (basis.representation χ).character w := by
  obtain ⟨ψ, hψ⟩ := character_norm_one_basis_character basis
    (linearTwist τ (basis.representation χ))
    (by rw [linearTwist_characterPairing, characterPairing_irreducible _ _ (basis.irreducible χ)
      (basis.irreducible χ), ite_eq_left rfl])
  exact ⟨ψ, fun w => by rw [hψ, linearTwist_character]⟩

end LinearTwistComplement

open LinearTwistComplement

theorem linear_twist_permutes_blocks {E : Type*} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (τ : E →* ℂˣ) :
    ∃ σ : basis.index ≃ basis.index,
      (∀ χ w, (basis.representation (σ χ)).character w =
        τ w * (basis.representation χ).character w) ∧
      ∀ χ, (coefficientBlock basis (localizedComplexIntegerRing ideal) χ).map σ.toEmbedding =
        coefficientBlock basis (localizedComplexIntegerRing ideal) (σ χ) := by
  choose f hf using exists_twist_label basis τ
  choose g hg using exists_twist_label basis τ⁻¹
  have hcancel : ∀ w, (τ w : ℂ) * (τ⁻¹ w : ℂ) = 1 ∧ (τ⁻¹ w : ℂ) * (τ w : ℂ) = 1 :=
    fun w => by
      rw [MonoidHom.inv_apply, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
        inv_mul_cancel, Units.val_one]
      exact ⟨rfl, rfl⟩
  have hfg : ∀ χ, f (g χ) = χ := fun χ => basis.distinct (funext fun w => by
    change (basis.representation (f (g χ))).character w = (basis.representation χ).character w
    rw [hf, hg, ← mul_assoc, (hcancel w).1, one_mul])
  have hgf : ∀ χ, g (f χ) = χ := fun χ => basis.distinct (funext fun w => by
    change (basis.representation (g (f χ))).character w = (basis.representation χ).character w
    rw [hg, hf, ← mul_assoc, (hcancel w).2, one_mul])
  let σ : basis.index ≃ basis.index := ⟨f, g, hgf, hfg⟩
  refine ⟨σ, hf, fun χ => ?_⟩
  ext ψ'
  rw [Finset.mem_map_equiv, coefficientBlock_mem_iff, coefficientBlock_mem_iff]
  have hψ' : ∀ w, (basis.representation ψ').character w =
      τ w * (basis.representation (σ.symm ψ')).character w := fun w => by
    have h := hf (g ψ') w
    rw [hfg] at h
    exact h
  exact sameCoefficientBlock_twist_iff basis ideal τ χ (σ.symm ψ') (σ χ) ψ' (hf χ) hψ'

theorem linear_twist_prime_complement_block_and_class_functions {C : Type u} [Group C]
    [Fintype C] (basis : FiniteIrreducibleCharacterBasis C)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (R : Subgroup C) [R.Normal]
    (hR : Nat.Coprime p (Nat.card R)) (hquotient : IsPGroup p (C ⧸ R)) (ν : C →* ℂˣ)
    (ν₀ : basis.index) (hν₀ : ∀ c, (basis.representation ν₀).character c = ν c) :
    (∀ ψ : basis.index, ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀ ↔
      ∃ lam : FiniteComplexRepresentation.{u, u} (C ⧸ R), lam.IsIrreducible ∧
        ∀ c, (basis.representation ψ).character c = ν c * lam.character (QuotientGroup.mk' R c)) ∧
    (∀ lam : FiniteComplexRepresentation.{u, u} (C ⧸ R), lam.IsIrreducible →
      ∃ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀,
        ∀ c, (basis.representation ψ).character c = ν c * lam.character (QuotientGroup.mk' R c)) ∧
    (∀ f : C → ℂ, f ∈ coefficientCharacterSpace basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀) ↔
      ∃ F : C ⧸ R → ℂ, (∀ x y : C ⧸ R, F (y * x * y⁻¹) = F x) ∧
        ∀ c, f c = ν c * F (QuotientGroup.mk' R c)) := by
  obtain ⟨σ, hσ, hσblock⟩ := linear_twist_permutes_blocks basis ideal ν
  have hν0 : ∀ c, (ν c : ℂ) ≠ 0 := fun c => Units.ne_zero _
  set principal := σ.symm ν₀ with hprincipal_def
  have hprincipal : (basis.representation principal).character = 1 := by
    funext c
    have h := hσ principal c
    rw [hprincipal_def, Equiv.apply_symm_apply, hν₀] at h
    rw [Pi.one_apply]
    exact (mul_eq_left₀ (hν0 c)).mp h.symm
  have hblock : coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀ =
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).map σ.toEmbedding := by
    rw [hσblock, hprincipal_def, Equiv.apply_symm_apply]
  have hmem : ∀ ψ, ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀ ↔
      σ.symm ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro ψ
    rw [hblock, Finset.mem_map_equiv]
  have hsymm : ∀ ψ c, (basis.representation ψ).character c =
      ν c * (basis.representation (σ.symm ψ)).character c := fun ψ c => by
    have h := hσ (σ.symm ψ) c
    rwa [Equiv.apply_symm_apply] at h
  obtain ⟨-, hinfl, hexist⟩ := normal_p_complement_principal_block basis ideal p principal
    hprincipal R hR hquotient
  have hdesc : ∀ ψ : basis.index,
      ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀ ↔
      ∃ lam : FiniteComplexRepresentation.{u, u} (C ⧸ R), lam.IsIrreducible ∧
        ∀ c, (basis.representation ψ).character c =
          ν c * lam.character (QuotientGroup.mk' R c) := by
    intro ψ
    rw [hmem, hinfl]
    constructor
    · rintro ⟨lam, hirr, hlam⟩
      refine ⟨lam, hirr, fun c => ?_⟩
      rw [hsymm ψ c, hlam]
      rfl
    · rintro ⟨lam, hirr, hlam⟩
      refine ⟨lam, hirr, funext fun c => ?_⟩
      have h := hlam c
      rw [hsymm ψ c] at h
      exact mul_left_cancel₀ (hν0 c) h
  have hexists : ∀ lam : FiniteComplexRepresentation.{u, u} (C ⧸ R), lam.IsIrreducible →
      ∃ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) ν₀,
        ∀ c, (basis.representation ψ).character c =
          ν c * lam.character (QuotientGroup.mk' R c) := by
    intro lam hirr
    obtain ⟨x, hx, hxlam⟩ := hexist lam hirr
    refine ⟨σ x, ?_, fun c => ?_⟩
    · rw [hmem, Equiv.symm_apply_apply]
      exact hx
    · rw [hσ x c, hxlam]
      rfl
  refine ⟨hdesc, hexists, fun f => ⟨fun hf => ?_, ?_⟩⟩
  · induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, rfl⟩ := hg
      obtain ⟨lam, -, hlam⟩ := (hdesc ψ).mp hψ
      exact ⟨lam.character, fun x y => Representation.char_conj _ x y, hlam⟩
    | zero => exact ⟨0, fun _ _ => rfl, fun c => by simp⟩
    | add g₁ g₂ _ _ h₁ h₂ =>
      obtain ⟨F₁, hF₁, hg₁⟩ := h₁
      obtain ⟨F₂, hF₂, hg₂⟩ := h₂
      exact ⟨F₁ + F₂, fun x y => by simp only [Pi.add_apply, hF₁, hF₂],
        fun c => by simp only [Pi.add_apply, hg₁, hg₂, mul_add]⟩
    | smul a g _ h =>
      obtain ⟨F, hF, hg⟩ := h
      exact ⟨a • F, fun x y => by simp only [Pi.smul_apply, hF],
        fun c => by simp only [Pi.smul_apply, smul_eq_mul, hg]; ring⟩
  · rintro ⟨F, hF, hf⟩
    obtain ⟨quotientBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C ⧸ R)
    choose ψ hψ hψval using fun lam : quotientBasis.index =>
      hexists (quotientBasis.representation lam) (quotientBasis.irreducible lam)
    have hexp : f = ∑ lam : quotientBasis.index,
        characterPairing F (quotientBasis.representation lam).character •
          (basis.representation (ψ lam)).character := by
      funext c
      rw [hf c, finiteIrreducibleCharacterBasis_reconstruction quotientBasis F
        (fun x y => hF x y) (QuotientGroup.mk' R c), Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hψval lam c]
      ring
    rw [hexp]
    exact Submodule.sum_mem _ fun lam _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ψ lam, hψ lam, rfl⟩)

end CFSG.Semidihedral.Principal
