module

public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockOrderFormula
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.LinearLocalTwistMoment

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour
open CFSG.Semidihedral.Principal
open CFSG.RankTwoShapes

universe u

variable {A : Type u} [Group A] [Fintype A]

theorem exists_linearTwist_equiv (basis : FiniteIrreducibleCharacterBasis A)
    (lam : A →* ℂˣ) :
    ∃ σ : basis.index ≃ basis.index, ∀ θ x,
      (basis.representation (σ θ)).character x =
        (lam x : ℂ) * (basis.representation θ).character x := by
  have htwist (lam' : A →* ℂˣ) (θ : basis.index) :
      ∃ θ' : basis.index, ∀ x,
        (basis.representation θ').character x =
          (lam' x : ℂ) * (basis.representation θ).character x := by
    obtain ⟨θ', hθ'⟩ := character_norm_one_basis_character basis
      (linearTwist lam' (basis.representation θ))
      (by rw [linearTwist_characterPairing, characterPairing_irreducible _ _
        (basis.irreducible θ) (basis.irreducible θ), ite_eq_left rfl])
    exact ⟨θ', fun x => by rw [hθ', linearTwist_character]⟩
  choose f hf using htwist lam
  choose g hg using htwist lam⁻¹
  have hcancel : ∀ x, (lam x : ℂ) * (lam⁻¹ x : ℂ) = 1 ∧
      (lam⁻¹ x : ℂ) * (lam x : ℂ) = 1 := fun x => by
    rw [MonoidHom.inv_apply, ← Units.val_mul, ← Units.val_mul,
      mul_inv_cancel, inv_mul_cancel, Units.val_one]
    exact ⟨rfl, rfl⟩
  have hfg : ∀ θ, f (g θ) = θ := fun θ => basis.distinct (funext fun x => by
    change (basis.representation (f (g θ))).character x = (basis.representation θ).character x
    rw [hf, hg, ← mul_assoc, (hcancel x).1, one_mul])
  have hgf : ∀ θ, g (f θ) = θ := fun θ => basis.distinct (funext fun x => by
    change (basis.representation (g (f θ))).character x = (basis.representation θ).character x
    rw [hg, hf, ← mul_assoc, (hcancel x).2, one_mul])
  exact ⟨⟨f, g, hgf, hfg⟩, hf⟩

@[expose] noncomputable def linearTwistLabelEquiv (basis : FiniteIrreducibleCharacterBasis A)
    (lam : A →* ℂˣ) : basis.index ≃ basis.index :=
  (exists_linearTwist_equiv basis lam).choose

theorem linearTwistLabelEquiv_character (basis : FiniteIrreducibleCharacterBasis A)
    (lam : A →* ℂˣ) (θ : basis.index) (x : A) :
    (basis.representation (linearTwistLabelEquiv basis lam θ)).character x =
      (lam x : ℂ) * (basis.representation θ).character x :=
  (exists_linearTwist_equiv basis lam).choose_spec θ x

theorem linearTwistLabelEquiv_degree (basis : FiniteIrreducibleCharacterBasis A)
    (lam : A →* ℂˣ) (θ : basis.index) :
    (basis.representation (linearTwistLabelEquiv basis lam θ)).character 1 =
      (basis.representation θ).character 1 := by
  rw [linearTwistLabelEquiv_character, map_one, Units.val_one, one_mul]

variable {G : Type u} [Group G] [Fintype G]

theorem classWeight_linearTwist (H : Subgroup G) (lam : H →* ℂˣ)
    (x : G) (hlam : ∀ t : H, IsConj (t : G) x → lam t = 1) (ψ : H → ℂ) :
    classWeight H (fun t => (lam t : ℂ) * ψ t) x = classWeight H ψ x := by
  unfold classWeight
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · change (lam t : ℂ) * ψ t = ψ t
    rw [hlam t ht, Units.val_one, one_mul]
  · rfl

theorem linearTwistLabelEquiv_classWeight (H : Subgroup G)
    (basis : FiniteIrreducibleCharacterBasis H) (lam : H →* ℂˣ)
    (x : G) (hlam : ∀ t : H, IsConj (t : G) x → lam t = 1) (θ : basis.index) :
    classWeight H (basis.representation (linearTwistLabelEquiv basis lam θ)).character x =
      classWeight H (basis.representation θ).character x := by
  rw [show (basis.representation (linearTwistLabelEquiv basis lam θ)).character =
    (fun t => (lam t : ℂ) * (basis.representation θ).character t) from
      funext (linearTwistLabelEquiv_character basis lam θ)]
  exact classWeight_linearTwist H lam x hlam _

theorem linearTwist_local_sum (H : Subgroup G) (basis : FiniteIrreducibleCharacterBasis H)
    (lam : H →* ℂˣ) (x : G) (xH : H) (hxH : (xH : G) = x)
    (hlam : ∀ t : H, IsConj (t : G) x → lam t = 1) (support : Finset basis.index) :
    (∑ θ ∈ support.image (linearTwistLabelEquiv basis lam),
      classWeight H (basis.representation θ).character x ^ 2 *
        (basis.representation θ).character xH / (basis.representation θ).character 1) =
      ∑ θ ∈ support, classWeight H (basis.representation θ).character x ^ 2 *
        (basis.representation θ).character xH / (basis.representation θ).character 1 := by
  rw [Finset.sum_image (fun a _ b _ h => (linearTwistLabelEquiv basis lam).injective h)]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [linearTwistLabelEquiv_classWeight H basis lam x hlam,
    linearTwistLabelEquiv_degree, linearTwistLabelEquiv_character,
    hlam xH (hxH ▸ IsConj.refl x), Units.val_one, one_mul]

theorem transported_centralCharacterResidueHom {A' : Type u} [Group A'] [Fintype A']
    (e : A ≃* A') (basis : FiniteIrreducibleCharacterBasis A')
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (θ : basis.index)
    (value : centralCoefficientSubring (G := A') (localizedComplexIntegerRing ideal)) :
    centralCharacterResidueHom (transportCharacterBasis e basis) ideal θ
        (centralCoefficientTransport _ e.symm value) =
      centralCharacterResidueHom basis ideal θ value := by
  have hscalar : localCentralCharacterHom (transportCharacterBasis e basis) ideal θ
      (centralCoefficientTransport _ e.symm value) =
        localCentralCharacterHom basis ideal θ value := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe, localCentralCharacterHom_coe]
    unfold centralCharacterScalar
    rw [Nat.card_congr e.toEquiv, transportCharacterBasis_character, map_one]
    congr 1
    have hcoeff : (fun c : A =>
        (centralCoefficientTransport (localizedComplexIntegerRing ideal) e.symm value).val.coeff
          c⁻¹) = (fun c : A => value.val.coeff (e c)⁻¹) := by
      funext c
      rw [centralCoefficientTransport_coeff, MulEquiv.symm_symm, map_inv]
    rw [hcoeff]
    congr 1
    change characterPairing (fun c : A => value.val.coeff (e c)⁻¹)
      (fun c : A => (basis.representation θ).character (e c)) = _
    exact characterPairing_mulEquiv e (fun c => value.val.coeff c⁻¹)
      (basis.representation θ).character
  exact congrArg (localizedComplexIntegerResidue ideal) hscalar

omit [Fintype G] in
theorem extendedCentralizer_involution_eq (x : G) (hx : x * x = 1) :
    extendedCentralizer x = Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  ext g
  rw [mem_extendedCentralizer, inv_eq_of_mul_eq_one_left hx, or_self,
    conj_eq_self_iff_mul_comm]
  constructor
  · intro h
    exact mem_centralizer_zpowers_of_commute (show Commute x g from h.symm)
  · intro h
    exact (commute_of_mem_centralizer_zpowers x ⟨g, h⟩).eq.symm

omit [Fintype G] in
theorem centralizerSelf_extendedCentralizer_le (x : G) (hx : x * x = 1) :
    extendedCentralizer ((centralizerSelf x :
      Subgroup.centralizer (Subgroup.zpowers x : Set G)) : G) ≤
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  change extendedCentralizer x ≤ _
  exact le_of_eq (extendedCentralizer_involution_eq x hx)

omit [Fintype G] in
theorem centralizerSelf_internal_centralizer_eq (x : G) :
    Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
      Set (Subgroup.centralizer (Subgroup.zpowers x : Set G))) = ⊤ := by
  ext t
  constructor
  · intro _
    trivial
  · intro _
    exact mem_centralizer_zpowers_of_commute (centralizerSelf_commute x t)

omit [Fintype G] in
theorem localCentralizerEquiv_centralizerSelf_apply (x : G) (hx : x * x = 1)
    (t : Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
      Set (Subgroup.centralizer (Subgroup.zpowers x : Set G)))) :
    localCentralizerEquiv (Subgroup.centralizer (Subgroup.zpowers x : Set G))
      (centralizerSelf x) (centralizerSelf_extendedCentralizer_le x hx) t = t.val :=
  Subtype.ext rfl

theorem self_brauer_coefficient_projection (x : G) (hx : x * x = 1) (ring : Subring ℂ)
    (value : centralCoefficientSubring
      (G := Subgroup.centralizer (Subgroup.zpowers x : Set G)) ring) :
    centralNormalizerCoefficientProjection ring (Subgroup.zpowers (centralizerSelf x))
      (Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
        Set (Subgroup.centralizer (Subgroup.zpowers x : Set G)))) le_rfl
      (Subgroup.centralizer_le_normalizer _) value =
      centralCoefficientTransport ring
        (localCentralizerEquiv (Subgroup.centralizer (Subgroup.zpowers x : Set G))
          (centralizerSelf x) (centralizerSelf_extendedCentralizer_le x hx)).symm value := by
  apply Subtype.ext
  ext t
  calc
    (centralNormalizerCoefficientProjection ring (Subgroup.zpowers (centralizerSelf x))
        (Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
          Set (Subgroup.centralizer (Subgroup.zpowers x : Set G)))) le_rfl
        (Subgroup.centralizer_le_normalizer _) value).val.coeff t =
        value.val.coeff t.val := by
      rw [centralNormalizerCoefficientProjection_coeff, ite_eq_left t.property]
    _ = _ := by
      have h := centralCoefficientTransport_coeff ring
        (localCentralizerEquiv (Subgroup.centralizer (Subgroup.zpowers x : Set G))
          (centralizerSelf x) (centralizerSelf_extendedCentralizer_le x hx)).symm value t
      exact h.symm

theorem self_brauer_residue_eq (x : G) (hx : x * x = 1)
    (basisN : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hgroupN : IsPGroup p (Subgroup.zpowers (centralizerSelf x))) (θ : basisN.index) :
    brauerNormalizerCharacterResidueHom ideal p (Subgroup.zpowers (centralizerSelf x)) hgroupN
      (Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
        Set (Subgroup.centralizer (Subgroup.zpowers x : Set G)))) le_rfl
      (Subgroup.centralizer_le_normalizer _)
      (transportCharacterBasis
        (localCentralizerEquiv (Subgroup.centralizer (Subgroup.zpowers x : Set G))
          (centralizerSelf x) (centralizerSelf_extendedCentralizer_le x hx)) basisN) θ =
      centralCharacterResidueHom basisN ideal θ := by
  apply RingHom.ext
  intro value
  change centralCharacterResidueHom (transportCharacterBasis _ basisN) ideal θ
    (centralNormalizerCoefficientProjection _ _ _ _ _ value) = _
  rw [self_brauer_coefficient_projection x hx]
  exact transported_centralCharacterResidueHom _ basisN ideal θ value

theorem centralizer_involution_block_moment_formula
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (x : G) (hxorder : orderOf x = 2)
    (basisN : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)))
    (block : basis.index) (localBlock : basisN.index)
    (hgroup : IsPGroup 2 (Subgroup.zpowers x))
    (hbrauer : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x) hgroup
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) basisN localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x) hgroup
        (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) basisN θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock) :
    (Nat.card G : ℂ) *
      (∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
        (basis.representation θ).character x ^ 3 / (basis.representation θ).character 1) =
      (Nat.card (Subgroup.centralizer (Subgroup.zpowers x : Set G)) : ℂ) ^ 3 *
        ∑ θ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock,
          classWeight (Subgroup.centralizer (Subgroup.zpowers x : Set G))
              (basisN.representation θ).character x ^ 2 *
            (basisN.representation θ).character (centralizerSelf x) /
              (basisN.representation θ).character 1 := by
  have hx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxorder, pow_two] at h
  have hgroupN : IsPGroup 2 (Subgroup.zpowers (centralizerSelf x)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    change orderOf x ∣ 2 ^ 1
    rw [hxorder, pow_one]
  have hbrauerN := self_brauer_residue_eq x hx basisN ideal 2 hgroupN localBlock
  have huniqueN : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (centralizerSelf x)) hgroupN
        (Subgroup.centralizer (Subgroup.zpowers (centralizerSelf x) :
          Set (Subgroup.centralizer (Subgroup.zpowers x : Set G)))) le_rfl
        (Subgroup.centralizer_le_normalizer _)
        (transportCharacterBasis
          (localCentralizerEquiv (Subgroup.centralizer (Subgroup.zpowers x : Set G))
            (centralizerSelf x) (centralizerSelf_extendedCentralizer_le x hx)) basisN) θ =
          centralCharacterResidueHom basisN ideal localBlock →
        θ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock := by
    intro θ hθ
    rw [self_brauer_residue_eq x hx basisN ideal 2 hgroupN θ] at hθ
    rw [coefficientBlock_mem_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    exact hθ.symm
  have hformula := (brauer_order_formula_with_unique_local_block basis ideal 2 hx hx
    (Subgroup.centralizer (Subgroup.zpowers x : Set G)) (centralizerSelf x) 1
    (by change orderOf x ∣ 2 ^ 1; rw [hxorder, pow_one])
    (centralizerSelf_extendedCentralizer_le x hx) basisN basisN block localBlock localBlock
    hgroup hgroupN hbrauer hunique hbrauerN huniqueN).1 1
      (Subgroup.one_mem _) (by simp)
  have hcentralizer : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => mem_centralizer_zpowers_of_commute (show Commute x g from h.symm),
      fun h => (commute_of_mem_centralizer_zpowers x ⟨g, h⟩).eq.symm⟩
  simp only [mul_one, hcentralizer] at hformula
  convert hformula using 1 <;> simp only [pow_three, pow_two, mul_assoc, centralizerSelf]

theorem exists_principalCharacterLabel (basis : FiniteIrreducibleCharacterBasis A) :
    ∃ θ : basis.index, (basis.representation θ).character = 1 := by
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation A) (principalFiniteComplexRepresentation_isIrreducible A)
  exact ⟨θ, hθ.trans (principalFiniteComplexRepresentation_character A)⟩

@[expose] noncomputable def principalCharacterLabel (basis : FiniteIrreducibleCharacterBasis A) : basis.index :=
  (exists_principalCharacterLabel basis).choose

theorem principalCharacterLabel_character (basis : FiniteIrreducibleCharacterBasis A) :
    (basis.representation (principalCharacterLabel basis)).character = 1 :=
  (exists_principalCharacterLabel basis).choose_spec

noncomputable abbrev principalCoefficientBlock (basis : FiniteIrreducibleCharacterBasis A)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] : Finset basis.index :=
  coefficientBlock basis (localizedComplexIntegerRing ideal) (principalCharacterLabel basis)

@[expose] noncomputable def linearTwistedBlock (basis : FiniteIrreducibleCharacterBasis A)
    (lam : A →* ℂˣ) (support : Finset basis.index) : Finset basis.index :=
  support.image (linearTwistLabelEquiv basis lam)

theorem mem_linearTwistedBlock (basis : FiniteIrreducibleCharacterBasis A) (lam : A →* ℂˣ)
    (support : Finset basis.index) (θ : basis.index) :
    θ ∈ linearTwistedBlock basis lam support ↔ ∃ θ₀ ∈ support,
      ∀ x, (basis.representation θ).character x =
        (lam x : ℂ) * (basis.representation θ₀).character x := by
  constructor
  · intro hθ
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hθ
    exact ⟨θ₀, hθ₀, linearTwistLabelEquiv_character basis lam θ₀⟩
  · rintro ⟨θ₀, hθ₀, hvalue⟩
    have heq : linearTwistLabelEquiv basis lam θ₀ = θ := basis.distinct (funext fun x => by
      change (basis.representation (linearTwistLabelEquiv basis lam θ₀)).character x =
        (basis.representation θ).character x
      rw [linearTwistLabelEquiv_character, hvalue])
    exact Finset.mem_image.mpr ⟨θ₀, hθ₀, heq⟩

omit [Fintype A] in
theorem linearCharacter_conj (lam : A →* ℂˣ) (t c : A) :
    lam (c * t * c⁻¹) = lam t := by
  rw [map_mul, map_mul, map_inv, mul_comm (lam c), mul_inv_cancel_right]

theorem linearCharacter_eq_one_of_sylow_trivial (H : Subgroup G) (lam : H →* ℂˣ)
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hS : ∀ s : H, (s : G) ∈ (S : Subgroup G) → lam s = 1)
    (t : H) (ht : t * t = 1) : lam t = 1 := by
  obtain ⟨c, hcH, hct⟩ := exists_conj_mem_sylow_of_le S hSH t.property
    ⟨1, by simp only [pow_one, pow_two, ← Subgroup.coe_mul, ht, Subgroup.coe_one]⟩
  let cH : H := ⟨c, hcH⟩
  have hvalue := hS (cH * t * cH⁻¹) hct
  rwa [linearCharacter_conj] at hvalue

theorem linearCharacter_class_condition_of_sylow_trivial (x : G) (hxorder : orderOf x = 2)
    (lam : (Subgroup.centralizer (Subgroup.zpowers x : Set G)) →* ℂˣ)
    (S : Sylow 2 G)
    (hSN : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hS : ∀ s : Subgroup.centralizer (Subgroup.zpowers x : Set G),
      (s : G) ∈ (S : Subgroup G) → lam s = 1) :
    ∀ t : Subgroup.centralizer (Subgroup.zpowers x : Set G),
      IsConj (t : G) x → lam t = 1 := by
  intro t htx
  apply linearCharacter_eq_one_of_sylow_trivial _ lam S hSN hS t
  have hx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hxorder, pow_two] at h
  exact classInter_mul_self _ hx t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htx⟩)

omit [Fintype A] in
theorem involution_zpowers_isPGroup (x : A) (hxorder : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_zpowers, hxorder, pow_one]

theorem linear_local_twist_preserves_involution_cubic_moment
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (x : G) (hxorder : orderOf x = 2)
    (basisN : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)))
    (block : basis.index) (localBlock : basisN.index)
    (lam : (Subgroup.centralizer (Subgroup.zpowers x : Set G)) →* ℂˣ)
    (hlam : ∀ t : Subgroup.centralizer (Subgroup.zpowers x : Set G),
      IsConj (t : G) x → lam t = 1)
    (htwisted : coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock =
      linearTwistedBlock basisN lam (principalCoefficientBlock basisN ideal))
    (hbrauerPrincipal : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
      (involution_zpowers_isPGroup x hxorder)
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) basisN (principalCharacterLabel basisN) =
        centralCharacterResidueHom basis ideal (principalCharacterLabel basis))
    (huniquePrincipal : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
        (involution_zpowers_isPGroup x hxorder)
        (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) basisN θ =
          centralCharacterResidueHom basis ideal (principalCharacterLabel basis) →
        θ ∈ principalCoefficientBlock basisN ideal)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
      (involution_zpowers_isPGroup x hxorder)
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) basisN localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
        (involution_zpowers_isPGroup x hxorder)
        (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) basisN θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock) :
    (∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
      (basis.representation θ).character x ^ 3 / (basis.representation θ).character 1) =
      ∑ θ ∈ principalCoefficientBlock basis ideal,
        (basis.representation θ).character x ^ 3 / (basis.representation θ).character 1 := by
  have hformula := centralizer_involution_block_moment_formula basis ideal x hxorder basisN
    block localBlock (involution_zpowers_isPGroup x hxorder) hbrauer hunique
  have hprincipal := centralizer_involution_block_moment_formula basis ideal x hxorder basisN
    (principalCharacterLabel basis) (principalCharacterLabel basisN)
    (involution_zpowers_isPGroup x hxorder) hbrauerPrincipal huniquePrincipal
  rw [htwisted] at hformula
  change (Nat.card G : ℂ) * _ = (Nat.card _ : ℂ) ^ 3 *
    ∑ θ ∈ (principalCoefficientBlock basisN ideal).image (linearTwistLabelEquiv basisN lam),
      classWeight (Subgroup.centralizer (Subgroup.zpowers x : Set G))
          (basisN.representation θ).character x ^ 2 *
        (basisN.representation θ).character (centralizerSelf x) /
          (basisN.representation θ).character 1 at hformula
  rw [linearTwist_local_sum _ basisN lam x (centralizerSelf x) rfl hlam] at hformula
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (hformula.trans hprincipal.symm)

theorem linear_local_twist_preserves_involution_cubic_moment_of_sylow_trivial
    (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (x : G) (hxorder : orderOf x = 2)
    (basisN : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)))
    (block : basis.index) (localBlock : basisN.index)
    (lam : (Subgroup.centralizer (Subgroup.zpowers x : Set G)) →* ℂˣ)
    (S : Sylow 2 G)
    (hSN : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hS : ∀ s : Subgroup.centralizer (Subgroup.zpowers x : Set G),
      (s : G) ∈ (S : Subgroup G) → lam s = 1)
    (htwisted : coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock =
      linearTwistedBlock basisN lam (principalCoefficientBlock basisN ideal))
    (hbrauerPrincipal : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
      (involution_zpowers_isPGroup x hxorder)
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) basisN (principalCharacterLabel basisN) =
        centralCharacterResidueHom basis ideal (principalCharacterLabel basis))
    (huniquePrincipal : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
        (involution_zpowers_isPGroup x hxorder)
        (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) basisN θ =
          centralCharacterResidueHom basis ideal (principalCharacterLabel basis) →
        θ ∈ principalCoefficientBlock basisN ideal)
    (hbrauer : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
      (involution_zpowers_isPGroup x hxorder)
      (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) basisN localBlock =
        centralCharacterResidueHom basis ideal block)
    (hunique : ∀ θ : basisN.index,
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers x)
        (involution_zpowers_isPGroup x hxorder)
        (Subgroup.centralizer (Subgroup.zpowers x : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) basisN θ =
          centralCharacterResidueHom basis ideal block →
        θ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) localBlock) :
    (∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) block,
      (basis.representation θ).character x ^ 3 / (basis.representation θ).character 1) =
      ∑ θ ∈ principalCoefficientBlock basis ideal,
        (basis.representation θ).character x ^ 3 / (basis.representation θ).character 1 :=
  linear_local_twist_preserves_involution_cubic_moment basis ideal x hxorder basisN block localBlock
    lam (linearCharacter_class_condition_of_sylow_trivial x hxorder lam S hSN hS)
    htwisted hbrauerPrincipal huniquePrincipal hbrauer hunique

end CFSG.Wreathed.LinearLocalTwistMoment
