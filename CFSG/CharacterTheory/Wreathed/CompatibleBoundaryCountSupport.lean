module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.TwoRankLowerBound.Helpers
open scoped Classical

universe u v

theorem normal_of_commutator_le {A : Type u} [Group A] {H : Subgroup A}
    (h : commutator A ≤ H) : H.Normal := by
  constructor
  intro x hx g
  have hc : g * x * g⁻¹ * x⁻¹ ∈ H := by
    apply h
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
  have := H.mul_mem hc hx
  simpa [mul_assoc] using this

theorem units_zpow_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun z : ℂˣ => z ^ n) := by
  have hnat : ∀ k : ℕ, k ≠ 0 → ∀ c : ℂˣ, ∃ z : ℂˣ, z ^ k = c := by
    intro k hk c
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) (Nat.pos_of_ne_zero hk)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact c.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  intro c
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · obtain ⟨z, hz⟩ := hnat k (by omega) c
    exact ⟨z, by simp only [zpow_natCast, hz]⟩
  · obtain ⟨z, hz⟩ := hnat k (by omega) c⁻¹
    exact ⟨z, by simp only [zpow_neg, zpow_natCast, hz, inv_inv]⟩

noncomputable instance : DivisibleBy (Additive ℂˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨z, hz⟩ := units_zpow_surjective hn (Additive.toMul y)
    have hz' : z ^ n = Additive.toMul y := hz
    exact ⟨Additive.ofMul z, by
      change Additive.ofMul (z ^ n) = y
      rw [hz']
      rfl⟩

theorem exists_hom_comp_eq {E : Type u} {Q : Type v} [Group E] [Group Q]
    [IsMulCommutative Q] (f : E →* Q) (μ : E →* ℂˣ) (hker : f.ker ≤ μ.ker) :
    ∃ ν : Q →* ℂˣ, ν.comp f = μ := by
  let : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => (IsMulCommutative.is_comm (M := Q)).comm a b }
  let μr : f.range →* ℂˣ := (QuotientGroup.lift f.ker μ hker).comp
    (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  have hμr : ∀ y : E, μr (f.rangeRestrict y) = μ y := by
    intro y
    change QuotientGroup.lift f.ker μ hker ((QuotientGroup.quotientKerEquivRange f).symm
      (f.rangeRestrict y)) = μ y
    rw [show (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict y) =
      (y : E ⧸ f.ker) from (QuotientGroup.quotientKerEquivRange f).symm_apply_eq.mpr rfl]
    rfl
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive f.range.subtype) Subtype.coe_injective (MonoidHom.toAdditive μr)
  refine ⟨MonoidHom.toAdditive.symm h, MonoidHom.ext fun y => ?_⟩
  have h' := DFunLike.congr_fun hh (Additive.ofMul (f.rangeRestrict y))
  change Additive.toMul (h (Additive.ofMul (f y))) = μ y
  rw [← hμr y]
  exact congrArg Additive.toMul h'

@[expose] def lineRep {A : Type u} [Group A] (μ : A →* ℂˣ) : Representation ℂ A ℂ where
  toFun g := (μ g : ℂ) • (1 : Module.End ℂ ℂ)
  map_one' := by simp
  map_mul' g g' := by
    simp only [map_mul, Units.val_mul, smul_mul_smul_comm, one_mul]

@[expose] def lineRepresentation {A : Type u} [Group A] (μ : A →* ℂˣ) :
    FiniteComplexRepresentation.{u, 0} A where
  vector := ℂ
  representation := lineRep μ

theorem lineRepresentation_character {A : Type u} [Group A] (μ : A →* ℂˣ) (g : A) :
    (lineRepresentation μ).character g = μ g := by
  change LinearMap.trace ℂ ℂ ((μ g : ℂ) • (1 : Module.End ℂ ℂ)) = _
  rw [map_smul, LinearMap.trace_one]
  simp

theorem lineRep_isIrreducible {A : Type u} [Group A] (μ : A →* ℂˣ) :
    (lineRep μ).IsIrreducible := by
  change IsSimpleOrder (Subrepresentation (lineRep μ))
  have hnontrivial : (⊥ : Subrepresentation (lineRep μ)) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊥ : Subrepresentation (lineRep μ)) := by
      rw [hequal]
      trivial
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation (lineRep μ)) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  obtain hbot | htop := eq_bot_or_eq_top W.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

theorem lineRepresentation_isIrreducible {A : Type u} [Group A] (μ : A →* ℂˣ) :
    (lineRepresentation μ).IsIrreducible :=
  lineRep_isIrreducible μ

theorem exists_hom_of_finrank_one {A : Type u} [Group A] (data : FiniteComplexRepresentation A)
    (h : Module.finrank ℂ data.vector = 1) :
    ∃ μ : A →* ℂˣ, ∀ g, (μ g : ℂ) = data.character g := by
  have hsmul : ∀ g : A, data.representation g =
      data.character g • (LinearMap.id : data.vector →ₗ[ℂ] data.vector) := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h
      (data.representation g)
    have htrace : data.character g = c := by
      change LinearMap.trace ℂ _ (data.representation g) = c
      rw [hc, map_smul, LinearMap.trace_id, h, Nat.cast_one, smul_eq_mul, mul_one]
    rw [hc, htrace]
  let f : A →* ℂ :=
    { toFun := data.character
      map_one' := by
        rw [FiniteComplexRepresentation.character, Representation.char_one, h, Nat.cast_one]
      map_mul' := fun x y => by
        change LinearMap.trace ℂ _ (data.representation (x * y)) =
          LinearMap.trace ℂ _ (data.representation x) *
            LinearMap.trace ℂ _ (data.representation y)
        rw [map_mul, Module.End.mul_eq_comp]
        change LinearMap.trace ℂ _ ((data.representation x).comp (data.representation y)) =
          data.character x * data.character y
        rw [hsmul x, hsmul y, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
          smul_smul, map_smul, LinearMap.trace_id, h, Nat.cast_one, smul_eq_mul, mul_one] }
  exact ⟨f.toHomUnits, fun g => rfl⟩

theorem exists_hom_of_isMulCommutative {A : Type u} [Group A] [Fintype A] [IsMulCommutative A]
    (qb : FiniteIrreducibleCharacterBasis A) (φ : qb.index) :
    ∃ μ : A →* ℂˣ, ∀ g, (μ g : ℂ) = (qb.representation φ).character g := by
  let : (qb.representation φ).representation.IsIrreducible := qb.irreducible φ
  exact exists_hom_of_finrank_one _
    (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      (qb.representation φ).representation)

theorem card_index_of_isMulCommutative {A : Type u} [Group A] [Fintype A] [IsMulCommutative A]
    (qb : FiniteIrreducibleCharacterBasis A) : Fintype.card qb.index = Nat.card A := by
  have hdeg : ∀ φ, (qb.representation φ).character 1 = 1 := by
    intro φ
    let : (qb.representation φ).representation.IsIrreducible := qb.irreducible φ
    rw [FiniteComplexRepresentation.character, Representation.char_one,
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (qb.representation φ).representation]
    simp
  set f : A → ℂ := fun y => if y = 1 then (Nat.card A : ℂ) else 0 with hf
  have hclass : ∀ g c : A, f (c * g * c⁻¹) = f g := by
    intro g c
    simp only [hf]
    congr 1
    apply propext
    constructor
    · intro h
      have := congrArg (fun z => c⁻¹ * z * c) h
      simpa [mul_assoc] using this
    · rintro rfl
      simp
  have hrec := finiteIrreducibleCharacterBasis_reconstruction qb f hclass 1
  have hpair : ∀ φ, characterPairing f (qb.representation φ).character = 1 := by
    intro φ
    unfold characterPairing
    rw [Finset.sum_eq_single 1]
    · simp only [hf, ↓reduceIte, inv_one, hdeg, mul_one]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    · intro y _ hy
      simp [hf, hy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsum : ∑ φ, characterPairing f (qb.representation φ).character *
      (qb.representation φ).character 1 = (Fintype.card qb.index : ℂ) := by
    rw [Finset.sum_congr rfl (fun φ _ => by rw [hpair φ, hdeg φ, one_mul])]
    simp
  have hf1 : f 1 = (Nat.card A : ℂ) := by simp [hf]
  rw [hsum, hf1] at hrec
  exact_mod_cast hrec.symm

end CFSG.Wreathed.CompatibleFamilies
