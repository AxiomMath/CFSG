module

public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Universal.IrreducibleQuadratic

public section

namespace CFSG.LieType.Catalog

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem card_galoisField (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (GaloisField p f) = p ^ f :=
  GaloisField.card p f (by omega)

theorem card_galoisField_mul (p f m : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hm : 1 ≤ m) :
    Nat.card (GaloisField p (m * f)) = (p ^ f) ^ m := by
  rw [GaloisField.card p (m * f) (Nat.mul_ne_zero (by omega) (by omega)), ← pow_mul, mul_comm]

theorem fam_classical_parameter_existence (t : StatedLieTag) (ht : t ∈ classicalTags)
    (n p f : ℕ) (hadm : StatedLieAdmissible t n p f) :
    ∃ (G : Type) (_ : Group G), StatedClassicalModel G t n p f := by
  have : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    exact ⟨StatedProj (StatedSL n (GaloisField p f)), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | PSU =>
    exact ⟨StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))), inferInstance, hadm,
      GaloisField p (2 * f), inferInstance, inferInstance, card_galoisField_mul p f 2 hf (by norm_num),
      ⟨MulEquiv.refl _⟩⟩
  | PSp =>
    exact ⟨StatedProj (StatedSp n (GaloisField p f)), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | POmegaOdd =>
    exact ⟨StatedProj (StatedOmega (StatedQuadOdd n (GaloisField p f))), inferInstance, hadm,
      GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | POmegaPlus =>
    exact ⟨StatedProj (StatedOmega (StatedQuadPlus n (GaloisField p f))), inferInstance, hadm,
      GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | POmegaMinus =>
    obtain ⟨b, c, hbc⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic (GaloisField p f)
    exact ⟨StatedProj (StatedOmega (StatedQuadMinus n (GaloisField p f) b c)), inferInstance,
      hadm, GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf, b, c, hbc,
      ⟨MulEquiv.refl _⟩⟩
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    simp [classicalTags] at ht

theorem iterateFrobenius_galoisField_apply (p m f : ℕ) [Fact p.Prime] (c : GaloisField p m) :
    iterateFrobenius (GaloisField p m) p f c = c ^ p ^ f :=
  rfl

theorem fam_chevalley_parameter_existence (t : StatedLieTag) (ht : t ∈ chevalleyExceptionalTags)
    (p f : ℕ) (hadm : StatedLieAdmissible t 0 p f) :
    ∃ (G : Type) (_ : Group G), ChevalleyExceptionalModel G t p f := by
  have : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | G2 =>
    exact ⟨AdjointQuotient .G2 (GaloisField p f), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | F4 =>
    exact ⟨AdjointQuotient .F4 (GaloisField p f), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | E6 =>
    exact ⟨AdjointQuotient .E6 (GaloisField p f), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | E7 =>
    exact ⟨AdjointQuotient .E7 (GaloisField p f), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | E8 =>
    exact ⟨AdjointQuotient .E8 (GaloisField p f), inferInstance, hadm, GaloisField p f,
      inferInstance, inferInstance, card_galoisField p f hf, ⟨MulEquiv.refl _⟩⟩
  | twistedE6 =>
    exact ⟨DerivedCentralQuotient (twistedFixedGroup .E6 (GaloisField p (2 * f))
        (iterateFrobenius (GaloisField p (2 * f)) p f)), inferInstance, hadm,
      GaloisField p (2 * f), inferInstance, inferInstance,
      card_galoisField_mul p f 2 hf (by norm_num), iterateFrobenius _ p f,
      iterateFrobenius_galoisField_apply p (2 * f) f, ⟨MulEquiv.refl _⟩⟩
  | trialityD4 =>
    exact ⟨DerivedCentralQuotient (twistedFixedGroup .D4 (GaloisField p (3 * f))
        (iterateFrobenius (GaloisField p (3 * f)) p f)), inferInstance, hadm,
      GaloisField p (3 * f), inferInstance, inferInstance,
      card_galoisField_mul p f 3 hf (by norm_num), iterateFrobenius _ p f,
      iterateFrobenius_galoisField_apply p (3 * f) f, ⟨MulEquiv.refl _⟩⟩
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | twistedB2 | twistedG2 | twistedF4
    | Tits => simp [chevalleyExceptionalTags] at ht

theorem fam_ree_tits_parameter_existence (t : StatedLieTag) (ht : t ∈ reeTitsTags) (p f : ℕ)
    (hadm : StatedLieAdmissible t 0 p f) :
    ∃ (G : Type) (_ : Group G), ReeTitsModel G t p f := by
  have : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | twistedG2 =>
    obtain ⟨a, ha⟩ := hadm.2.2.2.2.1
    exact ⟨DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField p f) reeG2Perm
        fun i => if i ∈ reeG2Long then p ^ a else p ^ (a + 1)), inferInstance, hadm, a, ha,
      GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf,
      ⟨MulEquiv.refl _⟩⟩
  | twistedF4 =>
    obtain ⟨a, ha⟩ := hadm.2.2.2.2.1
    exact ⟨DerivedCentralQuotient (reeFixedGroup .F4 (GaloisField p f) reeF4Perm
        fun i => if i ∈ reeF4Long then p ^ a else p ^ (a + 1)), inferInstance, hadm, a, ha,
      GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf,
      ⟨MulEquiv.refl _⟩⟩
  | Tits =>
    have h1 : f = 2 * 0 + 1 := hadm.2.2.2.2
    exact ⟨DerivedCentralQuotient (reeFixedGroup .F4 (GaloisField p f) reeF4Perm
        fun i => if i ∈ reeF4Long then p ^ 0 else p ^ (0 + 1)), inferInstance, hadm, 0, h1,
      GaloisField p f, inferInstance, inferInstance, card_galoisField p f hf,
      ⟨MulEquiv.refl _⟩⟩
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | G2 | F4 | E6 | E7 | E8
    | twistedE6 | trialityD4 | twistedB2 => simp [reeTitsTags] at ht

theorem fam_suzuki_parameter_existence (p f : ℕ) (hadm : StatedLieAdmissible .twistedB2 0 p f) :
    ∃ (G : Type) (_ : Group G), SuzukiModel G p f := by
  obtain ⟨-, -, -, rfl, ⟨a, rfl⟩, h3⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨suzukiGroup a (GaloisField 2 (2 * a + 1)), inferInstance, rfl, a, by omega,
    GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
    card_galoisField 2 (2 * a + 1) (by omega), ⟨MulEquiv.refl _⟩⟩

theorem cat_lie_parameter_existence (t : StatedLieTag) (n p f : ℕ)
    (hadm : StatedLieAdmissible t n p f) : ∃ (G : Type) (_ : Group G), LieModel G t n p f := by
  cases t with
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus =>
    obtain ⟨G, _, h⟩ := fam_classical_parameter_existence _ (by decide) n p f hadm
    exact ⟨G, inferInstance, .inl ⟨by decide, h⟩⟩
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    obtain ⟨G, _, h⟩ := fam_chevalley_parameter_existence _ (by decide) p f hadm
    exact ⟨G, inferInstance, .inr (.inl ⟨rfl, by decide, h⟩)⟩
  | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    obtain ⟨G, _, h⟩ := fam_chevalley_parameter_existence _ (by decide) p f hadm
    exact ⟨G, inferInstance, .inr (.inl ⟨rfl, by decide, h⟩)⟩
  | twistedG2 | twistedF4 | Tits =>
    obtain rfl : n = 0 := hadm.2.2.1
    obtain ⟨G, _, h⟩ := fam_ree_tits_parameter_existence _ (by decide) p f hadm
    exact ⟨G, inferInstance, .inr (.inr (.inl ⟨rfl, by decide, h⟩))⟩
  | twistedB2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    obtain ⟨G, _, h⟩ := fam_suzuki_parameter_existence p f hadm
    exact ⟨G, inferInstance, .inr (.inr (.inr ⟨rfl, rfl, h⟩))⟩

end CFSG.LieType.Catalog
