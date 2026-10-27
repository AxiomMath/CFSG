module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.PrimaryValues
public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.DegreeTwelve

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField CFSG.TwoRankLowerBound.Helpers

theorem card_sylow_eq_of_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) (Q : Sylow p H) : Nat.card Q = Nat.card H := by
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hH
  rw [Q.card_eq_multiplicity, hr, Nat.Prime.factorization_pow (Fact.out),
    Finsupp.single_eq_same]

variable {G : Type} [Group G] [Finite G]

theorem sylow_card_dvd_of_faithful_cyclotomic_character
    (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation) {m : ℕ} (hm : 0 < m) {ξ : ℂ}
    (hξ : ξ ^ m = 1) (hχ : ∀ g, data.character g ∈ ℚ⟮ξ⟯) {p : ℕ} [hp : Fact p.Prime]
    (hpm : ¬ p ∣ m) (P : Sylow p G) :
    Nat.card P ∣ p ^ (Module.finrank ℂ data.vector / (p - 1)) *
      (Module.finrank ℂ data.vector / (p - 1)).factorial := by
  set H : Subgroup G := (P : Subgroup G)
  let data' : FiniteComplexRepresentation.{0, 0} H :=
    inflatedFiniteComplexRepresentation H.subtype data
  have hfaithful' : Function.Injective data'.representation :=
    hfaithful.comp Subtype.val_injective
  have hrational' : ∀ y, ∃ q : ℚ, data'.character y = q := by
    intro y
    obtain ⟨e, he⟩ := P.isPGroup' y
    have hy : (y : G) ^ p ^ e = 1 := by rw [← Subgroup.coe_pow, he, Subgroup.coe_one]
    exact character_rat_of_pow_prime_pow data.representation hm hξ hp.out hpm hy (hχ y)
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p H))
  have h := sylow_card_dvd_of_faithful_rational_character data' hfaithful' hrational' Q
  rw [card_sylow_eq_of_isPGroup P.isPGroup' Q] at h
  exact h

theorem factorization_le_of_faithful_cyclotomic_character
    (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation) {m : ℕ} (hm : 0 < m) {ξ : ℂ}
    (hξ : ξ ^ m = 1) (hχ : ∀ g, data.character g ∈ ℚ⟮ξ⟯) {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) :
    (Nat.card G).factorization p ≤ Module.finrank ℂ data.vector / (p - 1) +
      (Module.finrank ℂ data.vector / (p - 1)).factorial.factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcard := sylow_card_dvd_of_faithful_cyclotomic_character data hfaithful hm hξ hχ hpm P
  rw [P.card_eq_multiplicity] at hcard
  have hne : p ^ (Module.finrank ℂ data.vector / (p - 1)) *
      (Module.finrank ℂ data.vector / (p - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero _)
  have := (hp.pow_dvd_iff_le_factorization hne).mp hcard
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero _),
    Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
  exact this

theorem prime_le_of_faithful_cyclotomic_character (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation) {m : ℕ} (hm : 0 < m) {ξ : ℂ}
    (hξ : ξ ^ m = 1) (hχ : ∀ g, data.character g ∈ ℚ⟮ξ⟯) {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hdvd : p ∣ Nat.card G) : p ≤ Module.finrank ℂ data.vector + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcard := sylow_card_dvd_of_faithful_cyclotomic_character data hfaithful hm hξ hχ hpm P
  have hpP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  by_contra hlt
  have hr : Module.finrank ℂ data.vector / (p - 1) = 0 := by
    apply Nat.div_eq_of_lt
    omega
  rw [hr, pow_zero, Nat.factorial_zero, mul_one, Nat.dvd_one] at hcard
  rw [hcard] at hpP
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpP)

theorem prime_le_of_faithful_character_pow_five (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation) {ξ : ℂ} (hξ : ξ ^ 5 = 1)
    (hχ : ∀ g, data.character g ∈ ℚ⟮ξ⟯) (hn : 4 ≤ Module.finrank ℂ data.vector) {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G) : p ≤ Module.finrank ℂ data.vector + 1 := by
  by_cases hp5 : p = 5
  · omega
  · have hpm : ¬ p ∣ 5 := fun h =>
      hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    exact prime_le_of_faithful_cyclotomic_character data hfaithful (by norm_num) hξ hχ hp hpm
      hdvd

theorem prime_le_of_faithful_cyclotomic_five_character
    (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hχ : ∀ g, data.character g ∈ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / 5)⟯)
    (hn : 4 ≤ Module.finrank ℂ data.vector) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    p ≤ Module.finrank ℂ data.vector + 1 := by
  have hξ : Complex.exp (2 * Real.pi * Complex.I / 5) ^ 5 = 1 := by
    simpa using (Complex.isPrimitiveRoot_exp 5 (by norm_num)).pow_eq_one
  exact prime_le_of_faithful_character_pow_five data hfaithful hξ hχ hn hp hdvd

theorem prime_le_of_simple_cyclotomic_five_character [Fintype G] [IsSimpleGroup G]
    (basis : FiniteIrreducibleCharacterBasis G) (label : basis.index)
    (hn : 4 ≤ Module.finrank ℂ (basis.representation label).vector)
    (hχ : ∀ g, (basis.representation label).character g ∈
      ℚ⟮Complex.exp (2 * Real.pi * Complex.I / 5)⟯)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    p ≤ Module.finrank ℂ (basis.representation label).vector + 1 := by
  have hfaithful := injective_of_isIrreducible_of_isSimpleGroup (basis.representation label)
    (basis.irreducible label) (by omega)
  exact prime_le_of_faithful_cyclotomic_five_character _ hfaithful hχ hn hp hdvd

end CFSG.LyonsUnitaryFour
