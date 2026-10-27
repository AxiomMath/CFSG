module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.TraceGap
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualPairingIntegral
public import CFSG.CharacterTheory.TwoRankLowerBound.ProductCharacterReconstruction

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Finite G]

theorem one_mem_virtualCharacters (H : Type) [Group H] : (1 : H → ℂ) ∈ virtualCharacters H := by
  have := character_mem_virtualCharacters (principalFiniteComplexRepresentation H)
  rwa [principalFiniteComplexRepresentation_character] at this

omit [Finite G] in
theorem faithful_rational_character_eq_of_pow (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q) {p : ℕ} (hp : p.Prime) {x : G} {e : ℕ}
    (hx : x ^ p ^ e = 1) (hx1 : x ≠ 1) :
    ∃ k ∈ Finset.Icc 1 (Module.finrank ℂ data.vector / (p - 1)),
      data.character x = (Module.finrank ℂ data.vector : ℂ) - p * k := by
  have hρ : data.representation x ^ (p ^ e) = 1 := by rw [← map_pow, hx, map_one]
  have hne : data.representation x ≠ 1 := fun h =>
    hx1 (hfaithful (by rw [h, map_one]))
  obtain ⟨q, hq⟩ := hrational x
  obtain ⟨k, hk1, hkm, hk⟩ := trace_gap_exists_of_ne_one hp hρ hne (t := q) hq
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkm⟩, ?_⟩
  rw [hq]
  have hq' : q = (Module.finrank ℂ data.vector : ℚ) - p * k := by linarith
  rw [hq']
  push_cast
  ring

theorem sylow_card_dvd_of_faithful_rational_character (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q) {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) :
    Nat.card P ∣ p ^ (Module.finrank ℂ data.vector / (p - 1)) *
      (Module.finrank ℂ data.vector / (p - 1)).factorial := by
  classical
  set n := Module.finrank ℂ data.vector with hn
  set m := n / (p - 1) with hm
  set H : Subgroup G := (P : Subgroup G)
  have : Fintype H := Fintype.ofFinite H
  set θ : H → ℂ := data.character ∘ H.subtype with hθdef
  have hθ : θ ∈ virtualCharacters H :=
    inflation_mem_virtualCharacters H.subtype (character_mem_virtualCharacters data)
  set F : H → ℂ := ∏ k ∈ Finset.Icc 1 m, (θ - (((n : ℤ) - p * k : ℤ)) • (1 : H → ℂ)) with hFdef
  have hF : F ∈ virtualCharacters H := by
    apply Finset.prod_induction _ (· ∈ virtualCharacters H)
    · exact fun f g hf hg => virtualCharacters_mul f g hf hg
    · exact one_mem_virtualCharacters H
    · intro k _
      exact (virtualCharacters H).sub_mem hθ
        ((virtualCharacters H).smul_mem _ (one_mem_virtualCharacters H))
  have hFapply : ∀ x : H, F x = ∏ k ∈ Finset.Icc 1 m, (θ x - ((n : ℂ) - p * k)) := by
    intro x
    rw [hFdef, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro k _
    simp
  have hFzero : ∀ x : H, x ≠ 1 → F x = 0 := by
    intro x hx
    obtain ⟨e, he⟩ := P.isPGroup' x
    have hx' : (x : G) ^ p ^ e = 1 := by rw [← Subgroup.coe_pow, he, Subgroup.coe_one]
    have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
    obtain ⟨k, hk, hval⟩ :=
      faithful_rational_character_eq_of_pow data hfaithful hrational hp.out hx' hx1
    rw [hFapply]
    exact Finset.prod_eq_zero hk (by simp [hθdef, hval, hn])
  have hF1 : F 1 = ((p ^ m * m.factorial : ℕ) : ℂ) := by
    rw [hFapply]
    have hθ1 : θ 1 = n := by
      simp [hθdef, FiniteComplexRepresentation.character, Representation.char_one, hn]
    simp only [hθ1, sub_sub_cancel]
    have hfact : ∏ k ∈ Finset.Icc 1 m, (k : ℂ) = (m.factorial : ℂ) := by
      rw [← Nat.cast_prod]
      congr 1
      have : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [this, Finset.prod_Ico_id_eq_factorial]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, hfact]
    push_cast
    rfl
  obtain ⟨z, hz⟩ := characterPairing_virtual_principal_integer F hF
  have hpair : characterPairing F 1 = (Nat.card H : ℂ)⁻¹ * F 1 := by
    unfold characterPairing
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp
    · intro x _ hx
      rw [hFzero x hx, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hpair, hF1] at hz
  have hcard0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hmul : ((p ^ m * m.factorial : ℕ) : ℂ) = z * Nat.card H := by
    field_simp at hz
    linear_combination hz
  have hmulZ : ((p ^ m * m.factorial : ℕ) : ℤ) = z * Nat.card H := by exact_mod_cast hmul
  have hdvd : (Nat.card H : ℤ) ∣ ((p ^ m * m.factorial : ℕ) : ℤ) := ⟨z, by rw [hmulZ, mul_comm]⟩
  exact Int.natCast_dvd_natCast.mp hdvd

theorem prime_le_of_faithful_rational_character (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : p ≤ Module.finrank ℂ data.vector + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcard := sylow_card_dvd_of_faithful_rational_character data hfaithful hrational P
  have hpP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  by_contra hlt
  have hm : Module.finrank ℂ data.vector / (p - 1) = 0 := by
    apply Nat.div_eq_of_lt
    omega
  rw [hm, pow_zero, Nat.factorial_zero, mul_one, Nat.dvd_one] at hcard
  rw [hcard] at hpP
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpP)

theorem factorization_le_of_faithful_rational_character
    (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q) {p : ℕ} (hp : p.Prime) :
    (Nat.card G).factorization p ≤ Module.finrank ℂ data.vector / (p - 1) +
      (Module.finrank ℂ data.vector / (p - 1)).factorial.factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcard := sylow_card_dvd_of_faithful_rational_character data hfaithful hrational P
  rw [P.card_eq_multiplicity] at hcard
  have hne : p ^ (Module.finrank ℂ data.vector / (p - 1)) *
      (Module.finrank ℂ data.vector / (p - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero _)
  have := (hp.pow_dvd_iff_le_factorization hne).mp hcard
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.factorial_ne_zero _),
    Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
  exact this

end CFSG.LyonsUnitaryFour
