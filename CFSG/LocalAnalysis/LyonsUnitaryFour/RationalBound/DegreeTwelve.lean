module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.Schur
public import CFSG.LocalAnalysis.LyonsUnitaryFour.NumericalStrongEmbedding

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem finrank_eq_one_of_isIrreducible_of_forall_eq_one {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (hirr : ρ.IsIrreducible)
    (htriv : ∀ g, ρ g = 1) : Module.finrank ℂ V = 1 := by
  have hnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    have h' : ∀ v : V, v = 0 := fun v => by
      by_contra hv
      exact h ⟨v, hv⟩
    apply hnt
    apply Subrepresentation.toSubmodule_injective
    ext x
    change x ∈ (⊥ : Submodule ℂ V) ↔ x ∈ (⊤ : Submodule ℂ V)
    simp [h' x]
  let W : Subrepresentation ρ := ⟨ℂ ∙ v, fun g w hw => by rw [htriv g]; exact hw⟩
  have hW : W = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
    · exfalso
      have hvW : v ∈ W.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at hvW
      exact hv ((Submodule.mem_bot ℂ).mp hvW)
    · exact h
  have hspan : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hW
  rw [← finrank_top ℂ V, ← hspan, finrank_span_singleton hv]

omit [Finite G] in
theorem injective_of_isIrreducible_of_isSimpleGroup [IsSimpleGroup G]
    (data : FiniteComplexRepresentation G) (hirr : data.IsIrreducible)
    (hdeg : 1 < Module.finrank ℂ data.vector) : Function.Injective data.representation := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal data.representation.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    have htriv : ∀ g, data.representation g = 1 := fun g =>
      MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)
    have := finrank_eq_one_of_isIrreducible_of_forall_eq_one hirr htriv
    omega

theorem le_of_pow_dvd_of_not_pow_dvd {p k e N : ℕ} (hk : p ^ k ∣ N)
    (hN : ¬ p ^ (e + 1) ∣ N) : k ≤ e := by
  by_contra hlt
  exact hN ((Nat.pow_dvd_pow p (by omega)).trans hk)

theorem card_dvd_of_faithful_rational_degree_twelve (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q)
    (hdeg : Module.finrank ℂ data.vector = 12) (S : Sylow 2 G) (hS : Nat.card S = 64) :
    Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have h64 : 2 ^ k ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hS]
      exact S.pow_dvd_card_of_pow_dvd_card hpk
    have hk6 : k ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h64
    exact (Nat.pow_dvd_pow 2 hk6).trans (by norm_num)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hk := (P.pow_dvd_card_of_pow_dvd_card hpk).trans
    (sylow_card_dvd_of_faithful_rational_character data hfaithful hrational P)
  rw [hdeg] at hk
  by_cases hp17 : 17 ≤ p
  · have hm : 12 / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hm, pow_zero, Nat.factorial_zero, mul_one, Nat.dvd_one] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have := Nat.one_lt_pow hk0 hp.one_lt
      omega
    rw [hk0, pow_zero]
    exact one_dvd _
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    have hlt : p < 17 := by omega
    interval_cases p <;> first | decide | omega | norm_num at hp
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · norm_num at hk
    have := le_of_pow_dvd_of_not_pow_dvd (e := 8) hk (by norm_num)
    exact (Nat.pow_dvd_pow 3 this).trans (by norm_num)
  · norm_num at hk
    have := le_of_pow_dvd_of_not_pow_dvd (e := 3) hk (by norm_num)
    exact (Nat.pow_dvd_pow 5 this).trans (by norm_num)
  · norm_num at hk
    have := le_of_pow_dvd_of_not_pow_dvd (e := 2) hk (by norm_num)
    exact (Nat.pow_dvd_pow 7 this).trans (by norm_num)
  · norm_num at hk
    have := le_of_pow_dvd_of_not_pow_dvd (e := 1) hk (by norm_num)
    exact (Nat.pow_dvd_pow 11 this).trans (by norm_num)
  · norm_num at hk
    have := le_of_pow_dvd_of_not_pow_dvd (e := 1) hk (by norm_num)
    exact (Nat.pow_dvd_pow 13 this).trans (by norm_num)

theorem not_pow_twelve_dvd_of_faithful_rational_degree_twelve
    (data : FiniteComplexRepresentation.{0, 0} G)
    (hfaithful : Function.Injective data.representation)
    (hrational : ∀ g, ∃ q : ℚ, data.character g = q)
    (hdeg : Module.finrank ℂ data.vector = 12) (S : Sylow 2 G) (hS : Nat.card S = 64)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 12 ∣ Nat.card G := fun h =>
  not_pow_twelve_dvd_lyons_order_bound hp hp2
    (h.trans (card_dvd_of_faithful_rational_degree_twelve data hfaithful hrational hdeg S hS))

theorem card_dvd_of_simple_rational_degree_twelve [Fintype G] [IsSimpleGroup G]
    (basis : FiniteIrreducibleCharacterBasis G) (label : basis.index)
    (hdeg : Module.finrank ℂ (basis.representation label).vector = 12)
    (hrational : ∀ g, ∃ q : ℚ, (basis.representation label).character g = q)
    (S : Sylow 2 G) (hS : Nat.card S = 64) :
    Nat.card G ∣ 2 ^ 6 * 3 ^ 8 * 5 ^ 3 * 7 ^ 2 * 11 * 13 ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 12 ∣ Nat.card G := by
  have hfaithful := injective_of_isIrreducible_of_isSimpleGroup (basis.representation label)
    (basis.irreducible label) (by omega)
  exact ⟨card_dvd_of_faithful_rational_degree_twelve _ hfaithful hrational hdeg S hS,
    fun p hp hp2 => not_pow_twelve_dvd_of_faithful_rational_degree_twelve _ hfaithful hrational
      hdeg S hS hp hp2⟩

end CFSG.LyonsUnitaryFour
