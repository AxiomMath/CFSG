module

public import CFSG.CharacterTheory.Semidihedral.NormalInductionConstituent
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalFamily

public section

noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.OddFieldSL2Degree

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.Wreathed.CentralSL2Abelianization CFSG.Semidihedral.NormalInductionConstituent
  CFSG.Section1

theorem isIrreducibleCharacterOnGroup_of_mem_blocksIrr {K : Type} [Group K] [Finite K]
    {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K) : IsIrreducibleCharacterOnGroup θ := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hθ
  exact ⟨Module.finrank ℂ V, standardizeRepresentation ρ,
    standardizeRepresentation_irreducible ρ hρ,
    funext fun g => (standardizeRepresentation_character ρ g).symm⟩

theorem mem_blocksIrr_of_isIrreducibleCharacterOnGroup {K : Type} [Group K] [Finite K]
    {θ : K → ℂ} (hθ : IsIrreducibleCharacterOnGroup θ) : θ ∈ BlocksIrr K := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hθ
  exact ⟨Fin n → ℂ, inferInstance, inferInstance, inferInstance, ρ, hρ, rfl⟩

theorem comp_mulEquiv_mem_blocksIrr {K K' : Type} [Group K] [Group K'] (e : K' ≃* K)
    {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K) : θ ∘ e ∈ BlocksIrr K' := by
  obtain ⟨V, i₁, i₂, i₃, ρ, hρ, rfl⟩ := hθ
  exact ⟨V, i₁, i₂, i₃, ρ.comp e.toMonoidHom,
    CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective e.toMonoidHom e.surjective ρ hρ, rfl⟩

theorem degree_of_mem_blocksIrr {F : Type} [Field F] [Fintype F] {p : ℕ} (hpodd : Odd p)
    [CharP F p] {b : Fˣ} (hb : ¬ IsSquare b) {m : ℕ} {hm : 0 < m} {heven : Even m}
    {χ : CentralExtension F b m hm heven → ℂ}
    (hχ : χ ∈ BlocksIrr (CentralExtension F b m hm heven)) :
    χ 1 = 1 ∨ χ 1 = Nat.card F ∨ χ 1 = Nat.card F + 1 ∨ χ 1 = Nat.card F - 1 := by
  obtain ⟨E, _, _, basis, y, hy⟩ := exists_cuspidal_data (F := F) hb
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (F := F)
  have h2 := two_ne_zero_of_not_isSquare hb
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  obtain ⟨hall, -⟩ := blocksIrr_eq_families (basis := basis) (hm := hm) (heven := heven) hpodd
    hb y hy h2 hψ _ hζ
  rw [hall] at hχ
  rcases hχ with ((h | h) | h) | h
  · exact Or.inl (linearFamily_degree _ hζ χ h)
  · exact Or.inr (Or.inl (steinbergFamily_degree _ hζ χ h))
  · exact Or.inr (Or.inr (Or.inl (principalFamily_degree χ h)))
  · exact Or.inr (Or.inr (Or.inr (cuspidalFamily_degree hb y hy h2 χ h)))

theorem odd_field_SL2_irreducible_degree_is_not_divisible_by_two_times_characteristic
    {F : Type} [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (θ : SpecialLinearGroup (Fin 2) F → ℂ)
    (hθ : θ ∈ BlocksIrr (SpecialLinearGroup (Fin 2) F)) :
    ∃ n : ℕ, θ 1 = n ∧ 0 < n ∧
      (∃ d a : ℕ, (d = 1 ∨ d = Nat.card F ∨ d = Nat.card F - 1 ∨ d = Nat.card F + 1) ∧
        0 < a ∧ d = a * n) ∧
      (p ∣ n → n ∣ Nat.card F ∧ Odd n) ∧ ¬ 2 * p ∣ n := by
  have hchar : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hring : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    rintro rfl
    exact absurd hpodd (by decide)
  obtain ⟨a₀, ha₀⟩ := FiniteField.exists_nonsquare hring
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact ha₀ ⟨0, by rw [mul_zero]⟩
  let b : Fˣ := Units.mk0 a₀ ha₀0
  have hb : ¬ IsSquare b := by
    rintro ⟨c, hc⟩
    exact ha₀ ⟨c, by rw [← Units.val_mk0 ha₀0]; exact congrArg Units.val hc⟩
  have hinj := specialInclusion_injective F b 2 two_pos even_two
  let H : Subgroup (CentralExtension F b 2 two_pos even_two) :=
    (specialInclusion F b 2 two_pos even_two).range
  have : H.Normal := by
    change (specialInclusion F b 2 two_pos even_two).range.Normal
    rw [← baseResidue_ker F b 2 two_pos even_two]
    infer_instance
  let e : SpecialLinearGroup (Fin 2) F ≃* H := MonoidHom.ofInjective hinj
  let θH : H → ℂ := θ ∘ e.symm
  have hθH : IsIrreducibleCharacterOnGroup θH :=
    isIrreducibleCharacterOnGroup_of_mem_blocksIrr (comp_mulEquiv_mem_blocksIrr e.symm hθ)
  obtain ⟨χ, hχ, -, a, -, ha, -, hdeg⟩ := exists_irreducible_positive_degree_multiple H θH hθH
  obtain ⟨n, hn, hθn⟩ := blocksIrr_one_eq_natCast hθ
  have hdθH : degree θH = n := by
    change θ (e.symm 1) = n
    rw [map_one]
    exact hθn
  have hχ1 : χ 1 = ((a * n : ℕ) : ℂ) := by
    change degree χ = _
    rw [hdeg, hdθH]
    push_cast
    ring
  have hq1 : 1 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.one_le_pow _ _ hp.pos
  have hd : a * n = 1 ∨ a * n = Nat.card F ∨ a * n = Nat.card F - 1 ∨
      a * n = Nat.card F + 1 := by
    rcases degree_of_mem_blocksIrr hpodd hb (mem_blocksIrr_of_isIrreducibleCharacterOnGroup hχ)
      with h | h | h | h <;> rw [hχ1] at h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (Or.inl (by exact_mod_cast h))
    · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast h)))
    · refine Or.inr (Or.inr (Or.inl ?_))
      have h' : ((a * n + 1 : ℕ) : ℂ) = (Nat.card F : ℂ) := by
        push_cast at h ⊢
        rw [h]
        ring
      have := Nat.cast_injective h'
      omega
  have hpq : p ∣ Nat.card F := by
    rw [hcard]
    exact dvd_pow_self p (by omega)
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hpodd.pow
  have hpart : p ∣ n → n ∣ Nat.card F ∧ Odd n := by
    intro hpn
    have hpd : p ∣ a * n := hpn.mul_left a
    have hdq : a * n = Nat.card F := by
      rcases hd with h | h | h | h
      · rw [h] at hpd
        exact absurd (Nat.le_of_dvd one_pos hpd) (by have := hp.two_le; omega)
      · exact h
      · rw [h] at hpd
        have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hpq hpd
        rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
        exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.two_le; omega)
      · rw [h] at hpd
        have h1 : p ∣ 1 := (Nat.dvd_add_right hpq).mp hpd
        exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.two_le; omega)
    have hnq : n ∣ Nat.card F := ⟨a, by rw [← hdq, mul_comm]⟩
    exact ⟨hnq, hqodd.of_dvd_nat hnq⟩
  refine ⟨n, hθn, hn, ⟨a * n, a, hd, ha, rfl⟩, hpart, fun h2p => ?_⟩
  obtain ⟨-, hnodd⟩ := hpart ((Dvd.intro_left 2 rfl).trans h2p)
  exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr ((Dvd.intro p rfl).trans h2p))

end CFSG.Semidihedral.OddFieldSL2Degree
