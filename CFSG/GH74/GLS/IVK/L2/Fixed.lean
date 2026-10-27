module

public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.GH74.GLS.IVK

section FixedField

variable {F : Type*} [Field F]

@[expose] noncomputable def fixedField (σ : F ≃+* F) : Subfield F :=
  FixedPoints.subfield (Subgroup.zpowers σ) F

theorem mem_fixedField_iff (σ : F ≃+* F) (x : F) : x ∈ fixedField σ ↔ σ x = x := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h a
    have hmem : σ ∈ (MulAction.stabilizer (F ≃+* F) x) := by
      rw [MulAction.mem_stabilizer_iff]
      exact h
    have := (Subgroup.zpowers_le.mpr hmem) a.2
    rw [MulAction.mem_stabilizer_iff] at this
    exact this

theorem fixedField_apply (σ : F ≃+* F) (x : fixedField σ) : σ (x : F) = x :=
  (mem_fixedField_iff σ x).mp x.2

instance instFiniteRingEquiv (F : Type*) [Field F] [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem fixedField_card_pow [Finite F] (σ : F ≃+* F) :
    Nat.card (fixedField σ) ^ orderOf σ = Nat.card F := by
  have h := CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow F
    (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at h
  exact h.symm

theorem one_lt_card_fixedField [Finite F] (σ : F ≃+* F) : 1 < Nat.card (fixedField σ) :=
  Finite.one_lt_card

theorem odd_card_fixedField [Finite F] (σ : F ≃+* F) (h : Odd (Nat.card F)) :
    Odd (Nat.card (fixedField σ)) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  rw [← fixedField_card_pow σ] at h
  exact (Nat.not_even_iff_odd.mpr h) (Nat.even_pow.mpr ⟨hne, (orderOf_pos σ).ne'⟩)

end FixedField

section Squares

variable {F : Type*} [Field F]

theorem two_mul_dvd_pow_sub_one {q₀ r : ℕ} (hq : Odd q₀) (hr : Even r) :
    2 * (q₀ - 1) ∣ q₀ ^ r - 1 := by
  obtain ⟨s, hs⟩ := hr
  have hpow : q₀ ^ r = (q₀ ^ 2) ^ s := by rw [hs, ← two_mul, pow_mul]
  have h1 : q₀ ^ 2 - 1 ∣ (q₀ ^ 2) ^ s - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (q₀ ^ 2) 1 s
  have h2 : 2 * (q₀ - 1) ∣ q₀ ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hq
    subst hk
    refine ⟨k + 1, ?_⟩
    have : (2 * k + 1) ^ 2 = 2 * (2 * k + 1 - 1) * (k + 1) + 1 := by
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]; ring
    omega
  rw [hpow]
  exact h2.trans h1

theorem isSquare_of_mem_fixedField_of_even [Finite F] (σ : F ≃+* F) (h : Even (orderOf σ))
    {a : F} (ha : a ∈ fixedField σ) : IsSquare a := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  have hcard := fixedField_card_pow σ
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0]⟩
  by_cases h2 : ringChar F = 2
  · exact FiniteField.isSquare_of_char_two h2 a
  have hodd : Odd (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two h2)
  have hq₀odd : Odd (Nat.card (fixedField σ)) := odd_card_fixedField σ hodd
  have hdvd : 2 * (Nat.card (fixedField σ) - 1) ∣ Nat.card F - 1 := by
    rw [← hcard]
    exact two_mul_dvd_pow_sub_one hq₀odd h
  have hdvd2 : (Nat.card (fixedField σ) - 1) ∣ Nat.card F / 2 := by
    have h1 : 2 * (Nat.card F / 2) + 1 = Nat.card F := Nat.two_mul_div_two_add_one_of_odd hodd
    have h3 : Nat.card F - 1 = 2 * (Nat.card F / 2) := by omega
    rw [h3] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have h1 : a ^ (Nat.card (fixedField σ) - 1) = 1 := by
    have h0 : (⟨a, ha⟩ : fixedField σ) ≠ 0 := fun h0 => ha0 (congrArg Subtype.val h0)
    have := FiniteField.pow_card_sub_one_eq_one (⟨a, ha⟩ : fixedField σ) h0
    have h' := congrArg (fun z : fixedField σ => (z : F)) this
    have h'' : a ^ (Fintype.card (fixedField σ) - 1) = 1 := by simpa using h'
    rw [← Nat.card_eq_fintype_card] at h''
    exact h''
  rw [FiniteField.isSquare_iff h2 ha0, ← Nat.card_eq_fintype_card]
  obtain ⟨m, hm⟩ := hdvd2
  rw [hm, pow_mul, h1, one_pow]

end Squares

end CFSG.GH74.GLS.IVK
