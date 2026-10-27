module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GU6

theorem apply_eq_of_fix_fifth {F : Type} [Field F] [Finite F] (hF : Nat.card F = 16)
    (φ : F ≃+* F) {ζ : F} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (hφ : φ ζ = ζ) (x : F) : φ x = x := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let T : Subfield F := RingHom.eqLocusField (φ : F →+* F) (RingHom.id F)
  have hT : ∀ y : F, y ∈ T ↔ φ y = y := fun y => RingHom.mem_eqLocusField
  have hζT : ζ ∈ T := (hT ζ).2 hφ
  have hcardT : Nat.card T ∣ 16 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card T.toAddSubgroup
    rw [hF] at h
    exact h
  have h2 : 2 ≤ Nat.card T := by
    have : 1 < Nat.card T := Finite.one_lt_card
    omega
  have hle : Nat.card T ≤ 16 := Nat.le_of_dvd (by norm_num) hcardT
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ5
    norm_num at hζ5
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hunit : (⟨ζ, hζT⟩ : T) ^ (Fintype.card T - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (fun h => hζ0 (congrArg Subtype.val h))
  have hord : orderOf (⟨ζ, hζT⟩ : T) = 5 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simpa using hζ5
    · intro h
      apply hζ1
      exact congrArg Subtype.val h
  have h5 : 5 ∣ Nat.card T - 1 := by
    have h := orderOf_dvd_of_pow_eq_one hunit
    rw [hord, ← Nat.card_eq_fintype_card] at h
    exact h
  have hT16 : Nat.card T = 16 := by
    generalize hn : Nat.card T = n at hcardT hle h2 h5
    interval_cases n <;> omega
  have htop : T.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hF]; exact hT16)
  have hmem : x ∈ T.toAddSubgroup := by
    rw [htop]
    exact AddSubgroup.mem_top x
  exact (hT x).1 hmem

end CFSG.LocalAnalysis.GLTheoremA.Y10GU6
