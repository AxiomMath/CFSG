module

public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem fg_exists_kernel {Γ : Type*} [Group Γ] (B : Subgroup Γ) (hB : Nat.card B = 16)
    (χ : ↥B → ZMod 3) (hone : χ 1 = 1) (hmul : ∀ g h, χ (g * h) = χ g * χ h)
    (hsq : ∀ g, χ g * χ g = 1) (hnt : ∃ g, χ g ≠ 1) :
    ∃ H : Subgroup Γ, H ≤ B ∧ Nat.card H = 8 ∧
      ∀ (g : Γ) (hg : g ∈ B), g ∈ H ↔ χ ⟨g, hg⟩ = 1 := by
  classical
  have hne : ∀ g : ↥B, χ g ≠ 0 := by
    intro g hg0
    have h0 : (0 : ZMod 3) ≠ 1 := by decide
    exact h0 (by simpa [hg0] using hsq g)
  let φ : ↥B →* (ZMod 3)ˣ :=
    { toFun := fun g => Units.mk0 (χ g) (hne g)
      map_one' := by
        apply Units.ext
        simp [Units.val_mk0, hone]
      map_mul' := by
        intro g h
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        exact hmul g h }
  have hφ : ∀ x : ↥B, (φ x : ZMod 3) = χ x := by
    intro x
    rfl
  have hunits : Nat.card (ZMod 3)ˣ = 2 := by
    rw [Nat.card_units, Nat.card_zmod]
  have hker : Nat.card φ.ker * Nat.card φ.range = 16 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rwa [hB] at h
  have hdvd : Nat.card φ.range ∣ 2 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hunits] at h
  have hne1 : Nat.card φ.range ≠ 1 := by
    rintro h1
    obtain ⟨g, hg⟩ := hnt
    have hbot : φ.range = ⊥ := (Subgroup.card_eq_one).mp h1
    have hmem : φ g ∈ φ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    rw [hbot] at hmem
    have hφg : φ g = 1 := by simpa using hmem
    apply hg
    have hthis := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hφg
    rw [hφ, Units.val_one] at hthis
    exact hthis
  have hrange : Nat.card φ.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hcardker : Nat.card φ.ker = 8 := by
    have h16 : (16 : ℕ) = 8 * 2 := rfl
    rw [hrange, h16] at hker
    exact mul_right_cancel₀ (by decide : (2 : ℕ) ≠ 0) hker
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le φ.ker, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective, hcardker]
  · intro g hg
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, hkg⟩
      have hk' : k = ⟨g, hg⟩ := Subtype.ext (by simpa using hkg)
      rw [hk'] at hk
      rw [MonoidHom.mem_ker] at hk
      have hthis := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hk
      rw [hφ, Units.val_one] at hthis
      exact hthis
    · intro hχ
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [hφ, hχ, Units.val_one]

end CFSG.OddStandard.SmallF3.Omega