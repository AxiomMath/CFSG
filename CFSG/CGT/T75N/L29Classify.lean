module

public import CFSG.CGT.T75N.L29Dual

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] {m : ℕ}

theorem odd_card_pow_sub_one [CharP F 2] {n : ℕ} (hn : 1 ≤ n) :
    ¬ 2 ∣ Nat.card F ^ n - 1 := by
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  rw [hq, ← pow_mul]
  have h2 : 2 ∣ 2 ^ ((f : ℕ) * n) := dvd_pow_self 2 (by positivity)
  have h3 : 1 ≤ 2 ^ ((f : ℕ) * n) := Nat.one_le_two_pow
  omega

theorem fixes_flag_one_or_last [CharP F 2] (S : Subgroup (SpecialLinearGroup (Fin (m + 2)) F))
    (hU : unitriangular (m + 2) F ≤ S) (hidx : S.index = Nat.card F ^ (m + 2) - 1) :
    S ≤ stabilizer (flagSpace (m + 2) F 1) ∨ S ≤ stabilizer (flagSpace (m + 2) F (m + 1)) := by
  classical
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hqn : 2 ^ (m + 2) ≤ Nat.card F ^ (m + 2) := Nat.pow_le_pow_left hq _
  have h4 : 4 ≤ 2 ^ (m + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hirr : ∀ X : Submodule F (Fin (m + 2) → F),
      (∀ s ∈ S, ∀ v ∈ X, (s : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ v ∈ X) → X = ⊥ ∨ X = ⊤
  · exfalso
    have htop := eq_top_of_unitriangular_le_gen (m := m + 1) S hU hirr
    rw [htop, Subgroup.index_top] at hidx
    omega
  · push Not at hirr
    obtain ⟨X, hX, hXbot, hXtop⟩ := hirr
    obtain ⟨j, hj, hXj⟩ := eq_flagSpace_of_invariant (fun u hu v hv => hX u (hU hu) v hv)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hXbot (by rw [hXj, flagSpace_zero])
    have hjk : j ≠ m + 2 := by
      rintro rfl
      exact hXtop (by rw [hXj, flagSpace_self_eq_top])
    have hle : S ≤ stabilizer (flagSpace (m + 2) F j) := by
      rw [← hXj]
      exact le_stabilizer_of_invariant S X hX
    by_cases h1 : j = 1
    · subst h1
      exact Or.inl hle
    by_cases h2 : j = m + 1
    · subst h2
      exact Or.inr hle
    exfalso
    have hind := Subgroup.index_dvd_of_le hle
    have hSne : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle' := Nat.le_of_dvd (Nat.pos_of_ne_zero hSne) hind
    have hgauss := index_stabilizer_flag_gauss (K := F) (n := m + 2) (k := j) (by omega)
    have hgt := gaussianCoeff_gt hq (by omega : 4 ≤ m + 2) (k := j) (by omega) (by omega)
    have h3 : ((Nat.card F ^ (m + 2) - 1 : ℕ) : ℚ) <
        (stabilizer (flagSpace (m + 2) F j)).index := by
      rw [hgauss, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
      exact hgt
    have h3' : Nat.card F ^ (m + 2) - 1 < (stabilizer (flagSpace (m + 2) F j)).index := by
      exact_mod_cast h3
    omega

theorem classify_stab [CharP F 2] (S : Subgroup (SpecialLinearGroup (Fin (m + 2)) F))
    (hidx : S.index = Nat.card F ^ (m + 2) - 1) :
    (∃ g : SpecialLinearGroup (Fin (m + 2)) F, ∀ y, y ∈ S ↔
      g * y * g⁻¹ ∈ vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)) ∨
    (∃ g : SpecialLinearGroup (Fin (m + 2)) F, ∀ y, y ∈ S ↔
      g * y * g⁻¹ ∈ (vecStab (m + 2) (Pi.single 0 1 : Fin (m + 2) → F)).map
        (tauHom (m + 2) F)) := by
  classical
  have hodd : ¬ 2 ∣ S.index := by
    rw [hidx]
    exact odd_card_pow_sub_one (by omega)
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_le_gen S hodd
  set S' : Subgroup (SpecialLinearGroup (Fin (m + 2)) F) :=
    S.comap (MulAut.conj g⁻¹).toMonoidHom with hS'
  have hmem : ∀ y, y ∈ S' ↔ g⁻¹ * y * g ∈ S := by
    intro y
    simp [hS']
  have hU : unitriangular (m + 2) F ≤ S' := fun u hu => (hmem u).2 (hg u hu)
  have hidx' : S'.index = Nat.card F ^ (m + 2) - 1 := by
    rw [hS', Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)]
    exact hidx
  have hback : ∀ y, y ∈ S ↔ g * y * g⁻¹ ∈ S' := by
    intro y
    rw [hmem]
    simp [mul_assoc]
  rcases fixes_flag_one_or_last S' hU hidx' with h | h
  · left
    refine ⟨g, fun y => ?_⟩
    rw [hback, eq_vecStab_of_index S' hU h hidx']
  · right
    refine ⟨g, fun y => ?_⟩
    rw [hback, eq_tau_vecStab_of_index S' hU h hidx']

end CFSG.CGT.T75N
