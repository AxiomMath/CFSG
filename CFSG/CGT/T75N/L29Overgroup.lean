module

public import CFSG.CGT.T75N.L29KL
public import CFSG.CGT.T75N.L29Count
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem flagSpace_self_eq_top (n : ℕ) : flagSpace n F n = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_flagSpace]
  intro j hj
  exact absurd j.isLt (not_lt.mpr hj)

theorem unitriangular_isPGroup_two [CharP F 2] (n : ℕ) :
    IsPGroup 2 (unitriangular n F) := by
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  exact IsPGroup.of_card (n := (f : ℕ) * (n * (n - 1) / 2))
    (by rw [card_unitriangular, this, pow_mul])

theorem exists_conj_unitriangular_le_gen [CharP F 2] {n : ℕ}
    (S : Subgroup (SpecialLinearGroup (Fin n) F)) (hS : ¬ 2 ∣ S.index) :
    ∃ g : SpecialLinearGroup (Fin n) F, ∀ u ∈ unitriangular n F, g⁻¹ * u * g ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := (unitriangular_isPGroup_two (F := F) n)
    |>.nonempty_fixed_point_of_prime_not_dvd_card
    (α := SpecialLinearGroup (Fin n) F ⧸ S) (by rwa [← Subgroup.index])
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun u hu => ?_⟩
  have h := hx ⟨u⁻¹, (unitriangular n F).inv_mem hu⟩
  have h2 : ((u⁻¹ * g : SpecialLinearGroup (Fin n) F) : SpecialLinearGroup (Fin n) F ⧸ S) =
      (g : SpecialLinearGroup (Fin n) F ⧸ S) := h
  rw [QuotientGroup.eq] at h2
  simpa [mul_assoc] using h2

omit [Finite F] in
theorem le_stabilizer_of_invariant {n : ℕ} (T : Subgroup (SpecialLinearGroup (Fin n) F))
    (X : Submodule F (Fin n → F))
    (hX : ∀ s ∈ T, ∀ v ∈ X, (s : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ X) : T ≤ stabilizer X := by
  intro s hs
  change X.map (mulVecLin (s : Matrix (Fin n) (Fin n) F)) = X
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact hX s hs v hv
  · intro v hv
    refine ⟨(s⁻¹ : SpecialLinearGroup (Fin n) F) *ᵥ v, hX _ (T.inv_mem hs) v hv, ?_⟩
    rw [mulVecLin_apply, mulVec_mulVec]
    have h1 : (s : Matrix (Fin n) (Fin n) F) *
        ((s⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    rw [h1, one_mulVec]

theorem eq_top_of_index_le (k : ℕ) (T : Subgroup (SpecialLinearGroup (Fin k) F))
    (hU : unitriangular k F ≤ T) (hidx : T.index ≤ Nat.card F - 1) : T = ⊤ := by
  classical
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  rcases Nat.lt_or_ge k 2 with hk | hk
  ·
    have hsub : Subsingleton (SpecialLinearGroup (Fin k) F) := by
      interval_cases k
      · exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      · refine ⟨fun a b => Subtype.ext ?_⟩
        have ha : (a : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
          have := a.2
          rwa [det_fin_one] at this
        have hb : (b : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
          have := b.2
          rwa [det_fin_one] at this
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        subst hi
        subst hj
        rw [ha, hb]
    exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 1]; exact T.one_mem
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    by_cases hirr : ∀ X : Submodule F (Fin (m + 1) → F),
        (∀ s ∈ T, ∀ v ∈ X, (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ v ∈ X) → X = ⊥ ∨ X = ⊤
    · exact eq_top_of_unitriangular_le_gen T hU hirr
    · exfalso
      push Not at hirr
      obtain ⟨X, hX, hXbot, hXtop⟩ := hirr
      obtain ⟨j, hj, hXj⟩ := eq_flagSpace_of_invariant (fun u hu v hv => hX u (hU hu) v hv)
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hXbot (by rw [hXj, flagSpace_zero])
      have hjk : j ≠ m + 1 := by
        rintro rfl
        exact hXtop (by rw [hXj, flagSpace_self_eq_top])
      have hTle : T ≤ stabilizer (flagSpace (m + 1) F j) := by
        rw [← hXj]
        exact le_stabilizer_of_invariant T X hX
      have hind := Subgroup.index_dvd_of_le hTle
      have hTne : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hTne) hind
      have hgauss := index_stabilizer_flag_gauss (K := F) (n := m + 1) (k := j) (by omega)
      have hge := gaussianCoeff_add_one_le hq (by omega : 2 ≤ m + 1) (k := j) (by omega)
        (by omega)
      have h2 : ((Nat.card F : ℚ) + 1 ≤ (stabilizer (flagSpace (m + 1) F j)).index) := by
        rw [hgauss]
        exact hge
      have h3 : Nat.card F + 1 ≤ (stabilizer (flagSpace (m + 1) F j)).index := by
        exact_mod_cast h2
      omega

end CFSG.CGT.T75N
