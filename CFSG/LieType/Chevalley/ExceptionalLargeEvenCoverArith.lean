module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus

public section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

@[expose] def UnitCoord (v : Fin τ.rank → ℤ) : Prop :=
  ∃ k, cartanCoord v k = 1 ∨ cartanCoord v k = -1 ∨ cartanCoord v k = 2 ∨ cartanCoord v k = -2

instance (v : Fin τ.rank → ℤ) : Decidable (UnitCoord v) := by
  unfold UnitCoord
  infer_instance

@[expose] def MinorBound (v w : Fin τ.rank → ℤ) : Prop :=
  ∃ k k', cartanCoord v k * cartanCoord w k' - cartanCoord v k' * cartanCoord w k ≠ 0 ∧
    |cartanCoord v k * cartanCoord w k' - cartanCoord v k' * cartanCoord w k| < 7

instance (v w : Fin τ.rank → ℤ) : Decidable (MinorBound v w) := by
  unfold MinorBound
  infer_instance

variable (τ) in
@[expose] def UnitCheck (n : ℕ) : Prop :=
  0 < height (τ.rootCertificate.root n) → UnitCoord (τ.rootCertificate.root n)

instance (n : ℕ) : Decidable (UnitCheck τ n) := by
  unfold UnitCheck
  infer_instance

variable (τ) in
@[expose] def PairCheck (n n' : ℕ) : Prop :=
  0 < height (τ.rootCertificate.root n) → 0 < height (τ.rootCertificate.root n') →
    τ.rootCertificate.root n ≠ τ.rootCertificate.root n' →
      MinorBound (τ.rootCertificate.root n) (τ.rootCertificate.root n')

instance (n n' : ℕ) : Decidable (PairCheck τ n n') := by
  unfold PairCheck
  infer_instance

theorem unitCheck_G2 : ∀ n < Tag.G2.rootCertificate.roots.length, UnitCheck .G2 n := by
  decide +kernel

theorem unitCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length, UnitCheck .F4 n := by
  decide +kernel

theorem unitCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length, UnitCheck .E6 n := by
  decide +kernel

theorem unitCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length, UnitCheck .E7 n := by
  decide +kernel

theorem unitCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length, UnitCheck .E8 n := by
  decide +kernel

theorem pairCheck_G2 : ∀ n < Tag.G2.rootCertificate.roots.length,
    ∀ n' < Tag.G2.rootCertificate.roots.length, PairCheck .G2 n n' := by
  decide +kernel

theorem pairCheck_F4 : ∀ n < Tag.F4.rootCertificate.roots.length,
    ∀ n' < Tag.F4.rootCertificate.roots.length, PairCheck .F4 n n' := by
  decide +kernel

theorem pairCheck_E6 : ∀ n < Tag.E6.rootCertificate.roots.length,
    ∀ n' < Tag.E6.rootCertificate.roots.length, PairCheck .E6 n n' := by
  decide +kernel

theorem pairCheck_E7 : ∀ n < Tag.E7.rootCertificate.roots.length,
    ∀ n' < Tag.E7.rootCertificate.roots.length, PairCheck .E7 n n' := by
  decide +kernel

theorem pairCheck_E8 : ∀ n < Tag.E8.rootCertificate.roots.length,
    ∀ n' < Tag.E8.rootCertificate.roots.length, PairCheck .E8 n n' := by
  decide +kernel

theorem isCoprime_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) (i : ℕ) :
    IsCoprime (2 ^ f - 1 : ℤ) (2 ^ i) := by
  refine IsCoprime.pow_right ⟨-1, 2 ^ (f - 1), ?_⟩
  have h : (2 : ℤ) ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h]
  ring

theorem le_two_pow_sub_one {f : ℕ} (hf : 3 ≤ f) : (7 : ℤ) ≤ 2 ^ f - 1 := by
  have h : (8 : ℤ) ≤ 2 ^ f := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
  linarith

theorem not_dvd_two_pow_add {f i j : ℕ} (hf : 3 ≤ f) (hi : i < f) (hj : j < f) :
    ¬ (2 ^ f - 1 : ℤ) ∣ 2 ^ i + 2 ^ j := by
  wlog hij : i ≤ j generalizing i j
  · rw [add_comm]
    exact this hj hi (by omega)
  intro hd
  have e : (2 : ℤ) ^ i + 2 ^ j = 2 ^ i * (1 + 2 ^ (j - i)) := by
    rw [mul_add, mul_one, ← pow_add, Nat.add_sub_cancel' hij]
  rw [e] at hd
  have hd' := (isCoprime_two_pow_sub_one (by omega) i).dvd_of_dvd_mul_left hd
  have hpos : (0 : ℤ) < 1 + 2 ^ (j - i) := by positivity
  have hle : (2 : ℤ) ^ (j - i) ≤ 2 ^ (f - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf2 : (2 : ℤ) ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : (4 : ℤ) ≤ 2 ^ (f - 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : 1 + 2 ^ (j - i) < (2 ^ f - 1 : ℤ) := by rw [hf2]; linarith
  exact absurd (Int.le_of_dvd hpos hd') (not_le.2 hlt)

theorem not_forall_dvd_of_unitCoord {f : ℕ} (hf : 3 ≤ f) {α : Fin τ.rank → ℤ}
    (hα : UnitCoord α) {i j : ℕ} (hi : i < f) (hj : j < f) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord α k := by
  intro h
  obtain ⟨k, hk⟩ := hα
  have hd := h k
  rw [← add_mul] at hd
  have hu : IsCoprime (2 ^ f - 1 : ℤ) (cartanCoord α k) := by
    rcases hk with hk | hk | hk | hk <;> rw [hk]
    · exact isCoprime_one_right
    · exact isCoprime_one_right.neg_right
    · simpa using isCoprime_two_pow_sub_one (f := f) (by omega) 1
    · simpa using (isCoprime_two_pow_sub_one (f := f) (by omega) 1).neg_right
  exact not_dvd_two_pow_add hf hi hj (hu.dvd_of_dvd_mul_right hd)

theorem not_forall_dvd_of_minorBound {f : ℕ} (hf : 3 ≤ f) {α β : Fin τ.rank → ℤ}
    (hαβ : MinorBound α β) (i j : ℕ) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k := by
  intro h
  obtain ⟨k, k', hne, hlt⟩ := hαβ
  set D := cartanCoord α k * cartanCoord β k' - cartanCoord α k' * cartanCoord β k with hD
  have hdvd : (2 ^ f - 1 : ℤ) ∣ 2 ^ i * D := by
    have e : (2 : ℤ) ^ i * D =
        (2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k) * cartanCoord β k' -
          (2 ^ i * cartanCoord α k' + 2 ^ j * cartanCoord β k') * cartanCoord β k := by
      rw [hD]
      ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left (h k) _) (dvd_mul_of_dvd_left (h k') _)
  have hD' := (isCoprime_two_pow_sub_one (by omega) i).dvd_of_dvd_mul_left hdvd
  have h7 := le_two_pow_sub_one hf
  have habs := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hD')
  omega

theorem checks_of_tag (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ n < τ.rootCertificate.roots.length, UnitCheck τ n) ∧
      ∀ n < τ.rootCertificate.roots.length, ∀ n' < τ.rootCertificate.roots.length,
        PairCheck τ n n' := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨unitCheck_G2, pairCheck_G2⟩
  · exact ⟨unitCheck_F4, pairCheck_F4⟩
  · exact ⟨unitCheck_E6, pairCheck_E6⟩
  · exact ⟨unitCheck_E7, pairCheck_E7⟩
  · exact ⟨unitCheck_E8, pairCheck_E8⟩

theorem unitCoord_of_tag
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α) : UnitCoord α := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hα
  exact (checks_of_tag hτ).1 n hn hαp

theorem pair_not_dvd
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 3 ≤ f) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α)
    (hβ : IsRoot τ β) (hβp : 0 < height β) (i j : ℕ) (hi : i < f) (hj : j < f) :
    ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k := by
  by_cases hab : α = β
  · subst hab
    exact not_forall_dvd_of_unitCoord hf (unitCoord_of_tag hτ hα hαp) hi hj
  · obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hα
    obtain ⟨n', hn', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check τ)).1 hβ
    exact not_forall_dvd_of_minorBound hf ((checks_of_tag hτ).2 n hn n' hn' hαp hβp hab) i j

theorem exists_not_dvd_cartanCoord
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 2 ≤ f) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hαp : 0 < height α) :
    ∃ k, ¬ (2 ^ f - 1 : ℤ) ∣ cartanCoord α k := by
  obtain ⟨k, hk⟩ := unitCoord_of_tag hτ hα hαp
  refine ⟨k, fun hd => ?_⟩
  have h3 : (3 : ℤ) ≤ 2 ^ f - 1 := by
    have : (4 : ℤ) ≤ 2 ^ f := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
    linarith
  rcases hk with hk | hk | hk | hk <;> rw [hk] at hd
  · exact absurd (Int.le_of_dvd one_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd one_pos (dvd_neg.1 hd)) (by omega)
  · exact absurd (Int.le_of_dvd two_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd two_pos (dvd_neg.1 hd)) (by omega)

end CFSG.LieType.Chevalley.ExceptionalCover
