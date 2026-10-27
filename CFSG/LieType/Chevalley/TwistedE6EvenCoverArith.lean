module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverArith
public import CFSG.LieType.Chevalley.FoldedRootOrbits

public section

namespace CFSG.LieType.Chevalley.TwistedE6Cover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover

@[expose] def foldCoord (α : Fin TwistTag.E6.tag.rank → ℤ) (a : Fin TwistTag.E6.foldedTag.rank) :
    ℤ :=
  ∑ i ∈ TwistTag.E6.orbit a, cartanCoord α i

@[expose] def FoldUnit (v : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∃ a, foldCoord v a = 1 ∨ foldCoord v a = -1 ∨ foldCoord v a = 2 ∨ foldCoord v a = -2

instance (v : Fin TwistTag.E6.tag.rank → ℤ) : Decidable (FoldUnit v) := by
  unfold FoldUnit
  infer_instance

@[expose] def FoldCross (v w : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∀ i < 2, ∀ j < 2, ∃ a, ¬ (3 : ℤ) ∣ 2 ^ i * foldCoord v a + 2 ^ j * foldCoord w a

instance (v w : Fin TwistTag.E6.tag.rank → ℤ) : Decidable (FoldCross v w) := by
  unfold FoldCross
  infer_instance

@[expose] def FoldMinor (v w : Fin TwistTag.E6.tag.rank → ℤ) : Prop :=
  ∃ a b, foldCoord v a * foldCoord w b - foldCoord v b * foldCoord w a ≠ 0 ∧
    |foldCoord v a * foldCoord w b - foldCoord v b * foldCoord w a| < 7

instance (v w : Fin TwistTag.E6.tag.rank → ℤ) : Decidable (FoldMinor v w) := by
  unfold FoldMinor
  infer_instance

@[expose] def FoldUnitCheck (n : ℕ) : Prop :=
  0 < height (TwistTag.E6.tag.rootCertificate.root n) →
    FoldUnit (TwistTag.E6.tag.rootCertificate.root n)

instance (n : ℕ) : Decidable (FoldUnitCheck n) := by
  unfold FoldUnitCheck
  infer_instance

@[expose] def FoldPairCheck (n n' : ℕ) : Prop :=
  0 < height (TwistTag.E6.tag.rootCertificate.root n) →
    0 < height (TwistTag.E6.tag.rootCertificate.root n') →
      TwistTag.E6.tag.rootCertificate.root n' ≠ TwistTag.E6.tag.rootCertificate.root n →
        TwistTag.E6.tag.rootCertificate.root n' ≠
            permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root n) →
          FoldCross (TwistTag.E6.tag.rootCertificate.root n)
              (TwistTag.E6.tag.rootCertificate.root n') ∧
            FoldMinor (TwistTag.E6.tag.rootCertificate.root n)
              (TwistTag.E6.tag.rootCertificate.root n')

instance (n n' : ℕ) : Decidable (FoldPairCheck n n') := by
  unfold FoldPairCheck
  infer_instance

@[expose] def FoldPermCheck (n : ℕ) : Prop :=
  foldCoord (permLattice TwistTag.E6.perm (TwistTag.E6.tag.rootCertificate.root n)) =
    foldCoord (TwistTag.E6.tag.rootCertificate.root n)

instance (n : ℕ) : Decidable (FoldPermCheck n) := by
  unfold FoldPermCheck
  infer_instance

theorem foldUnitCheck : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, FoldUnitCheck n := by
  decide +kernel

theorem foldPairCheck : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length,
    ∀ n' < TwistTag.E6.tag.rootCertificate.roots.length, FoldPairCheck n n' := by
  decide +kernel

theorem foldPermCheck : ∀ n < TwistTag.E6.tag.rootCertificate.roots.length, FoldPermCheck n := by
  decide +kernel

theorem foldCoord_permLattice
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    foldCoord (permLattice TwistTag.E6.perm α) = foldCoord α := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  exact foldPermCheck n hn

theorem foldCoord_permLattice_pow {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (k : ℕ) :
    foldCoord (permLattice (TwistTag.E6.perm ^ k) α) = foldCoord α := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : permLattice (TwistTag.E6.perm ^ (k + 1)) α =
        permLattice TwistTag.E6.perm (permLattice (TwistTag.E6.perm ^ k) α) := by
      rw [pow_succ']
      rfl
    rw [e, foldCoord_permLattice (hα.permLattice (TwistTag.E6.cartan_perm_pow k)), ih]

theorem foldCoord_of_mem_diagramOrbit
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : β ∈ TwistTag.E6.diagramOrbit α) :
    foldCoord β = foldCoord α := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hβ
  exact foldCoord_permLattice_pow hα k

theorem foldUnit_of_pos
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hαp : 0 < height α) : FoldUnit α := by
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  exact foldUnitCheck n hn hαp

theorem three_le_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) : (3 : ℤ) ≤ 2 ^ f - 1 := by
  have : (4 : ℤ) ≤ 2 ^ f := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
  linarith

theorem exists_not_dvd_foldCoord
    {f : ℕ} (hf : 2 ≤ f) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α) :
    ∃ a, ¬ (2 ^ f - 1 : ℤ) ∣ foldCoord α a := by
  obtain ⟨a, ha⟩ := foldUnit_of_pos hα hαp
  refine ⟨a, fun hd => ?_⟩
  have h3 := three_le_two_pow_sub_one hf
  rcases ha with ha | ha | ha | ha <;> rw [ha] at hd
  · exact absurd (Int.le_of_dvd one_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd one_pos (dvd_neg.1 hd)) (by omega)
  · exact absurd (Int.le_of_dvd two_pos hd) (by omega)
  · exact absurd (Int.le_of_dvd two_pos (dvd_neg.1 hd)) (by omega)

theorem not_forall_dvd_of_foldCross {v w : Fin TwistTag.E6.tag.rank → ℤ} (h : FoldCross v w)
    {i j : ℕ} (hi : i < 2) (hj : j < 2) :
    ¬ ∀ a, (2 ^ 2 - 1 : ℤ) ∣ 2 ^ i * foldCoord v a + 2 ^ j * foldCoord w a := by
  intro hd
  obtain ⟨a, ha⟩ := h i hi j hj
  exact ha (by simpa using hd a)

theorem not_forall_dvd_of_foldMinor {f : ℕ} (hf : 3 ≤ f) {v w : Fin TwistTag.E6.tag.rank → ℤ}
    (h : FoldMinor v w) (i j : ℕ) :
    ¬ ∀ a, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * foldCoord v a + 2 ^ j * foldCoord w a := by
  intro hd
  obtain ⟨a, b, hne, hlt⟩ := h
  set D := foldCoord v a * foldCoord w b - foldCoord v b * foldCoord w a with hD
  have hdvd : (2 ^ f - 1 : ℤ) ∣ 2 ^ i * D := by
    have e : (2 : ℤ) ^ i * D =
        (2 ^ i * foldCoord v a + 2 ^ j * foldCoord w a) * foldCoord w b -
          (2 ^ i * foldCoord v b + 2 ^ j * foldCoord w b) * foldCoord w a := by
      rw [hD]
      ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left (hd a) _) (dvd_mul_of_dvd_left (hd b) _)
  have hD' := (isCoprime_two_pow_sub_one (by omega) i).dvd_of_dvd_mul_left hdvd
  have h7 := le_two_pow_sub_one hf
  have habs := Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hD')
  omega

theorem fold_pair_not_dvd
    {f : ℕ} (hf : 2 ≤ f) {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α) (hβ : IsRoot TwistTag.E6.tag β)
    (hβp : 0 < height β) (hβα : β ∉ TwistTag.E6.diagramOrbit α)
    (i j : ℕ) (hi : i < f) (hj : j < f) :
    ¬ ∀ a, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * foldCoord α a + 2 ^ j * foldCoord β a := by
  have h1 : β ≠ α := fun h => hβα (h ▸ TwistTag.E6.self_mem_diagramOrbit α)
  have h2 : β ≠ permLattice TwistTag.E6.perm α := fun h => hβα (by
    rw [h]
    exact Finset.mem_image.2 ⟨1, Finset.mem_range.2 (by decide), by rw [pow_one]⟩)
  obtain ⟨n, hn, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  obtain ⟨n', hn', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  obtain ⟨hcross, hminor⟩ := foldPairCheck n hn n' hn' hαp hβp h1 h2
  rcases Nat.lt_or_ge f 3 with hf3 | hf3
  · obtain rfl : f = 2 := by omega
    exact not_forall_dvd_of_foldCross hcross hi hj
  · exact not_forall_dvd_of_foldMinor hf3 hminor i j

end CFSG.LieType.Chevalley.TwistedE6Cover
