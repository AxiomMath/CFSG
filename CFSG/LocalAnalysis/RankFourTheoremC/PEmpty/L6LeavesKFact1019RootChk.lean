module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.LieType.Steinberg

section Check

@[expose] def NoCone {r : ℕ} (R : Finset (Fin r → ℤ)) (x y : Fin r → ℤ) : Prop :=
  ∀ ε ∈ R, ∀ a ∈ Finset.range (ht ε).toNat.succ, 0 < a → 0 < (ht ε - a * ht x) / ht y →
    ε ≠ a • x + ((ht ε - a * ht x) / ht y).toNat • y

instance {r : ℕ} (R : Finset (Fin r → ℤ)) (x y : Fin r → ℤ) : Decidable (NoCone R x y) := by
  unfold NoCone
  infer_instance

theorem ht_add_smul {r : ℕ} (a c : ℕ) (x y : Fin r → ℤ) :
    ht (a • x + c • y) = a * ht x + c * ht y := by
  simp [ht, Finset.sum_add_distrib, Finset.mul_sum]

theorem openCone_eq_empty_of_noCone {r : ℕ} (Φ : Set (Fin r → ℤ)) (R : Finset (Fin r → ℤ))
    (hΦ : ∀ ε, ε ∈ Φ ↔ ε ∈ R) {x y : Fin r → ℤ} (hx : 0 < ht x) (hy : 0 < ht y)
    (h : NoCone R x y) : openCone Φ x y = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro ε ⟨hε, a, c, ha, hc, rfl⟩
  have hR := (hΦ _).1 hε
  have hht := ht_add_smul a c x y
  have h1 : (a : ℤ) ≤ ht (a • x + c • y) := by
    rw [hht]; nlinarith
  have hdiv : (ht (a • x + c • y) - a * ht x) / ht y = c := by
    rw [hht, add_sub_cancel_left]
    exact Int.mul_ediv_cancel _ hy.ne'
  have hc' : (0 : ℤ) < (ht (a • x + c • y) - a * ht x) / ht y := by
    rw [hdiv]; exact_mod_cast hc
  have := h _ hR a (Finset.mem_range.2 (by omega)) ha hc'
  rw [hdiv] at this
  simp only [Int.toNat_natCast] at this
  exact this rfl

@[expose] def FourCheck {r : ℕ} (cart : Matrix (Fin r) (Fin r) ℤ) (R : Finset (Fin r → ℤ))
    (i : Fin r) (b : Fin 3 → (Fin r → ℤ)) : Prop :=
  cart i i = 2 ∧ (Pi.single i 1 : Fin r → ℤ) ∈ R ∧
  (∀ ε ∈ R, (Pi.single i 1 : Fin r → ℤ) ≠ 2 • ε) ∧
  (∀ j, b j ∈ R ∧ 0 < ht (b j) ∧ (∑ k, cart i k * b j k = 0) ∧ ∀ ε ∈ R, b j ≠ 2 • ε) ∧
  b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2 ∧ (∀ j, b j ≠ Pi.single i 1) ∧
  (∀ j, NoCone R (Pi.single i 1) (b j)) ∧ NoCone R (b 0) (b 1) ∧ NoCone R (b 0) (b 2) ∧
  NoCone R (b 1) (b 2)

instance {r : ℕ} (cart : Matrix (Fin r) (Fin r) ℤ) (R : Finset (Fin r → ℤ)) (i : Fin r)
    (b : Fin 3 → (Fin r → ℤ)) : Decidable (FourCheck cart R i b) := by
  unfold FourCheck
  infer_instance

@[expose] def TwoCheck {r : ℕ} (cart : Matrix (Fin r) (Fin r) ℤ) (R : Finset (Fin r → ℤ))
    (i : Fin r) (b : Fin r → ℤ) : Prop :=
  cart i i = 2 ∧ (Pi.single i 1 : Fin r → ℤ) ∈ R ∧
  (∀ ε ∈ R, (Pi.single i 1 : Fin r → ℤ) ≠ 2 • ε) ∧
  b ∈ R ∧ 0 < ht b ∧ (∑ k, cart i k * b k = 0) ∧ (∀ ε ∈ R, b ≠ 2 • ε) ∧
  b ≠ Pi.single i 1 ∧ NoCone R (Pi.single i 1) b

instance {r : ℕ} (cart : Matrix (Fin r) (Fin r) ℤ) (R : Finset (Fin r → ℤ)) (i : Fin r)
    (b : Fin r → ℤ) : Decidable (TwoCheck cart R i b) := by
  unfold TwoCheck
  infer_instance

end Check

section Tags

open CFSG.Blueprint.Chevalley

@[expose] def TagCheck (τ : Tag) (i : Fin τ.rank) (b : Fin 3 → (Fin τ.rank → ℤ)) : Prop :=
  FourCheck τ.cartan (rootFinset τ) i b

instance (τ : Tag) (i : Fin τ.rank) (b : Fin 3 → (Fin τ.rank → ℤ)) :
    Decidable (TagCheck τ i b) := by
  unfold TagCheck
  infer_instance

theorem tagCheck_E8 : TagCheck .E8 ⟨7, by decide⟩
    ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0]] := by
  decide +kernel

theorem tagCheck_E7 : TagCheck .E7 ⟨0, by decide⟩
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0]] := by
  decide +kernel

theorem tagCheck_E6 : TagCheck .E6 ⟨0, by decide⟩
    ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0]] := by
  decide +kernel

theorem tagCheck_F4 : TagCheck .F4 ⟨0, by decide⟩
    ![![0, 0, 0, 1], ![0, 0, 1, 1], ![1, 2, 2, 2]] := by
  decide +kernel

@[expose] def TagCheck2 (τ : Tag) (i : Fin τ.rank) (b : Fin τ.rank → ℤ) : Prop :=
  TwoCheck τ.cartan (rootFinset τ) i b

instance (τ : Tag) (i : Fin τ.rank) (b : Fin τ.rank → ℤ) : Decidable (TagCheck2 τ i b) := by
  unfold TagCheck2
  infer_instance

theorem tagCheck_G2 : TagCheck2 .G2 ⟨0, by decide⟩
    (Pi.single ⟨0, by decide⟩ 1 + 2 • Pi.single ⟨1, by decide⟩ 1) := by
  decide +kernel

end Tags

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
