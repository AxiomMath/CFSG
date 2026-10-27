module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def bitVec (b : Fin τ.rank → Bool) : Fin τ.rank → ℤ :=
  fun i => if b i then 1 else 0

@[expose] def parityBits (s : Fin τ.rank → ℤ) : Fin τ.rank → Bool :=
  fun i => decide (s i % 2 = 1)

theorem eq_bitVec_add (s : Fin τ.rank → ℤ) :
    s = bitVec (parityBits s) + (2 : ℤ) • (fun i => s i / 2) := by
  funext i
  simp only [bitVec, parityBits, Pi.add_apply, Pi.smul_apply, smul_eq_mul, decide_eq_true_eq]
  split_ifs with h <;> omega

theorem iform_add_two_smul (r w : Fin τ.rank → ℤ) :
    iform (r + (2 : ℤ) • w) (r + (2 : ℤ) • w) = iform r r + 4 * iform r w + 4 * iform w w := by
  rw [iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_left,
    iform_smul_right, iform_smul_right, iform_comm w r]
  ring

theorem iform_eq_sum_single (r w : Fin τ.rank → ℤ) :
    iform r w = ∑ i, w i * iform r (Pi.single i 1) := by
  conv_lhs => rw [show w = ∑ i, w i • (Pi.single i 1 : Fin τ.rank → ℤ) by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]]
  rw [iform_finset_sum_right]
  exact Finset.sum_congr rfl fun i _ => iform_smul_right _ _ _

theorem exists_odd_iform_single {t : ℤ}
    (heven : ∀ b : Fin τ.rank → Bool, (iform (bitVec b) (bitVec b)) % 2 = 0)
    (hcheck : ∀ b : Fin τ.rank → Bool, (∀ i, (iform (bitVec b) (Pi.single i 1)) % 2 = 0) →
      iform (bitVec b) (bitVec b) % 8 ≠ t % 8)
    {s : Fin τ.rank → ℤ} (hs : iform s s = t) : ∃ i, Odd (iform s (Pi.single i 1)) := by
  by_contra h
  push Not at h
  have hev : ∀ i, iform s (Pi.single i 1) % 2 = 0 := fun i =>
    Int.even_iff.1 (Int.not_odd_iff_even.1 (h i))
  set r := bitVec (parityBits s) with hr_def
  set w : Fin τ.rank → ℤ := fun i => s i / 2 with hw_def
  have hsr : s = r + (2 : ℤ) • w := eq_bitVec_add s
  have hr : ∀ i, iform r (Pi.single i 1) % 2 = 0 := fun i => by
    have := hev i
    rw [hsr, iform_add_left, iform_smul_left] at this
    omega
  have hrw : iform r w % 2 = 0 := by
    rw [iform_eq_sum_single, ← Int.even_iff]
    exact Finset.even_sum _ fun i _ =>
      (Int.even_iff.2 (hr i)).mul_left _
  have hww : iform w w % 2 = 0 := by
    have h1 := heven (parityBits w)
    rw [eq_bitVec_add w, iform_add_two_smul]
    omega
  have h8 : iform s s % 8 = iform r r % 8 := by
    rw [hsr, iform_add_two_smul]
    omega
  exact hcheck _ hr (by rw [← h8, hs])

theorem e7_even_vec : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (iform (τ := .E7) (bitVec ![b0, b1, b2, b3, b4, b5, b6])
      (bitVec ![b0, b1, b2, b3, b4, b5, b6])) % 2 = 0 := by
  decide

theorem e7_check_vec : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (∀ i, (iform (τ := .E7) (bitVec ![b0, b1, b2, b3, b4, b5, b6]) (Pi.single i 1)) % 2 = 0) →
      iform (τ := .E7) (bitVec ![b0, b1, b2, b3, b4, b5, b6])
        (bitVec ![b0, b1, b2, b3, b4, b5, b6]) % 8 ≠ 4 := by
  decide

theorem e7_eq_vec (b : Fin (Tag.rank .E7) → Bool) :
    b = ![b ⟨0, by decide⟩, b ⟨1, by decide⟩, b ⟨2, by decide⟩, b ⟨3, by decide⟩, b ⟨4, by decide⟩,
      b ⟨5, by decide⟩, b ⟨6, by decide⟩] := by
  funext i
  fin_cases i <;> rfl

theorem e7_even (b : Fin (Tag.rank .E7) → Bool) :
    (iform (τ := .E7) (bitVec b) (bitVec b)) % 2 = 0 := by
  rw [e7_eq_vec b]
  exact e7_even_vec _ _ _ _ _ _ _

theorem e7_check (b : Fin (Tag.rank .E7) → Bool)
    (h : ∀ i, (iform (τ := .E7) (bitVec b) (Pi.single i 1)) % 2 = 0) :
    iform (τ := .E7) (bitVec b) (bitVec b) % 8 ≠ 4 % 8 := by
  rw [e7_eq_vec b] at h ⊢
  exact e7_check_vec _ _ _ _ _ _ _ h

theorem e6_even_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (iform (τ := .E6) (bitVec ![b0, b1, b2, b3, b4, b5])
      (bitVec ![b0, b1, b2, b3, b4, b5])) % 2 = 0 := by
  decide

theorem e6_check_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (∀ i, (iform (τ := .E6) (bitVec ![b0, b1, b2, b3, b4, b5]) (Pi.single i 1)) % 2 = 0) →
      iform (τ := .E6) (bitVec ![b0, b1, b2, b3, b4, b5])
        (bitVec ![b0, b1, b2, b3, b4, b5]) % 8 ≠ 4 := by
  decide

theorem e6_eq_vec (b : Fin (Tag.rank .E6) → Bool) :
    b = ![b ⟨0, by decide⟩, b ⟨1, by decide⟩, b ⟨2, by decide⟩, b ⟨3, by decide⟩, b ⟨4, by decide⟩,
      b ⟨5, by decide⟩] := by
  funext i
  fin_cases i <;> rfl

theorem e6_even (b : Fin (Tag.rank .E6) → Bool) :
    (iform (τ := .E6) (bitVec b) (bitVec b)) % 2 = 0 := by
  rw [e6_eq_vec b]
  exact e6_even_vec _ _ _ _ _ _

theorem e6_check (b : Fin (Tag.rank .E6) → Bool)
    (h : ∀ i, (iform (τ := .E6) (bitVec b) (Pi.single i 1)) % 2 = 0) :
    iform (τ := .E6) (bitVec b) (bitVec b) % 8 ≠ 4 % 8 := by
  rw [e6_eq_vec b] at h ⊢
  exact e6_check_vec _ _ _ _ _ _ h

theorem d4_even_vec : ∀ b0 b1 b2 b3 : Bool,
    (iform (τ := .D4) (bitVec ![b0, b1, b2, b3])
      (bitVec ![b0, b1, b2, b3])) % 2 = 0 := by
  decide

theorem d4_check_vec : ∀ b0 b1 b2 b3 : Bool,
    (∀ i, (iform (τ := .D4) (bitVec ![b0, b1, b2, b3]) (Pi.single i 1)) % 2 = 0) →
      iform (τ := .D4) (bitVec ![b0, b1, b2, b3])
        (bitVec ![b0, b1, b2, b3]) % 8 ≠ 6 := by
  decide

theorem d4_eq_vec (b : Fin (Tag.rank .D4) → Bool) :
    b = ![b ⟨0, by decide⟩, b ⟨1, by decide⟩, b ⟨2, by decide⟩, b ⟨3, by decide⟩] := by
  funext i
  fin_cases i <;> rfl

theorem d4_even (b : Fin (Tag.rank .D4) → Bool) :
    (iform (τ := .D4) (bitVec b) (bitVec b)) % 2 = 0 := by
  rw [d4_eq_vec b]
  exact d4_even_vec _ _ _ _

theorem d4_check (b : Fin (Tag.rank .D4) → Bool)
    (h : ∀ i, (iform (τ := .D4) (bitVec b) (Pi.single i 1)) % 2 = 0) :
    iform (τ := .D4) (bitVec b) (bitVec b) % 8 ≠ 6 % 8 := by
  rw [d4_eq_vec b] at h ⊢
  exact d4_check_vec _ _ _ _ h

theorem exists_odd_iform_single_four (hτ : τ = .E6 ∨ τ = .E7) {s : Fin τ.rank → ℤ}
    (hs : iform s s = 4) : ∃ i, Odd (iform s (Pi.single i 1)) := by
  rcases hτ with rfl | rfl
  · exact exists_odd_iform_single e6_even e6_check hs
  · exact exists_odd_iform_single e7_even e7_check hs

theorem exists_odd_iform_single_six {s : Fin (Tag.rank .D4) → ℤ} (hs : iform s s = 6) :
    ∃ i, Odd (iform s (Pi.single i 1)) :=
  exists_odd_iform_single d4_even d4_check hs

end CFSG.ComponentClassification.ExcSelector
