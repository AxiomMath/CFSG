module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JF4a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

structure Sec12Act {W Γ : Type} [Group W] [Group Γ] (ψ : Γ →* MulAut W)
    (φ : Sec12SL × Sec12SL →* Γ) : Prop where
  card : Nat.card W = 256
  comm : ∀ a b : W, a * b = b * a
  inj : Function.Injective φ
  fix1 : ∀ p : Sec12SL × Sec12SL, p ≠ 1 → Nat.card {w : W // ψ (φ p) w = w} ≤ 16
  fix2 : ∀ A B : Sec12SL, A ≠ 1 → B ≠ 1 →
    Nat.card {w : W // ψ (φ (A, 1)) w = w ∧ ψ (φ (1, B)) w = w} ≤ 4
  gen : ∀ w : W, ψ (φ (sec12U, 1)) w = w → ψ (φ (sec12Lo, 1)) w = w → w = 1

theorem sec12_card_M : Nat.card Sec12M = 256 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sec12Act_of_model {W Γ : Type} [Group W] [Group Γ] (ψ : Γ →* MulAut W)
    (φ : Sec12SL × Sec12SL →* Γ) (e : W ≃* Multiplicative Sec12M) (hinj : Function.Injective φ)
    (hact : ∀ (A B : Sec12SL) (w : W), Multiplicative.toAdd (e (ψ (φ (A, B)) w)) =
      (A : Sec12M) * Multiplicative.toAdd (e w) * (B : Sec12M)ᵀ) : Sec12Act ψ φ := by
  have hcard : Nat.card W = 256 := by
    rw [Nat.card_congr e.toEquiv]
    exact sec12_card_M
  have hle : ∀ (P : W → Prop) (Q : Sec12M → Prop),
      (∀ w, P w → Q (Multiplicative.toAdd (e w))) → Nat.card {w // P w} ≤ Nat.card {M // Q M} := by
    intro P Q h
    refine Nat.card_le_card_of_injective (fun w => ⟨Multiplicative.toAdd (e w.1), h w.1 w.2⟩) ?_
    intro a b hab
    apply Subtype.ext
    have h1 := congrArg (fun z : {M // Q M} => z.1) hab
    exact e.injective (Multiplicative.toAdd.injective h1)
  have hone : ((1 : Sec12SL) : Sec12M) = 1 := rfl
  have hone' : ((1 : Sec12SL) : Sec12M)ᵀ = 1 := by rw [hone, Matrix.transpose_one]
  refine ⟨hcard, ?_, hinj, ?_, ?_, ?_⟩
  · intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · intro p hp
    have hne : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hp (Prod.ext hcon.1 hcon.2)
    obtain ⟨A, B⟩ := p
    refine (hle _ (fun M => (A : Sec12M) * M * (B : Sec12M)ᵀ = M) ?_).trans
      (sec12F4_fix_le A B hne)
    intro w hw
    have h1 := hact A B w
    rw [hw] at h1
    exact h1.symm
  · intro A B hA hB
    refine (hle _ (fun M => (A : Sec12M) * M = M ∧ M * (B : Sec12M)ᵀ = M) ?_).trans
      (sec12F4_fix2_le A B hA hB)
    rintro w ⟨hw1, hw2⟩
    have h1 := hact A 1 w
    have h2 := hact 1 B w
    rw [hw1] at h1
    rw [hw2] at h2
    rw [hone', mul_one] at h1
    rw [hone, Matrix.one_mul] at h2
    exact ⟨h1.symm, h2.symm⟩
  · intro w h1 h2
    have h3 := hact sec12U 1 w
    have h4 := hact sec12Lo 1 w
    rw [h1] at h3
    rw [h2] at h4
    rw [hone', mul_one] at h3 h4
    have h5 := sec12F4_gen_fin (Multiplicative.toAdd (e w)) h3.symm h4.symm
    apply e.injective
    rw [map_one]
    exact Multiplicative.toAdd.injective (by simpa using h5)

end CFSG.OddStandard.SmallF3.Omega
