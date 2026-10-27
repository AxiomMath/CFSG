module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem c16N_comm_mul_of_abelian {A : Subgroup G} {t : G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAt : ∀ f ∈ A, ⁅f, t⁆ ∈ A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
  have hbA : ⁅b, t⁆ ∈ A := hAt b hb
  have haA : ⁅a, t⁆ ∈ A := hAt a ha
  have hconj : a * ⁅b, t⁆ * a⁻¹ = ⁅b, t⁆ := by
    rw [hA a ha (⁅b, t⁆) hbA, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul, hconj]
  exact (hA (⁅a, t⁆) haA (⁅b, t⁆) hbA).symm

theorem c16_norm_onto [Finite G] {Y K : Subgroup G} {t : G}
    (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hKY : K ≤ Y) (hcomm : ∀ f ∈ Y, ⁅f, t⁆ ∈ K)
    (hker : ∀ f ∈ Y, ⁅f, t⁆ = 1 → f ∈ K) (hKt : ∀ k ∈ K, k * t = t * k)
    (hcard : Nat.card Y = Nat.card K * Nat.card K) : ∀ k ∈ K, ∃ f ∈ Y, ⁅f, t⁆ = k := by
  let φ : Y →* K :=
    { toFun := fun f => ⟨⁅f.1, t⁆, hcomm f.1 f.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        exact c16N_comm_mul_of_abelian hY (fun f hf => hKY (hcomm f hf)) a.2 b.2 }
  have hcard_ker : Nat.card φ.ker = Nat.card K := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, hker x.1.1 x.1.2 ?_⟩
        invFun := fun k => ⟨⟨k.1, hKY k.2⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := congrArg Subtype.val x.2
      dsimp only [φ] at h
      exact h
    · apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hKt k.1 k.2)
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      rfl
    · intro k
      apply Subtype.ext
      rfl
  have hmul : Nat.card K * Nat.card φ.range = Nat.card K * Nat.card K :=
    calc Nat.card K * Nat.card φ.range
        = Nat.card φ.ker * Nat.card φ.range := by rw [hcard_ker]
      _ = Nat.card Y := Subgroup.card_ker_mul_card_range φ
      _ = Nat.card K * Nat.card K := hcard
  have hrange : Nat.card φ.range = Nat.card K :=
    Nat.mul_left_cancel (Nat.card_pos_iff.mpr ⟨⟨(1 : K)⟩, inferInstance⟩) hmul
  have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq φ.range hrange
  intro k hk
  have hmem : (⟨k, hk⟩ : K) ∈ φ.range := by rw [htop]; exact Subgroup.mem_top _
  rcases hmem with ⟨f, hf⟩
  refine ⟨f.1, f.2, ?_⟩
  have h := congrArg Subtype.val hf
  dsimp only [φ] at h
  exact h

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
