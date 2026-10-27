module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

@[expose]
def fz21b_S01 : FzSigma4 := Equiv.swap 0 1

@[expose]
def fz21b_S23 : FzSigma4 := Equiv.swap 2 3

@[expose]
def fz21b_D1 : FzSigma4 := fz21b_S01 * fz21b_S23

@[expose]
def fz21b_D2 : FzSigma4 := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose]
def fz21b_D3 : FzSigma4 := fz21b_D1 * fz21b_D2

@[expose]
def fz21b_C012 : FzSigma4 := Equiv.swap 0 1 * Equiv.swap 0 2

@[expose]
def fz21b_C013 : FzSigma4 := Equiv.swap 0 1 * Equiv.swap 0 3

private abbrev IsDbl (d : FzSigma4) : Prop := d ^ 2 = 1 ∧ ∀ i, d i ≠ i

abbrev fz21b_V : Subgroup FzSigma4 where
  carrier := {x | x = 1 ∨ x = fz21b_D1 ∨ x = fz21b_D2 ∨ x = fz21b_D3}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

instance : DecidablePred (· ∈ fz21b_V) := fun x => by
  change Decidable (x = 1 ∨ x = fz21b_D1 ∨ x = fz21b_D2 ∨ x = fz21b_D3)
  infer_instance

lemma fz21b_V_card : Nat.card fz21b_V = 4 := by
  rw [Nat.card_eq_fintype_card]; decide

lemma fz21b_V_normal : fz21b_V.Normal := ⟨by decide⟩

lemma fz21b_V_sq_one : ∀ v ∈ fz21b_V, v ^ 2 = 1 := by decide

lemma fz21b_V_le_of_normal {M : Subgroup FzSigma4} (hM : M.Normal)
    (hcard : 1 < Nat.card M) : fz21b_V ≤ M := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have hcard' : 1 < Fintype.card M := by rwa [Nat.card_eq_fintype_card] at hcard
  obtain ⟨y, hy1⟩ := Fintype.exists_ne_of_one_lt_card hcard' (1 : M)
  have hyM : (y : FzSigma4) ∈ M := y.2
  have hyne : (y : FzSigma4) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have key : ∀ d : FzSigma4, IsDbl d → d ∈ M → fz21b_V ≤ M := by
    intro d hd hdM
    have hconj : (∃ g, g * d * g⁻¹ = fz21b_D1) ∧ (∃ g, g * d * g⁻¹ = fz21b_D2) :=
      (by decide : ∀ d : FzSigma4, IsDbl d →
        (∃ g, g * d * g⁻¹ = fz21b_D1) ∧ (∃ g, g * d * g⁻¹ = fz21b_D2)) d hd
    obtain ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩ := hconj
    have hD1 : fz21b_D1 ∈ M := hg1 ▸ hM.conj_mem d hdM g1
    have hD2 : fz21b_D2 ∈ M := hg2 ▸ hM.conj_mem d hdM g2
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact M.one_mem
    · exact hD1
    · exact hD2
    · exact M.mul_mem hD1 hD2
  rcases (by decide : ∀ x : FzSigma4, x ≠ 1 →
      x ^ 2 = 1 ∨ (x ^ 3 = 1 ∧ x ≠ 1) ∨ (x ^ 4 = 1 ∧ x ^ 2 ≠ 1)) (y : FzSigma4) hyne with
    h2 | h3 | h4
  · by_cases hfix : ∃ i, (y : FzSigma4) i = i
    · have hconj : (∃ g, g * (y : FzSigma4) * g⁻¹ = fz21b_S01) ∧
          (∃ g, g * (y : FzSigma4) * g⁻¹ = fz21b_S23) :=
        (by decide : ∀ x : FzSigma4, x ^ 2 = 1 → x ≠ 1 → (∃ i, x i = i) →
          (∃ g, g * x * g⁻¹ = fz21b_S01) ∧
            (∃ g, g * x * g⁻¹ = fz21b_S23)) (y : FzSigma4) h2 hyne hfix
      obtain ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩ := hconj
      have hS01 : fz21b_S01 ∈ M := hg1 ▸ hM.conj_mem (y : FzSigma4) hyM g1
      have hS23 : fz21b_S23 ∈ M := hg2 ▸ hM.conj_mem (y : FzSigma4) hyM g2
      have hD : fz21b_D1 ∈ M := by
        show fz21b_S01 * fz21b_S23 ∈ M
        exact M.mul_mem hS01 hS23
      exact key fz21b_D1 (by decide) hD
    · push_neg at hfix
      exact key (y : FzSigma4) ⟨h2, fun i => hfix i⟩ hyM
  · obtain ⟨h3pow, h3ne⟩ := h3
    have hconj : (∃ g, g * (y : FzSigma4) * g⁻¹ = fz21b_C012) ∧
        (∃ g, g * (y : FzSigma4) * g⁻¹ = fz21b_C013) :=
      (by decide : ∀ x : FzSigma4, x ^ 3 = 1 → x ≠ 1 →
        (∃ g, g * x * g⁻¹ = fz21b_C012) ∧ (∃ g, g * x * g⁻¹ = fz21b_C013)) (y : FzSigma4) h3pow h3ne
    obtain ⟨⟨g1, hg1⟩, ⟨g2, hg2⟩⟩ := hconj
    have hC1 : fz21b_C012 ∈ M := hg1 ▸ hM.conj_mem (y : FzSigma4) hyM g1
    have hC2 : fz21b_C013 ∈ M := hg2 ▸ hM.conj_mem (y : FzSigma4) hyM g2
    exact key (fz21b_C012 * fz21b_C013) (by decide) (M.mul_mem hC1 hC2)
  · obtain ⟨h4pow, h4ne⟩ := h4
    have hd : IsDbl ((y : FzSigma4) ^ 2) :=
      (by decide : ∀ x : FzSigma4, x ^ 4 = 1 → x ^ 2 ≠ 1 → IsDbl (x ^ 2)) _ h4pow h4ne
    have hy2M : (y : FzSigma4) ^ 2 ∈ M := by
      have : (y : FzSigma4) * (y : FzSigma4) ∈ M := M.mul_mem hyM hyM
      simpa [pow_two] using this
    exact key ((y : FzSigma4) ^ 2) hd hy2M

lemma fz21b_range_card_le_two {G : Type*} [CommGroup G] (H : Subgroup G) (A : Subgroup H)
    (hcard : Nat.card (H ⧸ A) = 2) (ψ : H →* G) (hker : A ≤ ψ.ker) :
    Nat.card ψ.range ≤ 2 := by
  let ψ' : H ⧸ A →* G := QuotientGroup.lift A ψ hker
  have hcomp : ψ'.comp (QuotientGroup.mk' A) = ψ := QuotientGroup.lift_comp_mk' A ψ hker
  have hrange : ψ.range = ψ'.range := by
    rw [← hcomp, MonoidHom.range_comp, QuotientGroup.range_mk', Subgroup.map_top]
  haveI : Finite (H ⧸ A) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  calc Nat.card ψ.range = Nat.card ψ'.range := by rw [hrange]
    _ ≤ Nat.card (H ⧸ A) :=
        Nat.card_le_card_of_surjective ψ'.rangeRestrict ψ'.rangeRestrict_surjective
    _ = 2 := hcard

open scoped IsMulCommutative

lemma fz21b_hword_V : ∀ a b : FzSigma4, a ^ 3 = 1 → b ^ 2 = 1 → b * a * b⁻¹ = a⁻¹ →
    a ≠ 1 → ∀ i : Fin 3, ∀ j : Fin 2, b ^ (j : ℕ) * a ^ (i : ℕ) = 1 ∨
      b ^ (j : ℕ) * a ^ (i : ℕ) = fz21b_D1 ∨ b ^ (j : ℕ) * a ^ (i : ℕ) = fz21b_D2 ∨
      b ^ (j : ℕ) * a ^ (i : ℕ) = fz21b_D3 → i = 0 ∧ j = 0 := by decide
lemma fz21b_hVtrace : ∀ c v : FzSigma4, c ^ 3 = 1 → c ≠ 1 →
    (v = 1 ∨ v = fz21b_D1 ∨ v = fz21b_D2 ∨ v = fz21b_D3) →
    v * (c * v * c⁻¹) * (c * (c * v * c⁻¹) * c⁻¹) = 1 := by decide +kernel

lemma fz21b_hword_ne' : ∀ a b : FzSigma4, a ^ 3 = 1 → b ^ 2 = 1 → b * a * b⁻¹ = a⁻¹ →
    a ≠ 1 → ∀ i : Fin 3, ∀ j : Fin 2, ∀ k : Fin 3, ∀ l : Fin 2,
      b ^ (j : ℕ) * a ^ (i : ℕ) = b ^ (l : ℕ) * a ^ (k : ℕ) → i = k ∧ j = l := by decide

end CFSG.OddStandard.SmallF3.FritzII
