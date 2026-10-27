module

public import CFSG.GH74.SmallRanks

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup

variable {Y : Type*} [Group Y]

theorem pow_val_add {x : Y} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · rw [add_zero, hv0, pow_zero, one_mul]
  · rw [zero_add, hv0, pow_zero, one_mul]
  · rw [add_zero, hv0, pow_zero, mul_one]
  · rw [h11, hv0, hv1, pow_zero, pow_one, hx]

@[expose] def e8Hom (x₁ x₂ x₃ : Y) (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : x₃ * x₃ = 1)
    (h₁₂ : Commute x₁ x₂) (h₁₃ : Commute x₁ x₃) (h₂₃ : Commute x₂ x₃) :
    Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) →* Y where
  toFun v := x₁ ^ (Multiplicative.toAdd v).1.val *
    (x₂ ^ (Multiplicative.toAdd v).2.1.val * x₃ ^ (Multiplicative.toAdd v).2.2.val)
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_val_add h₁, pow_val_add h₂,
      pow_val_add h₃, mul_assoc]
    congr 1
    set A' := x₁ ^ (Multiplicative.toAdd w).1.val
    set B := x₂ ^ (Multiplicative.toAdd v).2.1.val
    set B' := x₂ ^ (Multiplicative.toAdd w).2.1.val
    set C := x₃ ^ (Multiplicative.toAdd v).2.2.val
    set C' := x₃ ^ (Multiplicative.toAdd w).2.2.val
    have hA'B : Commute A' B := (h₁₂.pow_pow _ _)
    have hA'C : Commute A' C := (h₁₃.pow_pow _ _)
    have hB'C : Commute B' C := (h₂₃.pow_pow _ _)
    calc A' * (B * (B' * (C * C'))) = B * (A' * (B' * (C * C'))) := hA'B.left_comm _
      _ = B * (A' * (C * (B' * C'))) := by rw [hB'C.left_comm]
      _ = B * (C * (A' * (B' * C'))) := by rw [hA'C.left_comm]

theorem e8Hom_apply (x₁ x₂ x₃ : Y) (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : x₃ * x₃ = 1)
    (h₁₂ : Commute x₁ x₂) (h₁₃ : Commute x₁ x₃) (h₂₃ : Commute x₂ x₃) (a b c : ZMod 2) :
    e8Hom x₁ x₂ x₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (Multiplicative.ofAdd (a, b, c)) =
      x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val) := rfl

theorem three_le_twoRank [Finite Y] (x₁ x₂ x₃ : Y) (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1)
    (h₃ : x₃ * x₃ = 1) (h₁₂ : Commute x₁ x₂) (h₁₃ : Commute x₁ x₃) (h₂₃ : Commute x₂ x₃)
    (hind : ∀ a b c : ZMod 2, x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val) = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    3 ≤ Open.twoRank Y := by
  set φ := e8Hom x₁ x₂ x₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    obtain ⟨⟨a, b, c⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
    obtain ⟨rfl, rfl, rfl⟩ := hind a b c hv
    rfl
  have hE : Open.IsElemAbelian 2 φ.range := by
    refine ⟨?_, ?_⟩
    · rw [MonoidHom.range_eq_map]
      exact Subgroup.map_isMulCommutative _ φ
    · rintro _ ⟨v, rfl⟩
      rw [← map_pow]
      have hv : v ^ 2 = 1 := by
        have h2 : ∀ w : ZMod 2 × ZMod 2 × ZMod 2, w + w = 0 := by decide
        rw [sq]
        change Multiplicative.ofAdd (Multiplicative.toAdd v + Multiplicative.toAdd v) = 1
        rw [h2]
        rfl
      rw [hv, map_one]
  have hcard : Nat.card φ.range = 2 ^ 3 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
    simp
  exact TwoRankLowerBound.Helpers.le_twoRank_of_elementary Y φ.range hE 3 hcard

theorem false_of_lieModel_psl_two {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y .PSL 2 p f) (x₁ x₂ x₃ : Y) (h₁ : x₁ * x₁ = 1)
    (h₂ : x₂ * x₂ = 1) (h₃ : x₃ * x₃ = 1) (h₁₂ : Commute x₁ x₂) (h₁₃ : Commute x₁ x₃)
    (h₂₃ : Commute x₂ x₃)
    (hind : ∀ a b c : ZMod 2, x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val) = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) : False := by
  have h1 := three_le_twoRank x₁ x₂ x₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hind
  have h2 := GH74.twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 hY
  omega

theorem mk_ne_one_of_involution {L : Type*} [Group L] [Finite L] {x : L} (hx : x * x = 1)
    (hx1 : x ≠ 1) : (QuotientGroup.mk x : L ⧸ pPrimeCore 2 L) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx) hx1
  have hdvd : orderOf (⟨x, h⟩ : pPrimeCore 2 L) ∣ Nat.card (pPrimeCore 2 L) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 L)) := pPrimeCore_coprime_card
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

theorem independent_quotient_pPrimeCore {L : Type*} [Group L] [Finite L] (x₁ x₂ x₃ : L)
    (h₁ : x₁ * x₁ = 1) (h₂ : x₂ * x₂ = 1) (h₃ : x₃ * x₃ = 1) (h₁₂ : Commute x₁ x₂)
    (h₁₃ : Commute x₁ x₃) (h₂₃ : Commute x₂ x₃)
    (hind : ∀ a b c : ZMod 2, x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val) = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) (a b c : ZMod 2) :
    (QuotientGroup.mk x₁ : L ⧸ pPrimeCore 2 L) ^ a.val *
        ((QuotientGroup.mk x₂ : L ⧸ pPrimeCore 2 L) ^ b.val *
          (QuotientGroup.mk x₃ : L ⧸ pPrimeCore 2 L) ^ c.val) = 1 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  intro h
  set y := x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val)
  have hy : y * y = 1 := by
    have := map_mul (e8Hom x₁ x₂ x₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) (Multiplicative.ofAdd (a, b, c))
      (Multiplicative.ofAdd (a, b, c))
    rw [← ofAdd_add] at this
    have h2 : (a, b, c) + (a, b, c) = (0 : ZMod 2 × ZMod 2 × ZMod 2) := by
      have h2' : ∀ w : ZMod 2 × ZMod 2 × ZMod 2, w + w = 0 := by decide
      exact h2' _
    rw [h2, ofAdd_zero, map_one, e8Hom_apply] at this
    exact this.symm
  have hmk : (QuotientGroup.mk y : L ⧸ pPrimeCore 2 L) = 1 := by
    simpa only [y, QuotientGroup.mk_mul, QuotientGroup.mk_pow] using h
  by_contra hne
  have hy1 : y ≠ 1 := fun h1 => hne (hind a b c h1)
  exact mk_ne_one_of_involution hy hy1 hmk

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
