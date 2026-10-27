module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Reg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Idx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

variable {D : Data} [Group Y63TG]

theorem y63_inv_val (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) (x : Y63TG) : (x⁻¹).val = D.iv x.val := by
  obtain ⟨hlt, hx⟩ := hI x.val x.lt
  have hxy : x * (⟨D.iv x.val, hlt⟩ : Y63TG) = 1 := Y63TG.ext (by rw [hmul, h1]; exact hx)
  have := eq_inv_of_mul_eq_one_right hxy
  rw [← this]

theorem y63_pow4_val (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val) (x : Y63TG) :
    (x ^ 4).val = D.pow4 x.val := by
  rw [show x ^ 4 = (x * x) * (x * x) by simp only [pow_succ, pow_zero, one_mul, mul_assoc], hmul,
    hmul, Data.pow4]

theorem y63_M_eq (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hM : D.MSpec) (M₁ : Subgroup Y63TG) (hcard : Nat.card M₁ = 64)
    (h4 : ∀ x ∈ M₁, x ^ 4 = 1) (hcomm : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y = y * x) :
    ∀ x : Y63TG, x ∈ M₁ ↔ x.val ∈ D.m0 := by
  classical
  have hM' := hM
  obtain ⟨hnd, hlen, -, -, -, -, -⟩ := hM'
  obtain ⟨A, hAdef⟩ : ∃ A : Finset ℕ,
      A = (Finset.univ.filter (fun x : Y63TG => x ∈ M₁)).image Y63TG.val := ⟨_, rfl⟩
  have hAmem : ∀ a, a ∈ A ↔ ∃ x ∈ M₁, x.val = a := by
    intro a
    simp [hAdef]
  have hAcard : A.card = 64 := by
    rw [hAdef, Finset.card_image_of_injective _ (fun x y h => Y63TG.ext h), ← hcard,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hAlt : ∀ a ∈ A, a < 512 := fun a ha => by
    obtain ⟨x, -, rfl⟩ := (hAmem a).mp ha
    exact x.lt
  have hA4 : ∀ a ∈ A, D.pow4 a = 0 := fun a ha => by
    obtain ⟨x, hx, rfl⟩ := (hAmem a).mp ha
    rw [← y63_pow4_val hmul x, h4 x hx, h1]
  have hAc : ∀ a ∈ A, ∀ b ∈ A, D.mt a b = D.mt b a := fun a ha b hb => by
    obtain ⟨x, hx, rfl⟩ := (hAmem a).mp ha
    obtain ⟨y, hy, rfl⟩ := (hAmem b).mp hb
    rw [← hmul, ← hmul, hcomm x hx y hy]
  have hsub := y63_idx_M D hM hAcard hAlt hA4 hAc
  intro x
  constructor
  · intro hx
    exact hsub x.val ((hAmem _).mpr ⟨x, hx, rfl⟩)
  · intro hx
    have hEq : A = D.m0.toFinset :=
      Finset.eq_of_subset_of_card_le (fun a ha => List.mem_toFinset.mpr (hsub a ha))
        (by rw [List.toFinset_card_of_nodup hnd, hlen, hAcard])
    have hxA : x.val ∈ A := by rw [hEq]; exact List.mem_toFinset.mpr hx
    obtain ⟨y, hy, hyx⟩ := (hAmem _).mp hxA
    rwa [Y63TG.ext hyx] at hy

end CFSG.OddStandard.HigherRank.YamadaG23
