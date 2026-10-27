module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

theorem hsAut_exists_mulAut_pair {W : Type} [Group W] [Finite W] (hW : Nat.card W = 8)
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ w : W, w * w = 1)
    {a b a' b' : W} (ha : a ≠ 1) (ha' : a' ≠ 1) (hb : b ∉ Subgroup.zpowers a)
    (hb' : b' ∉ Subgroup.zpowers a') :
    ∃ σ : MulAut W, σ a = a' ∧ σ b = b' := by
  have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact hsq _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  have hcard : Nat.card (Additive W) = 8 := by
    rw [Nat.card_congr (Additive.toMul : Additive W ≃ W)]
    exact hW
  have hrank : Module.finrank (ZMod 2) (Additive W) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod, hcard] at h
    have h' : 2 ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ 3 := by
      rw [← h]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  have key : ∀ {x y : W}, x ≠ 1 → y ∉ Subgroup.zpowers x →
      ∃ B : Module.Basis (Fin 3) (ZMod 2) (Additive W),
        B 1 = Additive.ofMul x ∧ B 2 = Additive.ofMul y := by
    intro x y hx hy
    have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
    have hyx : y ≠ x := fun h => hy (h ▸ Subgroup.mem_zpowers _)
    have hli : LinearIndependent (ZMod 2) ![Additive.ofMul x, Additive.ofMul y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exfalso
        simp only [zero_smul, one_smul, zero_add] at hst
        exact hy1 (toMul_eq_one.mpr hst)
      · exfalso
        simp only [zero_smul, one_smul, add_zero] at hst
        exact hx (toMul_eq_one.mpr hst)
      · exfalso
        simp only [one_smul] at hst
        have h3 := congrArg Additive.toMul hst
        rw [toMul_add, toMul_zero, toMul_ofMul, toMul_ofMul] at h3
        exact hyx ((eq_inv_of_mul_eq_one_right h3).trans (inv_eq_of_mul_eq_one_right (hsq x)))
    have hspan : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range ![Additive.ofMul x, Additive.ofMul y])) = 2 := by
      rw [finrank_span_eq_card hli]
      simp
    obtain ⟨c, hc⟩ : ∃ c : Additive W,
        c ∉ Submodule.span (ZMod 2) (Set.range ![Additive.ofMul x, Additive.ofMul y]) := by
      by_contra hcon
      have htop : Submodule.span (ZMod 2)
          (Set.range ![Additive.ofMul x, Additive.ofMul y]) = ⊤ :=
        eq_top_iff.mpr fun u _ => not_not.mp fun hu => hcon ⟨u, hu⟩
      rw [htop, finrank_top, hrank] at hspan
      omega
    have hl : LinearIndependent (ZMod 2) ![c, Additive.ofMul x, Additive.ofMul y] :=
      linearIndependent_fin_cons.mpr ⟨hli, hc⟩
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp [hrank]), ?_, ?_⟩ <;>
      simp
  obtain ⟨B, hB1, hB2⟩ := key ha hb
  obtain ⟨B', hB1', hB2'⟩ := key ha' hb'
  let e : Additive W ≃ₗ[ZMod 2] Additive W := B.equiv B' (Equiv.refl (Fin 3))
  refine ⟨MulEquiv.toAdditive.symm e.toAddEquiv, ?_, ?_⟩
  · have h1 : e (B 1) = B' 1 := by simp [e]
    rw [hB1, hB1'] at h1
    exact h1
  · have h1 : e (B 2) = B' 2 := by simp [e]
    rw [hB2, hB2'] at h1
    exact h1

end CFSG.GF2Type.Aschbacher1976Full.HS
