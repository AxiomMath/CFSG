module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossSL2Grp
public import CFSG.GH74.GLS.Stage4.HexCSL2
public import CFSG.RankThree.PartOne.FTL.Frattini

public section

open Subgroup CFSG CFSG.GH74.GLS.Stage4.Hex CFSG.OrderReductions.FrattiniAutomorphisms CFSG.RankThree.PartOne.FTL
open scoped commutatorElement IsMulCommutative

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Triv

variable {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

theorem sl2L_pow {F : Type} [Field F] (c : F) (n : ℕ) : sl2L c ^ n = sl2L (n • c) := by
  induction n with
  | zero => simp [sl2L_zero]
  | succ n ih => rw [pow_succ, ih, ← sl2L_add, succ_nsmul]

theorem centralizes_of_frattiniRepOf_eq_one {F : Type} [Field F] [Finite F]
    (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A) {X : Subgroup A} [Fact (IsPGroup p X)]
    (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) {e : SL2 F} (he : e ^ Nat.card F = 1)
    (hρ : frattiniRepOf (p := p) ι X hnorm e = 1) : ι e ∈ centralizer (X : Set A) := by
  let _ := conjActOfHom ι X hnorm
  let ψ : SL2 F →* MulAut ↥X := MulDistribMulAction.toMulAut (SL2 F) ↥X
  have hψ : ∀ (x : ↥X), ((ψ e x : ↥X) : A) = ι e * x * (ι e)⁻¹ := fun x => rfl
  have hτ : (ψ e) ^ Nat.card F = 1 := by rw [← map_pow, he, map_one]
  have hcop : Nat.Coprime (Nat.card F) p :=
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpq).symm
  have htriv : quotientAutomorphism (frattini ↥X) (ψ e) = 1 := by
    rw [← MonoidHom.mem_ker, mem_quotientAutomorphism_kernel]
    intro x
    have h1 := congrArg (fun f : Module.End (ZMod p) (Additive (↥X ⧸ frattini ↥X)) =>
      f (Additive.ofMul (x : ↥X ⧸ frattini ↥X))) hρ
    simp only [Module.End.one_apply] at h1
    rw [frattiniRepOf_apply_mk] at h1
    exact Additive.ofMul.injective h1
  have h1 : ψ e = 1 := eq_one_of_trivial_mod_frattini (Fact.out : IsPGroup p ↥X) hτ hcop htriv
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg (fun τ : MulAut ↥X => ((τ ⟨x, hx⟩ : ↥X) : A)) h1
  simp only [hψ, MulAut.one_apply] at this
  calc x * ι e = (ι e * x * (ι e)⁻¹) * ι e := by rw [this]
    _ = ι e * x := by group

theorem sl2_centralizes_or_large (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hpq : ¬ p ∣ Nat.card F) (ι : SL2 F →* A)
    {X : Subgroup A} (hX : IsPGroup p ↥X) (hnorm : ∀ g, ι g ∈ normalizer (X : Set A)) :
    (∀ g, ∀ x ∈ X, ι g * x = x * ι g) ∨ (Nat.card F - 1) / 2 ≤ padicValNat p (Nat.card X) := by
  have _ : p ≠ 2 ∧ Odd (Nat.card F) ∧ 5 ≤ Nat.card F := ⟨hp2, hodd, h5⟩
  have : Fact (IsPGroup p X) := ⟨hX⟩
  by_cases hU : ∃ c : F, frattiniRepOf (p := p) ι X hnorm (sl2U c) ≠ 1
  · right
    have h1 := sl2_cross_dim_of_unip (Fact.out : p.Prime) hpq (frattiniRepOf (p := p) ι X hnorm) hU
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Additive (↥X ⧸ frattini ↥X))
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive (↥X ⧸ frattini ↥X) ≃ _)] at hcard
    have hdvd : p ^ Module.finrank (ZMod p) (Additive (↥X ⧸ frattini ↥X)) ∣ Nat.card X :=
      hcard ▸ Subgroup.card_quotient_dvd_card (frattini ↥X)
    exact h1.trans ((padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd)
  · left
    push Not at hU
    have hL : ∀ c : F, frattiniRepOf (p := p) ι X hnorm (sl2L c) = 1 := by
      intro c
      rw [sl2L_eq_conj, map_mul, map_mul, hU (-c), mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hpowU : ∀ c : F, sl2U c ^ Nat.card F = 1 := by
      intro c
      rw [CFSG.GH74.GLS.Stage4.Rest.sl2U_pow, card_nsmul_eq_zero', sl2U_zero]
    have hpowL : ∀ c : F, sl2L c ^ Nat.card F = 1 := by
      intro c
      rw [sl2L_pow, card_nsmul_eq_zero', sl2L_zero]
    have hmem := sl2_hom_mem ι (centralizer (X : Set A))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowU c) (hU c))
      (fun c => centralizes_of_frattiniRepOf_eq_one hpq ι hnorm (hpowL c) (hL c))
    intro g x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hmem g)) x hx).symm

end Triv

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
