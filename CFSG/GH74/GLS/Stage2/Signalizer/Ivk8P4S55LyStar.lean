module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtModel
public import CFSG.Sporadic.Ly.TwoWeightsSpecBase
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtApply

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

open Subgroup CFSG.GroupTheory.TwoWeights CFSG.Sporadic.Recognition.LyonsSims

theorem ly_not_pow_dvd {p : ℕ} (hp : 3 ≤ p) : ¬ p ^ 8 ∣ 51765179004000000 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hp123 : p < 123 := by
    by_contra h1
    have h2 : 123 ^ 8 ≤ p ^ 8 := Nat.pow_le_pow_left (by omega) 8
    omega
  interval_cases p <;> omega

theorem ly_central
    {Y : Type} [Group Y] [Finite Y]
    (hY : Blueprint.NativeSporadic.IsSporadic Y .Ly) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A X : Subgroup Y} (hA : Nat.card ↥A = 2 ^ 8) {τ : Y} (hτA : τ ∈ A) (hτ2 : orderOf τ = 2)
    (hτc : ∀ g ∈ A, g * τ = τ * g) (hX : IsPGroup p ↥X)
    (hN : A ≤ normalizer (X : Set Y)) : X ≤ centralizer ({τ} : Set Y) := by
  obtain ⟨eT⟩ := hY
  have hcardY : Nat.card Y = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly'
  have hfact : (Nat.card Y).factorization 2 = 8 := by
    rw [hcardY, show (51765179004000000 : ℕ) = 2 ^ 8 * 202207730484375 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hconj : ∀ u v : Y, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    isConj_of_equiv_of_involutions eT (fun u v hu hv => ly_isConj_of_involutions hu hv) hu hv
  have e1 : Y ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  have hD := CFSG.Sporadic.Ly.two_weight_rels
  have ha2 := CFSG.Sporadic.Ly.orderOf_a
  obtain ⟨u₁, u₂, u₃, x, y, hu₁, hu₂, hu₃, hx, hy, D⟩ :=
    @exists_data_of_model Y CFSG.Sporadic.Ly.J _ _ inferInstance e1 hconj 8 hfact _ _ _ _ _ _ ha2 hD
      _ hA _ hτA hτ2 hτc
  have hsmall : Nat.card ↥X < p ^ 8 :=
    card_lt_pow_eight hp2 hcardY (fun q hq => ly_not_pow_dvd hq) hX
  exact central_of_data hp2 D hτA hu₁ hu₂ hu₃ hx hy hX hN hsmall

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP
