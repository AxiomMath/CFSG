module

public import CFSG.HardMathSupport.Lang.AnisoF4.B4Even
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Arith
public import CFSG.HardMathSupport.Lang.AnisoF4.B4SylowConj
public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration
  CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false


theorem factorization_card_F4_le_card_b4_even {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1) :
    (Nat.card (adjointGroup .F4 K)).factorization p ≤
      (Nat.card ↥(⨆ k, b4Chain K k)).factorization p := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨Ψ, -, -, -, hlie⟩ := exists_psi_B4_F4_frame_even hK hK4
  set X := ⨆ k, b4Chain K k with hX
  have hn0 : n.val ≠ 0 := by
    rintro h
    rw [h, pow_zero] at hK
    omega
  have hcardQ : Nat.card (↥X ⧸ Subgroup.center ↥X) = CFSG.Open.ordBC 4 (Nat.card K) := by
    rcases hlie with ⟨-, hc⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hc
      haveI : Fintype K' := Fintype.ofFinite K'
      have : CharP K' 2 := charP_of_card_eq_prime_pow (p := 2) (f := n.val)
        (by rw [← Nat.card_eq_fintype_card, hK', ← hK])
      have hKK : Nat.card K' = Nat.card K := by rw [hK', hK]
      have hg : Nat.gcd 2 (Nat.card K - 1) = 1 := by
        refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
        have h2 : 2 ∣ 2 ^ n.val := dvd_pow_self 2 hn0
        have h4 : 4 ≤ 2 ^ n.val := hK ▸ hK4
        rw [hK]
        omega
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hKK,
        CFSG.Open.ordBC, hg, Nat.div_one]
      norm_num
    all_goals exact absurd h0 (by norm_num)
  have hdvd : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card X :=
    ⟨Nat.card (Subgroup.center ↥X), by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  have hKq : 2 ≤ Nat.card K := by omega
  calc (Nat.card (adjointGroup .F4 K)).factorization p
      = (CFSG.Open.ordF4 (Nat.card K)).factorization p := by
        rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    _ ≤ (CFSG.Open.ordBC 4 (Nat.card K)).factorization p :=
        factorization_ordF4_le_ordBC hp hp5 hKq hpq
    _ = (Nat.card (↥X ⧸ Subgroup.center ↥X)).factorization p := by rw [hcardQ]
    _ ≤ (Nat.card X).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p

theorem exists_conj_plane_b4_even {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1)
    {e : adjointGroup .F4 K} (he : e ∈ ⨆ k, b4Chain K k) (heo : orderOf e = p)
    (E₀ : Subgroup (adjointGroup .F4 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hE₀c : Nat.card E₀ = p ^ 2) :
    ∃ g : adjointGroup .F4 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, b4Chain K k ∧
      e ∈ E₀.map (MulAut.conj g).toMonoidHom := by
  have hT : SylowTorus (adjointGroup .F4 K) p 2 := sylowTorus_F4_four K hp.out (by omega) hpq
  have hE₀el : CFSG.Open.IsElemAbelian p E₀ :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.mul_comm_of_sylowTorus hT
        (IsPGroup.of_card (n := 2) hE₀c) a.2 b.2), fun x hx => hE₀p x hx⟩
  exact exists_conj_plane_le_of_factorization hT _
    (factorization_card_F4_le_card_b4_even hK4 hp.out hp5 hpq) he heo hE₀el hE₀c

end CFSG.HardMathSupport.Lang.AnisoF4
