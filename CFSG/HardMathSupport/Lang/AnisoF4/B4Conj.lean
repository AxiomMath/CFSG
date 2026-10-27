module

public import CFSG.HardMathSupport.Lang.AnisoF4.B4Arith
public import CFSG.HardMathSupport.Lang.AnisoF4.B4SylowConj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameB4
public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.ClassicalInvolution.Orders.Orthogonal

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem factorization_card_F4_le_card_b4 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1) :
    (Nat.card (adjointGroup .F4 K)).factorization p ≤
      (Nat.card ↥(⨆ k, b4Chain K k)).factorization p := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hℓ2 : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    simpa using this)
  have hKq : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  obtain ⟨Ψ, -, -, -, hlie⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
  set X := ⨆ k, b4Chain K k with hX
  have hcardQ : Nat.card (↥X ⧸ Subgroup.center ↥X) = CFSG.Open.ordBC 4 (Nat.card K) := by
    rcases hlie with ⟨-, hc⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hc
      rw [Nat.card_congr e.toEquiv,
        ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC hℓ hℓ2 hK' (by norm_num),
        ← hK]
    all_goals exact absurd h0 (by norm_num)
  have hdvd : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ Nat.card X :=
    ⟨Nat.card (Subgroup.center ↥X), by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
  calc (Nat.card (adjointGroup .F4 K)).factorization p
      = (CFSG.Open.ordF4 (Nat.card K)).factorization p := by
        rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4]
    _ ≤ (CFSG.Open.ordBC 4 (Nat.card K)).factorization p :=
        factorization_ordF4_le_ordBC hp hp5 hKq hpq
    _ = (Nat.card (↥X ⧸ Subgroup.center ↥X)).factorization p := by rw [hcardQ]
    _ ≤ (Nat.card X).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p

theorem exists_conj_plane_b4 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {p : ℕ}
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
    (factorization_card_F4_le_card_b4 h2 hp.out hp5 hpq) he heo hE₀el hE₀c

end CFSG.HardMathSupport.Lang.AnisoF4
