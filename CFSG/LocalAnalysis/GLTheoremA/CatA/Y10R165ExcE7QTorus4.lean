module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7QTorus2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7QTorus3

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Open CFSG.RankThree.Classical2
open scoped MatrixGroups Pointwise

section Split

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem exists_elemAbelian_pRank_three_of_a5Layer_split
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ Nat.card K - 1 ∨ Nat.card K = 2 ∧ q = 3) :
    ∃ F : Subgroup J, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  by_cases h : q ∣ Nat.card K - 1
  · exact exists_elemAbelian_pRank_three_of_fixSubgroup_split hfix ρ hρ hc hk hq hq2 h
  · obtain ⟨hK2, hq3⟩ := hdiv.resolve_left h
    subst hq3
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [← Nat.card_eq_fintype_card, hK2]
      norm_num)
    exact exists_elemAbelian_pRank_three_of_fixSubgroup_split_f2 hfix hK2 ρ hρ hc hk

end Split

section Unitary

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_elemAbelian_pRank_three_of_a5Layer_unitary
    (hℓ2 : ℓ = 2) (hK : Nat.card K = ℓ ^ f)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ Nat.card K - 1) :
    ∃ F : Subgroup J, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F :=
  exists_elemAbelian_pRank_three_of_fixSubgroup_unitary hℓ2 hK hfix ρ hρ hc hk hq hq2 hdiv

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
