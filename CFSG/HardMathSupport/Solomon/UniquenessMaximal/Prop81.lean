module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma82
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem prop81Core_of_inputs (i7 : Coordinator.I_7_13_1_OuterPPrime) (i10 : Input10_20_3) (iodd : InputOddTwoLocal)
    (i33 : Input33_4) (iU : InputUExists) (i11 : Input11_3) (i5 : Input28_5)
    (i14 : Input28_14) (it : InputMcLaughlinTypeFacts) : Prop81Core := by
  intro G _ _ m p hS B M₀ hB hM
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBM : B ≤ M₀ := hM.le hS hB
  have h82 : ∀ N : Subgroup G, IsTwoLocal N → B ≤ N → ∀ J : Subgroup G,
      GLAPComponent 2 (GLAPPrimeCoreOf p M₀) J →
        ¬ J ≤ (N ⊓ GLAPPrimeCoreOf p M₀) ⊔ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) :=
    fun N hN hBN J hJ => lemma82 hS hB hM hN hBN hJ
  have h83 : ∀ b ∈ B, (∀ y ∈ layerPreimage (GLAPPrimeCoreOf p M₀),
      b * y * b⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀)) → b = 1 :=
    fun b hb hc => lemma83 hS hB hM hb hc
  have h84 : GLAPLayer 2 (GLAPPrimeCoreOf p M₀) = ⊥ := lemma84 i7 i10 iodd hS hB hM h82 h83
  set X := GLAPPrimeCoreOf p M₀ with hX
  set R := oTwoPrimeTwo X with hR
  have hM₀X : M₀ ≤ Subgroup.normalizer (X : Set G) := le_normalizer_glaPPrimeCoreOf p M₀
  have hBR : B ≤ Subgroup.normalizer (R : Set G) :=
    hBM.trans (Lemma85Aux.normalizer_le_oTwoPrimeTwo hM₀X)
  have hRX : R ≤ X := Lemma85Aux.oTwoPrimeTwo_le X
  have hRcop : ¬ p ∣ Nat.card R := fun h =>
    not_dvd_card_glaPPrimeCoreOf hp M₀ (h.trans (Subgroup.card_dvd_of_le hRX))
  have hBp : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hB.1.1.2 g g.2)⟩
  obtain ⟨Q, hQR, hQ2, hQc, hBQ⟩ :=
    exists_sylow_normalized_of_not_dvd (p := p) (q := 2) R B hBp hBR hRcop
  have hQmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ R → IsPGroup 2 Q' → Q' = Q := by
    intro Q' hQQ' hQ'R hQ'2
    obtain ⟨k, hk⟩ := hQ'2.exists_card_eq
    have h1 : 2 ^ k ∣ Nat.card R := hk ▸ Subgroup.card_dvd_of_le hQ'R
    have h2 := hQc k h1
    exact (Subgroup.eq_of_le_of_card_ge hQQ' (hk ▸ Nat.le_of_dvd (Nat.card_pos) h2)).symm
  obtain ⟨P, hPQ⟩ := hQ2.exists_le_sylow
  obtain ⟨U, hU⟩ := iU G m p hS P
  have h85 := fun (P' : Sylow 2 G) (U' : Subgroup G) (hP' : Q ≤ (P' : Subgroup G))
      (hU' : IsUGroup 2 (P' : Subgroup G) U') =>
    lemma85 i33 hS hB hM h84 hQ2 hQR hQmax hBQ hP' hU'
  obtain ⟨hQ0, hQeq, hUN, -⟩ := h85 P U hPQ hU
  exact lemma86 i11 i5 i14 it hS hB hM hQ0 hQeq hBQ hPQ hU hUN
    (fun P' U' hP' hU' _ h => (h85 P' U' hP' hU').2.2.2 h)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
