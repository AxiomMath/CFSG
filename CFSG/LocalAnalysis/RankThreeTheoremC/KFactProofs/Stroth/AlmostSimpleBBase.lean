module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleSignalizer
public import CFSG.LocalAnalysis.GL83PartI.I_33
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Burnside

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC

section Witness

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_inf_centralizer {p : ℕ} {D T A : Subgroup X} (hD : IsElemAbelian p D)
    (hAD : A ≤ D) (hDT : D ≤ normalizer (T : Set X)) :
    D ≤ normalizer ((T ⊓ centralizer (A : Set X) : Subgroup X) : Set X) := by
  have hDcomm : ∀ b ∈ D, ∀ a ∈ A, Commute a b := fun b hb a ha =>
    CFSG.Open.IsElemAbelian.comm hD (hAD ha) hb
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hbT := Subgroup.mem_normalizer_iff.1 (hDT hb) h
  constructor
  · rintro ⟨hhT, hhC⟩
    exact ⟨hbT.1 hhT, GL83.mul_mul_inv_mem_centralizer_of_commute (hDcomm b hb) hhC⟩
  · rintro ⟨hhT, hhC⟩
    refine ⟨hbT.2 hhT, ?_⟩
    have := GL83.mul_mul_inv_mem_centralizer_of_commute (A := A) (b := b⁻¹)
      (h := b * h * b⁻¹) (fun a ha => (hDcomm b hb a ha).inv_right) hhC
    simpa [mul_assoc] using this

end Witness

section Centralized

variable {X : Type} [Group X] [Finite X]

theorem le_centralizer_of_invariantTwo {p : ℕ} {L D : Subgroup X} [L.Normal]
    (hF : ThompsonFrame p D)
    (hc : ∀ a ∈ D, a ≠ 1 → ∀ S : Subgroup X,
      S ≤ relPPrimeCore p (L ⊓ centralizer ({a} : Set X)) → IsPGroup 2 S →
      D ≤ normalizer (S : Set X) → ⁅S, D⁆ = ⊥)
    {T : Subgroup X} (hTL : T ≤ L) (hT2 : IsPGroup 2 T) (hDT : D ≤ normalizer (T : Set X)) :
    T ≤ centralizer (D : Set X) := by
  have hp := hF.prime
  have hp2 := hF.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hDne : D ≠ ⊥ := by
    intro h
    have hcard := hF.card
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hgen := GL83.le_iSup_hyperplane hp hp2 hDne hF.elem hT2 hDT
  refine hgen.trans (iSup₂_le fun A hA => ?_)
  have hAne : A ≠ ⊥ := by
    rintro rfl
    have hAi := hA.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, hF.card] at hAi
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hAne ((Subgroup.eq_bot_iff_forall A).2 hcon)
  have hDY : D ≤ normalizer ((T ⊓ centralizer (A : Set X) : Subgroup X) : Set X) :=
    le_normalizer_inf_centralizer hF.elem hA.1 hDT
  have hY2 : IsPGroup 2 (T ⊓ centralizer (A : Set X) : Subgroup X) := hT2.to_le inf_le_left
  have hYL : T ⊓ centralizer (A : Set X) ≤ L ⊓ centralizer ({a} : Set X) :=
    le_inf (inf_le_left.trans hTL)
      (inf_le_right.trans (Subgroup.centralizer_le (by simpa using haA)))
  have hYR : T ⊓ centralizer (A : Set X) ≤ relPPrimeCore p (L ⊓ centralizer ({a} : Set X)) :=
    (le_invariantTwoJoinIn hYL hY2 hDY).trans
      (invariantTwoJoin_le_relPPrimeCore hF (hA.1 haA) ha1)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hc a (hA.1 haA) ha1 _ hYR hY2 hDY)

end Centralized

section Burnside

variable {X : Type} [Group X] [Finite X]

theorem not_dvd_card_invariantTwoJoin_of_centralizes {p : ℕ} {L D : Subgroup X}
    (hF : ThompsonFrame p D)
    (hall : ∀ T : Subgroup X, T ≤ L → IsPGroup 2 T → D ≤ normalizer (T : Set X) →
      T ≤ centralizer (D : Set X)) :
    ¬ p ∣ Nat.card (invariantTwoJoinIn D L) := by
  have hp := hF.prime
  have hp2 := hF.odd
  obtain ⟨Q, -, hQcop, -, hQ⟩ := exists_normal_pComplement_centralizer hp hF.elem.1 hF.sylow
  have hle : invariantTwoJoinIn D L ≤ Q := by
    refine invariantTwoJoinIn_le_of_forall fun T hTL hT2 hDT t ht => ?_
    refine hQ t (hall T hTL hT2 hDT ht) ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨t, ht⟩
    have hk' : orderOf t = 2 ^ k := (Subgroup.orderOf_coe ⟨t, ht⟩).trans hk
    rw [hk']
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  intro hdvd
  have h1 : p ∣ Nat.card Q := hdvd.trans (Subgroup.card_dvd_of_le hle)
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hQcop h1)

end Burnside

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
