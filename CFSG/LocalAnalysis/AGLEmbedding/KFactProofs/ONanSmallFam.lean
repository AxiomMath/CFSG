module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

@[expose] def SylowSq (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ T : Sylow p K, Nat.card T = p ^ 2

@[expose] def SylowCube (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ T : Sylow p K, Nat.card T = p ^ 3 ∧ ∀ t ∈ (T : Subgroup K), t ^ p = 1

section Transport

variable {K L : Type} [Group K] [Group L] [Finite K]

theorem sylow_card_of_factorization {p a : ℕ} (hp : p.Prime) (e : K ≃* L)
    (hf : (Nat.card L).factorization p = a) (T : Sylow p K) : Nat.card T = p ^ a := by
  have : Fact p.Prime := ⟨hp⟩
  rw [T.card_eq_multiplicity, Nat.card_congr e.toEquiv, hf]

end Transport

theorem factorization_card_alt_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ((2 * p).factorial / 2).factorization p = 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ℕ) ∣ (2 * p).factorial := Nat.dvd_factorial two_pos (by omega)
  have hlog : Nat.log p (2 * p) < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega)]
    nlinarith
  rw [Nat.factorization_def _ hp, padicValNat.div_of_dvd h2, padicValNat_factorial hlog]
  have h0 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))
  simp only [h0, Nat.sub_zero, pow_one, Finset.sum_Ico_succ_top (Nat.le_refl 1), Finset.Ico_self,
    Finset.sum_empty, zero_add]
  exact Nat.mul_div_cancel 2 hp.pos

theorem sylowSq_of_isAltTwoP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hK : IsAltTwoP p K) : SylowSq p K := by
  obtain ⟨e⟩ := hK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : Nontrivial (Fin (2 * p)) := Fin.nontrivial_iff_two_le.2 (by omega)
  intro T
  refine sylow_card_of_factorization hp e ?_ T
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_nat_card, nat_card_alternatingGroup]
  simpa using factorization_card_alt_two hp hp2

theorem sylowSq_of_isSmallLinTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hK : IsSmallLinTwo p K) : SylowSq p K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  intro T
  refine sylow_card_of_factorization hp (e.trans e₂) ?_ T
  exact CFSG.SectionRank.OddCover.factorization_card_psl_two hp hp2
    (GaloisField.card p 2 (by norm_num))

theorem sylowCube_of_isSmallUnitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hK : IsSmallUnitary p K) : SylowCube p K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := hK
  have hfe : d.1.fieldExponent = 1 := by
    rw [hd]
    simpa using hqe
  intro T
  obtain ⟨hcard, -, hexp, -⟩ := kFactUnitarySylowStructure K p d hp2 ⟨q, hqp, hd⟩ ⟨e⟩ T
  rw [hfe] at hcard
  exact ⟨by simpa using hcard, hexp⟩

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
