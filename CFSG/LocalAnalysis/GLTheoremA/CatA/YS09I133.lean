module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Fix
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.TitsLI
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs104
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def ChevTwoFourDvd : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple 2 S → 4 ∣ Nat.card S

@[expose] def SmallChev2Aut : Prop :=
  ∀ (H : Type) [Group H] [Finite H], commutator H = ⊤ → IsSimpleGroup (H ⧸ Subgroup.center H) →
    IsChevSimple 2 (H ⧸ Subgroup.center H) →
    ¬ CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar 2 (H ⧸ Subgroup.center H) →
    Nat.Coprime (Nat.card (Subgroup.center H)) 2 → ∀ (α : MulAut H) (m : ℕ), Odd m → α ^ m = 1 →
    ∀ (Q : Subgroup H), IsPGroup 2 ↥Q → Q ≠ ⊥ → twoPart (Nat.card H) ≤ 2 * Nat.card Q →
    (∀ x ∈ Q, α x = x) → α = 1

theorem i133At_of_facts
    (hL : CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained 2)
    (h4 : ChevTwoFourDvd) (hsmall : SmallChev2Aut) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I133At G p := by
  unfold I133At
  intro hp hp2 X J I D hJ hch hIJ hDN hDp hDc hcard d hd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hperf : commutator (PQuot p J) = ⊤ := hq.1
  have hsimpleS : IsSimpleGroup (PQuot p J ⧸ Subgroup.center (PQuot p J)) := hq.2
  have hcore : GLAPPrimeCore p (PQuot p J) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot (G := ↥J) hp
  have hZodd : Odd (Nat.card (Subgroup.center (PQuot p J))) := odd_card_center hp hp2 hcore
  have hZcop : Nat.Coprime (Nat.card (Subgroup.center (PQuot p J))) 2 :=
    Nat.coprime_two_right.2 hZodd
  have hnab : ∃ a b : PQuot p J ⧸ Subgroup.center (PQuot p J), a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcardJ : Nat.card (PQuot p J) =
      Nat.card (Subgroup.center (PQuot p J)) * Nat.card (PSimple p J) :=
    (Subgroup.card_mul_index _).symm
  have h2J : 4 ≤ twoPart (Nat.card (PQuot p J)) := by
    have h4S : 4 ∣ Nat.card (PSimple p J) := h4 (PSimple p J) hsimpleS hch
    have hS0 : Nat.card (PSimple p J) ≠ 0 := Nat.card_pos.ne'
    have hZ0 : Nat.card (Subgroup.center (PQuot p J)) ≠ 0 := Nat.card_pos.ne'
    rw [hcardJ, i133_twoPart_mul_of_ne hZ0 hS0, i133_twoPart_eq_one_of_odd hZodd, one_mul]
    have h44 : (2 : ℕ) ^ 2 ∣ Nat.card (PSimple p J) := by
      norm_num
      exact h4S
    have := i133_pow_two_le_twoPart hS0 h44
    norm_num at this
    exact this
  have hcardI := i133_card2_le_twoPart_image hp hIJ
  obtain ⟨Q, hQcard, hQIb⟩ : ∃ Q : Subgroup (PQuot p J),
      Nat.card ↥Q = twoPart (Nat.card ↥(i133ImageHom p hIJ).range) ∧
        ∀ x ∈ Q, x ∈ (i133ImageHom p hIJ).range := by
    obtain ⟨K, hK⟩ := i133_exists_card_eq_twoPart (i133ImageHom p hIJ).range
    refine ⟨K.map (i133ImageHom p hIJ).range.subtype, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective Subtype.val_injective]
      exact hK
    · rintro _ ⟨y, _, rfl⟩
      exact y.2
  have hQp : IsPGroup 2 ↥Q := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ↥Q = 2 ^ n :=
      ⟨(Nat.card ↥(i133ImageHom p hIJ).range).factorization 2, hQcard⟩
    exact IsPGroup.of_card hn
  have hsize : twoPart (Nat.card (PQuot p J)) ≤ 2 * Nat.card ↥Q := by
    rw [hQcard]
    have h1 : twoPart (Nat.card (PQuot p J)) ≤ 2 * card2 p I := hcard
    have h2 : card2 p I ≤ twoPart (Nat.card ↥(i133ImageHom p hIJ).range) := hcardI
    omega
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥Q = 1 := by
      rw [hbot, Subgroup.card_bot]
    have h3 := hsize
    rw [h1] at h3
    omega
  have hQc : ¬ Q ≤ Subgroup.center (PQuot p J) := by
    intro hle
    have hdvd : Nat.card ↥Q ∣ Nat.card (Subgroup.center (PQuot p J)) :=
      Subgroup.card_dvd_of_le hle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hQne
      apply Subgroup.eq_bot_of_card_eq Q
      rw [hn]
      norm_num
    have h2dvd : 2 ∣ Nat.card (Subgroup.center (PQuot p J)) := by
      have h2Q : 2 ∣ Nat.card ↥Q := by
        rw [hn]
        exact dvd_pow_self 2 hn0
      exact h2Q.trans hdvd
    obtain ⟨j, hj⟩ := hZodd
    omega
  have hdN : d ∈ Subgroup.normalizer (J : Set G) := hDN hd
  have hdI : ∀ i ∈ I, i * d = d * i := fun i hi => Subgroup.mem_centralizer_iff.1 (hDc hd) i hi
  set α : MulAut (PQuot p J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut p J ⟨d, hdN⟩ with hαdef
  have hαι : ∀ i : ↥I, α (i133ImageHom p hIJ i) = i133ImageHom p hIJ i := by
    intro i
    have hc : d * (i : G) * d⁻¹ = (i : G) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hdI i i.2).symm
    rw [i133ImageHom_apply, hαdef, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    congr 1
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.GLTheoremA.chev_coe_normalizerMonoidHom]
    exact hc
  have hQfix : ∀ x ∈ Q, α x = x := by
    intro x hx
    obtain ⟨i, hi⟩ := MonoidHom.mem_range.1 (hQIb x hx)
    rw [← hi]
    exact hαι i
  obtain ⟨k, hk⟩ := hDp ⟨d, hd⟩
  have hdm : d ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hm : Odd (p ^ k) := hpodd.pow
  have hm2 : Nat.Coprime (p ^ k) 2 := Nat.coprime_two_right.2 hm
  have hαpow : α ^ (p ^ k) = 1 := by
    rw [hαdef, ← map_pow]
    have h1 : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ (p ^ k) = 1 :=
      Subtype.ext (by simpa using hdm)
    rw [h1, map_one]
  have hα1 : α = 1 := by
    by_cases hIC : CFSG.HardMathSupport.Solomon.Coordinator.IsChevOfChar 2 (PSimple p J)
    · exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.lieQConstrained_aut_central_cover hL hsimpleS hnab hIC hZcop hperf hQp hQc α hm2 hαpow
        hQfix (i133_fix_pCore_two α hm2 hαpow hQp hQfix hsize)
    · exact hsmall (PQuot p J) hperf hsimpleS hch hIC hZcop α (p ^ k) hm hαpow Q hQp hQne hsize hQfix
  exact (CFSG.LocalAnalysis.GLTheoremA.chev_barAut_eq_one_iff_centMod hdN).1 hα1

theorem i133At_of_named
    (h4 : ChevTwoFourDvd) (hsmall : SmallChev2Aut) (G : Type) [Group G] [Finite G] (p : ℕ) :
    I133At G p :=
  i133At_of_facts CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_two_holds h4 hsmall G p

end CFSG.LocalAnalysis.GLTheoremA
