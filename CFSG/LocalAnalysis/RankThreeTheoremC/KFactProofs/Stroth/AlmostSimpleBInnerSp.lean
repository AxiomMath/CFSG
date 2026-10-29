module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGLMain
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section IndexTwo

theorem oddPCoreInClosure_of_simple_index_two {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : Subgroup G) [Q.Normal] [IsSimpleGroup ↥Q]
    (hQ : Q.index = 2) : OddPCoreInClosure p G := by
  by_cases hG : p ∣ Nat.card G
  · have hp2' : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    have hpQ : p ∣ Nat.card Q := by
      have h := Subgroup.card_mul_index Q
      rw [hQ] at h
      rw [← h] at hG
      exact ((Nat.Prime.dvd_mul hp).1 hG).resolve_right hp2'
    intro K hK hKle hKcop
    have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have hKQ : K ≤ Q := by
      refine hKle.trans ?_
      rw [pElemClosure, Subgroup.closure_le]
      rintro x ⟨k, hk⟩
      have hcard : Nat.card (G ⧸ Q) = 2 := (Subgroup.index_eq_card Q).symm.trans hQ
      have h2 : ((x : G ⧸ Q)) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := G ⧸ Q) (x := (x : G ⧸ Q))
        rwa [hcard] at this
      have hpk : ((x : G ⧸ Q)) ^ p ^ k = 1 := by
        rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
      have hd1 : orderOf (x : G ⧸ Q) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      have hd2 : orderOf (x : G ⧸ Q) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpk
      have hone : orderOf (x : G ⧸ Q) = 1 :=
        Nat.dvd_one.1 ((Nat.Coprime.pow_right k hcop2).gcd_eq_one ▸ Nat.dvd_gcd hd1 hd2)
      exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 hone)
    haveI : (K.subgroupOf Q).Normal := Subgroup.Normal.subgroupOf hK Q
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf Q) with h0 | htop
    · have hKbot : K = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        have : (⟨k, hKQ hk⟩ : ↥Q) ∈ K.subgroupOf Q := hk
        rw [h0, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      rw [hKbot, Subgroup.card_bot]
      exact odd_one
    · exfalso
      have hQK : Q ≤ K := Subgroup.subgroupOf_eq_top.1 htop
      exact hp.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd hKcop (hpQ.trans (Subgroup.card_dvd_of_le hQK)))
  · exact OddPCoreInClosure.of_not_dvd hp hG

end IndexTwo

section Small

open CFSG.ComponentClassification.PresentationLocal

theorem oddPCoreInClosure_sympFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥sympFour := by
  haveI : IsSimpleGroup ↥(commutator ↥sympFour) := isSimpleGroup_commutator_sympFour
  have hidx : (commutator ↥sympFour).index = 2 :=
    (CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour (MulEquiv.refl ↥sympFour)).2
  exact oddPCoreInClosure_of_simple_index_two hp hp2 (commutator ↥sympFour) hidx

end Small

section Sp

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_statedSp_eq_bot (s : ℕ) : Subgroup.center (StatedSp s K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq s K]
  exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot

theorem oddPCoreInClosure_statedSp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : ℕ) :
    OddPCoreInClosure p ↥(StatedSp s K) := by
  have hcard := SymplecticFlag.card_statedSp (K := K) s
  have hbot := center_statedSp_eq_bot (K := K) s
  by_cases hs : s = 0
  · subst hs
    have h1 : Nat.card (StatedSp 0 K) = 1 := by
      rw [hcard]
      simp
    refine OddPCoreInClosure.of_not_dvd hp ?_
    rw [h1]
    exact hp.not_dvd_one
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs
  have hK2 : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hcardK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
    rcases (show (n : ℕ) = 1 ∨ 2 ≤ (n : ℕ) by have := n.pos; omega) with h1 | h2
    · left
      rw [hcardK, h1]
      norm_num
    · right
      rw [hcardK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2
  by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · have hQ : CFSG.IsQuasisimple ↥(⊤ : Subgroup (StatedSp s K)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
        (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs1 hq)
    refine oddPCoreInClosure_of_quasisimple_normal hp ⊤ hQ ?_ ?_
    · have : Subgroup.centralizer ((⊤ : Subgroup (StatedSp s K)) : Set ↥(StatedSp s K)) = ⊥ := by
        rw [Subgroup.coe_top, Subgroup.centralizer_univ, hbot]
      rw [this, Subgroup.card_bot]
      exact odd_one
    · intro h
      rw [Subgroup.card_top]
      exact h
  · have hK2' : Nat.card K = 2 := by
      rcases hK2 with h | h
      · exact h
      · exact absurd (Or.inl (Or.inr h)) hq
    have hs2 : s = 1 ∨ s = 2 := by
      by_contra hn
      push Not at hn
      exact hq (Or.inr (Or.inr ⟨hK2', by omega⟩))
    rcases hs2 with rfl | rfl
    ·
      have h6 : Nat.card (StatedSp 1 K) = 6 := by
        rw [hcard, hK2']
        norm_num [Finset.Icc_self]
      by_cases hp6 : p ∣ 6
      · have hp3 : p = 3 := by
          have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) hp6
          interval_cases p <;> first | rfl | (exfalso; revert hp hp2 hp6; decide)
        subst hp3
        refine OddPCoreInClosure.of_odd_core fun N hN hNcop => ?_
        have hNdvd : Nat.card N ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card N
        have hNd2 : Nat.card N ∣ 2 := by
          have : Nat.Coprime (Nat.card N) 3 := hNcop.symm
          exact this.dvd_of_dvd_mul_left (by simpa using hNdvd)
        rcases (Nat.dvd_prime Nat.prime_two).1 hNd2 with h1 | h2
        · rw [h1]
          exact odd_one
        · exfalso
          have hcen := le_center_of_normal_of_natCard_eq_two N h2
          rw [hbot, le_bot_iff] at hcen
          rw [hcen, Subgroup.card_bot] at h2
          omega
      · exact OddPCoreInClosure.of_not_dvd hp (by rw [h6]; exact hp6)
    ·
      have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK2'
        (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
        (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
      let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
        (MonoidHom.ofInjective
          (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
          (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
      exact OddPCoreInClosure.of_mulEquiv (e₀.trans E).symm (oddPCoreInClosure_sympFour hp hp2)

theorem oddPCoreInClosure_sesqUnitaryGroup_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {B : LinearMap.BilinForm K W}
    (hB : B.IsAlt) (hn : B.Nondegenerate) : OddPCoreInClosure p ↥(sesqUnitaryGroup B) := by
  obtain ⟨s, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  exact OddPCoreInClosure.of_mulEquiv e.symm (oddPCoreInClosure_statedSp hp hp2 s)

end Sp

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
