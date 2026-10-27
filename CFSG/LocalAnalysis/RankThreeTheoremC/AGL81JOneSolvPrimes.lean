module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

theorem IsSymThreeOrSUThreeTwo.prime_eq_of_dvd_card {Q : Type} [Group Q]
    (h : IsSymThreeOrSUThreeTwo Q) {q : ℕ} (hq : q.Prime) (hd : q ∣ Nat.card Q) :
    q = 2 ∨ q = 3 := by
  have hc : Nat.card Q ∣ 2 ^ 3 * 3 ^ 3 := by
    rcases h with ⟨f⟩ | ⟨K, _, _, hK, ⟨f⟩⟩
    · rw [Nat.card_congr f.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K hK
      have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1)
        (by rw [hK]; norm_num)
      rw [pow_one] at h2
      rw [Nat.card_congr f.toEquiv, h2]
      norm_num
  rcases (Nat.Prime.dvd_mul hq).1 (hd.trans hc) with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3))

variable {G : Type} [Group G] [Finite G]

theorem prime_eq_of_dvd_card_of_symThree {I : Subgroup G}
    (hb : IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I)) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card I) : q = 2 ∨ q = 3 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)] at hd
  rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
  · exact IsSymThreeOrSUThreeTwo.prime_eq_of_dvd_card hb hq h
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    rw [hk] at h
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem le_pPrimeCore_of_mem_cZero {X I : Subgroup G} (hI : I ∈ cZero X)
    (hs : ¬ IsTwoPrimeComponent I I) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    I ≤ (CFSG.pPrimeCore q ↥X).map X.subtype := by
  have hq : q.Prime := Fact.out
  have hle : I ≤ X := hI.le
  have hsn : (I.subgroupOf X).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hle).1 hI.subnormal
  have hcop : Nat.Coprime q (Nat.card (I.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    refine hq.coprime_iff_not_dvd.2 fun hd => ?_
    rcases prime_eq_of_dvd_card_of_symThree (hI.shape.resolve_left hs).2 hq hd with h | h
    · exact hq2 h
    · exact hq3 h
  have hcore := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal q hsn hcop
  intro x hx
  exact ⟨⟨x, hle hx⟩, hcore (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩

theorem prime_eq_of_dvd_card_jOne {H L : Subgroup G}
    (hs : ∀ I₀ ∈ cZero (H ⊓ L), ¬ IsTwoPrimeComponent I₀ I₀) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card (jOne H L)) : q = 2 ∨ q = 3 := by
  by_contra hne
  push Not at hne
  haveI : Fact q.Prime := ⟨hq⟩
  have hJ : jOne H L ≤ (CFSG.pPrimeCore q ↥(H ⊓ L)).map (H ⊓ L).subtype := by
    refine iSup₂_le fun I₀ hI => ?_
    refine le_trans ?_ (le_pPrimeCore_of_mem_cZero hI (hs I₀ hI) hne.1 hne.2)
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hdvd := hd.trans (Subgroup.card_dvd_of_le hJ)
  rw [Subgroup.card_map_of_injective (H ⊓ L).subtype_injective] at hdvd
  exact hq.coprime_iff_not_dvd.1 CFSG.pPrimeCore_coprime_card hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC
