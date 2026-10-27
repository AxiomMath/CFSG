module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreGamma
public import CFSG.LocalAnalysis.OddStandard.Solomon75Recognition
public import CFSG.ClassicalInvolution.Generic.Generation.Endgame
import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Excl
import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CoreAux


theorem oddCore_eq_bot_of_balanced (hA : ClassicalInvolution.AschbacherProperTwoGeneratedCore)
    {n : ℕ} (hn : 8 ≤ n) (hD : CoverSylowData n) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) n)
    (hconj : ∀ u : G, orderOf u = 2 → ∃ g : G, u = g * t * g⁻¹)
    (hbal : OddCoreBalanced G) : pPrimeCore 2 ↥(cen t) = ⊥ := by
  obtain ⟨P, htP, hPC⟩ := exists_sylow_central ht hn hcov
  have hshape := sylowShape_of_hasSylowTwoTypeAhat hn hD
    (hasSylowTwoTypeAhat_of_centralizer_cover ht hn hcov) P
  have h3 : 3 ≤ Open.pRank 2 (P : Subgroup G) := by rw [hshape.rank]; norm_num
  obtain ⟨U₀, hU₀P, hU₀ab, hU₀4⟩ := exists_fourSub_of_two_le_pRank
    (by rw [hshape.rank]; norm_num : 2 ≤ Open.pRank 2 (P : Subgroup G))
  obtain ⟨E, hEP, hEab, hE8, hU₀E⟩ := hshape.four_in_E8 U₀ hU₀P hU₀ab hU₀4
  have hWE : Wsub U₀ = Wsub E := Wsub_eq_of_le hbal hEab hE8 hU₀E hU₀4
  obtain ⟨hWodd, -, -⟩ := Wsub_complete hbal hEab hE8
  have hcard2 : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
  have hW : Wsub U₀ = ⊥ := by
    by_contra hW1
    have hnormW : normalizer (Wsub U₀ : Set G) ≠ ⊤ := by
      intro htop
      have hnormal : (Wsub U₀).Normal := normalizer_eq_top_iff.mp htop
      rcases hnormal.eq_bot_or_eq_top with h | h
      · exact hW1 h
      · have : Odd (Nat.card (Wsub U₀)) := hWE ▸ hWodd
        rw [h, Subgroup.card_top] at this
        exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hcard2)
    have hgamma := gamma_le_normalizer_W hbal hshape.connected ⟨U₀, hU₀P, hU₀ab, hU₀4⟩
    have hne : Open.properTwoGenCoreGamma (P : Subgroup G) 2 ≠ ⊤ := fun htop =>
      hnormW (top_le_iff.mp (htop ▸ hgamma))
    rcases hA G hnonab P h3 hne with h1 | ⟨⟨e⟩⟩
    · refine ClassicalInvolution.false_of_gamma_one_ne_top P h3 h1 ht le_rfl ?_
      intro hsolv
      have : Group.IsSolvable (CentQuot t) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(cen t)))
      have hnt : Nontrivial (CentQuot t) := by
        apply Finite.one_lt_card_iff_nontrivial.mp
        have := hcov.2.1
        have h2 : Nat.card (center (CentQuot t)) ≤ Nat.card (CentQuot t) :=
          Subgroup.card_le_card_group _
        omega
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (CentQuot t)).ne
        hcov.1.1.commutator_eq_top
    · have hcardG : Nat.card G = 175560 := by
        rw [Nat.card_congr e.toEquiv, ClassicalInvolution.properTwoGenCoreJ1_eq_walterJ1]
        exact CFSG.Walter.J1Props.card_walterJ1
      have hdvd : n.factorial ∣ Nat.card G :=
        (factorial_dvd_natCard_of_cover (by omega) hcov).trans (Subgroup.card_subgroup_dvd_card _)
      have h8 : (8 : ℕ).factorial ∣ n.factorial := Nat.factorial_dvd_factorial hn
      rw [hcardG] at hdvd
      have := h8.trans hdvd
      revert this
      decide
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨a, haE⟩, ha⟩ := exists_ne (1 : E)
    exact ⟨a, haE, fun h => ha (Subtype.ext h)⟩
  have ha2 : orderOf a = 2 := orderOf_eq_two_of_isElemAbelian hEab haE ha1
  have hbot : oddCoreOf (cen a) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc oddCoreOf (cen a) ≤ Wsub E := oddCoreOf_cen_le_Wsub haE ha1
      _ = ⊥ := hWE ▸ hW
  obtain ⟨g, rfl⟩ := hconj a ha2
  rw [cen_conj, oddCoreOf_map_equiv (MulAut.conj g) (cen t)] at hbot
  have hbot' : oddCoreOf (cen t) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ (cen t).subtype_injective).mp hbot'

theorem solomon44OddCore_of_balanced (hA : ClassicalInvolution.AschbacherProperTwoGeneratedCore)
    {n : ℕ} (hn : 8 ≤ n) (hn10 : n ≤ 10) (hD : CoverSylowData n)
    (hB : AlternatingBalanceData n) : Solomon44OddCore n := by
  intro G _ _ _ hnonab t ht hcov
  exact oddCore_eq_bot_of_balanced hA hn hD hnonab ht hcov
    (exists_conj_of_involution hnonab ht hn hcov hB)
    (balanced hn hn10 hD hB hnonab ht hcov)

theorem oddCore_eleven_eq_bot_of_not_three_dvd
    (hA : ClassicalInvolution.AschbacherProperTwoGeneratedCore) (hD : CoverSylowData 11)
    (hB : AlternatingBalanceData 11) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) 11)
    (h3 : ¬ 3 ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ :=
  oddCore_eq_bot_of_balanced hA (by norm_num) hD hnonab ht hcov
    (exists_conj_of_involution hnonab ht (by norm_num) hcov hB)
    (balanced_of_not_three_dvd (by norm_num) hD hB hnonab ht hcov h3)

end CFSG.OddStandard.Solomon75
