module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Sub

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_theorem4 (h4 : Asc76Theorem4) {A K₀ : Subgroup G}
    (hA : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥) {g : G}
    (hg : g ∉ normalizer (A : Set G)) (hK₀K : K₀ ≤ centralizer (A : Set G))
    (hNK : normalizer (centralizer (A : Set G) : Set G) ≤ normalizer (K₀ : Set G))
    (hK2 : oUpperTwoPrime K₀ = K₀)
    (hstar : ∀ y : G, Even (Nat.card (rightConjugate K₀ y ⊓ normalizer (K₀ : Set G) :
      Subgroup G)) → ∃ S, IsSylowOf 2 S (rightConjugate K₀ y) ∧ S ≤ normalizer (K₀ : Set G))
    {R : Subgroup G} (hR : IsSylowOf 2 R K₀) (hm : 1 < Open.pRank 2 R) : IsElemAbelian 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hΦ
  set K := centralizer (A : Set G) with hKdef
  have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
  have hR1 : R ≠ ⊥ := by
    intro h
    obtain ⟨E, hER, -, hE4⟩ := Asc76X.exists_fourGroup_le hm
    rw [h, le_bot_iff] at hER
    rw [hER, card_bot] at hE4
    norm_num at hE4
  have hK₀even : Even (Nat.card K₀) :=
    (even_card_of_isPGroup hR.isPGroup hR1).two_dvd.trans (card_dvd_of_le hR.le) |>
      even_iff_two_dvd.mpr
  have hK₀N : normalizer (K₀ : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_of_tightlyEmbedded hK hK₀K hK₀even
  have hK₀T : TightlyEmbedded K₀ := by
    refine ⟨hK₀even, fun y hy => ?_⟩
    have hyK : y ∉ normalizer (K : Set G) := fun h => hy (hNK h)
    have hle : K₀ ⊓ rightConjugate K₀ y ≤ K ⊓ rightConjugate K y :=
      inf_le_inf hK₀K (AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀K y)
    exact (hK.2 y hyK).of_dvd_nat (card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := exists_ncChain_succ_eq K₀
  set H := ncChain K₀ n with hHdef
  have hst : ncIn K₀ H = H := hn
  have hKH : K₀ ≤ H := le_ncChain K₀ n
  have hOH := eq_bot_of_odd_of_le_ncChain K₀ hO n
  have hnorm := false_of_ncChain_le_normalizer hA hO hK₀K hK₀even hNK hg n
  rcases normal_or_isSzOrU3_of_theorem4 h4 hK₀T hKH hst hOH hK2
      (fun y _ hy => hstar y hy) hR hm hΦ with hle | ⟨hsz, hsyl⟩
  · exact hnorm hle
  · apply hnorm
    have hAK₀ : A ≤ normalizer (K₀ : Set G) := by
      refine le_trans ?_ hNK
      rw [normalizer_centralizer_eq hA]
      exact le_normalizer
    have hAH : A ≤ normalizer (H : Set G) := hAK₀.trans (normalizer_le_normalizer_ncChain K₀ n)
    have hAR : A ≤ centralizer (R : Set G) := le_centralizer_iff.mp (hR.le.trans hK₀K)
    have hAC := le_centralizer_of_isSzOrU3 (commutator_self_of_isQuasisimple hA.1) hsz hAH hsyl
      hAR
    have hHK : H ≤ K := le_centralizer_iff.mp hAC
    intro h hh
    by_contra hhN
    have hhK : h ∉ normalizer (K : Set G) := fun h' => hhN (hNK h')
    have hle : rightConjugate K₀ h ≤ K ⊓ rightConjugate K h :=
      le_inf ((AschbacherTheorem3.rightConjugate_le_of_mem hKH hh).trans hHK)
        (AschbacherTheorem3.rightConjugate_le_rightConjugate hK₀K h)
    have hodd := (hK.2 h hhK).of_dvd_nat (card_dvd_of_le hle)
    rw [rightConjugate_card] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) hK₀even

end CFSG.ComponentClassification.Asc76.Sec5
