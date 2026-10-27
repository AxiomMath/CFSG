module

public import CFSG.LocalAnalysis.OddStandard.Solomon75LyLeaf
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bGen4Check
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bSmall
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bG2D4
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bLy
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.Assembly.LowTwoRank CoreAux

section Assembly


theorem oddCoreElevenThree_of_gh74_of_gen4
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput) (hG4 : SylowGen4 11) :
    OddCoreElevenThree := by
  intro G _ _ _ hnonab t ht hcov
  have hD := coverSylowData_eleven_of_certificate
  have hB := alternatingBalanceData_eleven_of_certificate
  have hT : HasSylowTwoTypeAhat G 11 :=
    hasSylowTwoTypeAhat_of_centralizer_cover ht (by norm_num) hcov
  obtain ⟨P, htP, hPC⟩ := exists_sylow_central ht (by norm_num) hcov
  have hshape := sylowShape_of_hasSylowTwoTypeAhat (by norm_num) hD hT P
  have hgen := gen4_of_hasSylowTwoTypeAhat hG4 hT
  have hone := one_class hnonab ht (by norm_num) hcov hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardP : Nat.card (P : Subgroup G) = 256 := by simpa using hshape.card
  have hv : (Nat.card G).factorization 2 = 8 := by
    have h1 := P.card_eq_multiplicity
    rw [hcardP] at h1
    have h2 : (2 : ℕ) ^ 8 = 2 ^ (Nat.card G).factorization 2 := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  have hrank : 3 ≤ CFSG.Open.twoRank G := by
    have h4 := hshape.rank
    have h5 := (SectionRank.pRank_sylow P).1
    unfold CFSG.Open.twoRank
    rw [← h5, h4]
    norm_num
  rcases hGH G hnonab hrank hgen with
    ⟨p, f, hp, hp2, hf, hG⟩ | ⟨p, f, hp, hp2, hf, hPSp⟩ | ⟨f, htG2⟩ |
    ⟨p, f, hp, hp2, hf, hmod, hL4⟩ | ⟨p, f, hp, hp2, hf, hmod, hU4⟩ | ⟨p, f, hp, hf, hmod, hL5⟩ |
    ⟨p, f, hp, hf, hmod, hU5⟩ | hmid | ⟨n, hn8, hn11, ⟨e⟩⟩ | hspor
  ·
    rw [pPrimeCore_cen_eq_bot_of_g2d4 hp hp2 hf hG ht, Subgroup.card_bot]
    decide
  ·
    exfalso
    have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f :=
      le_trans (by have := hp.two_le; omega : 3 ≤ p) (Nat.le_self_pow (by omega) p)
    by_cases h5 : 5 ≤ p ^ f
    · exact false_of_psp4_oneClass ht hp hp2 h5 hPSp P htP
        (fun x hx => mem_centralizer_singleton_iff.mp (hPC hx)) hone
    · have hq : p ^ f = 3 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      have hcard := CFSG.GH74.card_of_lieModel_PSp (n := 2) (by norm_num) hp2 hPSp
      rw [hq] at hcard
      exact false_of_card_eq_of_factorization hv hcard (by decide +kernel)
  ·
    exact absurd hv (not_eight_of_lieModel_twistedG2 htG2)
  ·
    have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    exact absurd hv (not_eight_of_lieModel_PSL4 hmod (Nat.odd_iff.mp hpodd) hL4)
  ·
    have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p ^ f :=
      le_trans (by have := hp.two_le; omega : 3 ≤ p) (Nat.le_self_pow (by omega) p)
    exact absurd hv (not_eight_of_lieModel_PSU4 hp2 hmod h3 (Nat.odd_iff.mp hpodd) hU4)
  ·
    exact absurd hv (not_eight_of_lieModel_PSL5 hmod hL5)
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact two_pow_mod_four_ne_one hf hmod
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    exact absurd hv (not_eight_of_lieModel_PSU5 hp2 hmod (by omega) hU5)
  ·
    exact absurd hv (not_eight_of_small_lie hmid)
  ·
    exact absurd hv (not_eight_of_alt hn8 hn11 e)
  ·
    rcases hspor with h | h | h | h | h | h | h | hL
    · exact absurd hv (not_eight_of_sporadic (Or.inl h))
    · exact absurd hv (not_eight_of_sporadic (Or.inr (Or.inl h)))
    · exact absurd hv (not_eight_of_sporadic (Or.inr (Or.inr (Or.inl h))))
    · exact absurd hv (not_eight_of_sporadic (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact absurd hv (not_eight_of_sporadic (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact absurd hv
        (not_eight_of_sporadic (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact absurd hv
        (not_eight_of_sporadic (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    ·
      rw [pPrimeCore_cen_eq_bot_of_Ly hnonab hL ht, Subgroup.card_bot]
      decide

theorem oddCoreElevenThree_of_gh74
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput)
    (hchk : AhatData.Gen4Good 11 (AhatData.P0 11)) : OddCoreElevenThree :=
  oddCoreElevenThree_of_gh74_of_gen4 hGH
    (sylowGen4_eleven Certificates.certificate6122.1 Certificates.certificate6122.2.1
      hchk)

end Assembly

end CFSG.OddStandard.Solomon75
