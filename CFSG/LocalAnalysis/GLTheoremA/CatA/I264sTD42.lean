module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


section Arith

theorem not_sq_dvd_td42 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 3 * 211341312 := by
  intro hd
  have hN : (3 * 211341312 : ℕ) = 2 ^ 12 * 3 ^ 5 * 7 ^ 2 * 13 := by norm_num
  rw [hN] at hd
  have hpd : p ∣ 2 ^ 12 * 3 ^ 5 * 7 ^ 2 * 13 := (dvd_pow_self p two_ne_zero).trans hd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
    · exact h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 (hp.dvd_of_dvd_pow h))
  · have hp13 : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h
    subst hp13
    norm_num at hd

end Arith

section Certs


theorem card_mulAut_fTD42 {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (h : catalogIs S fTD42) :
    Nat.card (MulAut S) = 3 * 211341312 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isTD4two h
  obtain ⟨h1, h2⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
  obtain ⟨⟨eT⟩, -, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec19.lineGroup_facts_of_isoLie q h1 h2 ⟨hv, ⟨e⟩⟩
  rw [Nat.card_congr (MulAut.congr eT).toEquiv, hA]

theorem kDescFam_td42_of_ne_three_seven (p : ℕ) (h3 : p ≠ 3) (h7 : p ≠ 7) : KDescFam p fTD42 := by
  intro hp hp2 Y _ _ K B hK hc hcB
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.qs.2
  have hA := card_mulAut_fTD42 hc
  refine (false_of_not_sq_dvd hp hK hcB (MulEquiv.refl _) ?_).elim
  rw [hA]
  exact not_sq_dvd_td42 hp hp2 h3 h7

theorem card_fTD42 {S : Type} [Group S] [Finite S] (h : catalogIs S fTD42) :
    Nat.card S = 211341312 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isTD4two h
  obtain ⟨h1, h2⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
  have hc := CFSG.AGLEmbedding.card_catGroup_trialityD4_even
    (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) h1 rfl
  rw [Nat.card_congr e.toEquiv, hc, h2]
  norm_num [CFSG.Open.ordTrialityD4]

theorem kDescFam_td42_seven_of_rankBound
    (hR : ∀ (S : Type) [Group S] [Finite S], catalogIs S fTD42 → ∀ E T : Subgroup S,
      IsElemAbelian 7 E → IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ 7) :
    KDescFam 7 fTD42 := by
  intro hp hp2 Y _ _ K B hK hc hcB
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.qs.2
  have hA := card_mulAut_fTD42 hc
  have hS := card_fTD42 hc
  have hO : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) = 3 := by
    have h := card_mulAut_eq_mul_outer hS (by norm_num)
    rw [hA] at h
    omega
  have hZ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    center_eq_bot_of_simple_nonprime hS (by norm_num)
  refine (false_of_rank_bound' hp hp2 hK hcB (MulEquiv.refl _) hZ (m := 3) (r := 7)
    (fun P _ => ?_) (hR _ hc) (by norm_num)).elim
  have h := card_le_mul_card_inf_inner P
  rwa [hO] at h

theorem kDescFam_td42_of_ne_three (hR : ∀ (S : Type) [Group S] [Finite S], catalogIs S fTD42 → ∀ E T : Subgroup S,
      IsElemAbelian 7 E → IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ 7)
    (p : ℕ) (h3 : p ≠ 3) : KDescFam p fTD42 := by
  by_cases h7 : p = 7
  · subst h7
    exact kDescFam_td42_seven_of_rankBound hR
  · exact kDescFam_td42_of_ne_three_seven p h3 h7

end Certs

end CFSG.LocalAnalysis.GLTheoremA
