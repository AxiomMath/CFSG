module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Violation
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Nonabelian
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

private theorem mem_sylow_iff {X : Type} [Group X] (K : Subgroup X) (Q : Subgroup X)
    (S : Subgroup ↥K) (hS : S.map K.subtype = Q ⊓ K) :
    ∀ s : ↥K, s ∈ S ↔ (s : X) ∈ Q := by
  intro s
  constructor
  · intro hs
    have : (s : X) ∈ S.map K.subtype := ⟨s, hs, rfl⟩
    rw [hS] at this
    exact this.1
  · intro hs
    have : (s : X) ∈ Q ⊓ K := ⟨hs, s.2⟩
    rw [← hS] at this
    obtain ⟨t, ht, hts⟩ := this
    have : t = s := Subtype.ext hts
    rwa [← this]

private theorem map_le_of_weaklyClosed {X : Type} [Group X] {Q A : Subgroup X} (hAQ : A ≤ Q)
    (hwc : ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ Q → A.map (MulAut.conj g).toMonoidHom = A) :
    ∀ q ∈ Q, A.map (MulAut.conj q).toMonoidHom ≤ A := by
  intro q hq
  refine le_of_eq (hwc q ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact Q.mul_mem (Q.mul_mem hq (hAQ ha)) (Q.inv_mem hq)

theorem kFactWeakClosureOmega3_of_dich (hWC : KFactWeakClosure) (hI : GL83.I_7_13_1)
    (hIA : KFactInnerAction) (hD : DichThree) : KFactWeakClosureOmega3 := by
  intro X _ _ K hKn hKs hKnab hKcat hKc hKdvd Q hKQ hEx A hAQ hAcard
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEQ, hEab, hEcard, hEall⟩ := hEx
  by_contra hcon
  push Not at hcon
  have hAcent : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup X), q * a = a * q :=
    central_of_normal_of_card_prime Q.isPGroup' hAQ hAcard (map_le_of_weaklyClosed hAQ hcon)
  obtain ⟨S, hS⟩ := exists_sylow_map_subtype K Q hKQ
  have hSmem := mem_sylow_iff K (Q : Subgroup X) (S : Subgroup ↥K) hS
  have h3 : 3 ≤ CFSG.Open.pRank 3 (Q : Subgroup X) :=
    le_pRank_of_elemAbelian (by norm_num) hEQ hEab hEcard
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    two_le_pRank_of_I713 hI Nat.prime_three (by norm_num) K hKs hKnab hKcat hKc h3
  by_cases hab : IsMulCommutative (S : Subgroup ↥K)
  · exact false_of_abelian_sylow hWC hIA K hKs hKnab hKcat hKc hKdvd Q S hSmem hab h2 hAQ
      hAcard hAcent hcon
  · rcases (hD ↥K hKs hKnab hKcat hKdvd).1 with hall | hpair | hrank | hfus
    · exact hab (hall S)
    · exact omega_false_of_pair Q hEab hEall (hpair.map K.subtype K.subtype_injective)
    · obtain ⟨F, -, hF, j, hj, hFcard⟩ := exists_elemAbelian_of_le_pRank (by norm_num) hrank
      refine omega_false_of_elemAbelian Q (by rw [hEcard]; norm_num) hEall (F := F.map K.subtype)
        ((isElemAbelian_map_iff_of_injective K.subtype K.subtype_injective F).2 hF) ?_
      rw [Subgroup.card_map_of_injective K.subtype_injective, hFcard]
      calc 27 < 3 ^ 4 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    · exact false_of_centralFusion K hKc hfus Q hAQ hAcard hAcent hcon

theorem kFactWeakClosureHeisThree_of_heis (hWC : KFactWeakClosure) (hI : GL83.I_7_13_1)
    (hIA : KFactInnerAction) (hO : OuterThreeInner) (hH : HeisDichThree) :
    KFactWeakClosureHeisThree := by
  intro X _ _ K hKn hKs hKnab hKcat hKc hKdvd Q hKQ Q₀ Q₁ hcyc hQ0 hcard hnab hexp hcomm hdisj
    hsup A hAQ hAcard
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsh : HeisShape 3 (Q : Subgroup X) Q₀ Q₁ :=
    ⟨Q.isPGroup', hcyc, hQ0, hcard, hnab, hexp, hcomm, hdisj, hsup⟩
  by_contra hcon
  push Not at hcon
  have hAcent : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup X), q * a = a * q :=
    central_of_normal_of_card_prime Q.isPGroup' hAQ hAcard (map_le_of_weaklyClosed hAQ hcon)
  obtain ⟨S, hS⟩ := exists_sylow_map_subtype K Q hKQ
  have hSmem := mem_sylow_iff K (Q : Subgroup X) (S : Subgroup ↥K) hS
  have h3 : 3 ≤ CFSG.Open.pRank 3 (Q : Subgroup X) := three_le_pRank_heis Nat.prime_three hsh
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    two_le_pRank_of_I713 hI Nat.prime_three (by norm_num) K hKs hKnab hKcat hKc h3
  by_cases hab : IsMulCommutative (S : Subgroup ↥K)
  · exact false_of_abelian_sylow hWC hIA K hKs hKnab hKcat hKc hKdvd Q S hSmem hab h2 hAQ
      hAcard hAcent hcon
  have hSn : ¬ IsMulCommutative ↥((Q : Subgroup X) ⊓ K) := fun hc =>
    hab ((isMulCommutative_map_subtype_iff K (S : Subgroup ↥K)).1 (hS ▸ hc))
  have hSle : (Q : Subgroup X) ⊓ K ≤ (Q : Subgroup X) := inf_le_left
  have hcardS : Nat.card ((Q : Subgroup X) ⊓ K : Subgroup X) = Nat.card (S : Subgroup ↥K) := by
    rw [← hS]
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hcardSylow : Nat.card (S : Subgroup ↥K) = 3 ^ (Nat.card K).factorization 3 :=
    S.card_eq_multiplicity
  have hfinish : Nat.card ((Q : Subgroup X) ⊓ K : Subgroup X) = 3 ^ 3 → False := by
    intro hc3
    have hfac : (Nat.card K).factorization 3 ≤ 3 := by
      have : 3 ^ (Nat.card K).factorization 3 = 3 ^ 3 := by rw [← hcardSylow, ← hcardS, hc3]
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).le
    have hZ : Nat.card (((Q : Subgroup X) ⊓ K) ⊓ centralizer (((Q : Subgroup X) ⊓ K :
        Subgroup X) : Set X) : Subgroup X) ≤ 3 :=
      (Generic49U3.card_inf_centralizer_of_nonabelian_card_p_cube hc3 hSn).le
    obtain ⟨u, huQ, hup, huc, hu⟩ := exists_central_order_p_not_mem Nat.prime_three hsh hSle hZ
    have huK : u ∈ K := by
      refine mem_of_fixes_small_sylow hO K hKs hKnab hKcat hKc S hab hfac hup ?_
      intro s hs
      rw [mul_inv_eq_iff_eq_mul]
      exact huc s ((hSmem s).1 hs)
    exact hu ⟨huQ, huK⟩
  rcases hH ↥K hKs hKnab hKcat hKdvd with hSD | hfus
  · rcases hSD with ha | hb | hb' | ⟨U, hU, hv⟩
    ·
      refine hfinish (le_antisymm ?_ ?_)
      · rw [hcardS, hcardSylow]
        exact Nat.pow_le_pow_right (by norm_num) ha
      · rw [hcardS]
        exact pow_three_le_card_of_nonabelian (S.isPGroup')
          ((isMulCommutative_map_subtype_iff K _).not.1 (hS ▸ hSn))
    · exact hab (hb S)
    ·
      have hrk : CFSG.Open.pRank 3 ((Q : Subgroup X) ⊓ K) ≤ 2 := by
        rw [← hS, pRank_map_subtype_eq Nat.prime_three, ← pRank_top_eq_of_sylow S]
        exact hb'
      exact hfinish (card_eq_of_nonabelian_pRank_le_two Nat.prime_three hsh hSle hSn hrk)
    ·
      exact heis_violation_false Nat.prime_three Q hsh (U.map K.subtype) (hU.map K.subtype)
        (violation_map Nat.prime_three K U hv)
  · exact false_of_centralFusion K hKc hfus Q hAQ hAcard hAcent hcon

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
