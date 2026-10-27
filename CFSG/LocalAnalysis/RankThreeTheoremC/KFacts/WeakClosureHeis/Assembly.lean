module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Violation
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Nonabelian
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.KFactDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open Subgroup

theorem kFactWeakClosureHeis_of_dichotomy (hWC : KFactWeakClosure) (hI : GL83.I_7_13_1)
    (hL : OuterHeisInner) (hD : SylowDichotomy) : Generic49U3.KFactWeakClosureHeis := by
  intro p hp h5 X _ _ K hKn hKs hKnab hKcat hKc hKdvd Q hKQ Q₀ Q₁ hcyc hQ0 hcard hnab hexp hcomm hdisj hsup A
    hAQ hAcard
  haveI := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hsh : HeisShape p (Q : Subgroup X) Q₀ Q₁ :=
    ⟨Q.isPGroup', hcyc, hQ0, hcard, hnab, hexp, hcomm, hdisj, hsup⟩
  by_contra hcon
  push Not at hcon
  have hAn : ∀ q ∈ (Q : Subgroup X), A.map (MulAut.conj q).toMonoidHom ≤ A := by
    intro q hq
    refine le_of_eq (hcon q ?_)
    rintro _ ⟨a, ha, rfl⟩
    exact Q.mul_mem (Q.mul_mem hq (hAQ ha)) (Q.inv_mem hq)
  have hAcent : ∀ a ∈ A, ∀ q ∈ (Q : Subgroup X), q * a = a * q :=
    central_of_normal_of_card_prime Q.isPGroup' hAQ hAcard hAn
  have hApow : ∀ a ∈ A, a ^ p = 1 := pow_eq_one_of_card_prime hAcard
  obtain ⟨S, hS⟩ := exists_sylow_map_subtype K Q hKQ
  have hSmem : ∀ s : ↥K, s ∈ (S : Subgroup ↥K) ↔ (s : X) ∈ (Q : Subgroup X) := by
    intro s
    constructor
    · intro hs
      have : (s : X) ∈ (S : Subgroup ↥K).map K.subtype := ⟨s, hs, rfl⟩
      rw [hS] at this
      exact this.1
    · intro hs
      have : (s : X) ∈ (Q : Subgroup X) ⊓ K := ⟨hs, s.2⟩
      rw [← hS] at this
      obtain ⟨t, ht, hts⟩ := this
      have : t = s := Subtype.ext hts
      rwa [← this]
  have h3 : 3 ≤ CFSG.Open.pRank p (Q : Subgroup X) := three_le_pRank_heis hp hsh
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥K) :=
    two_le_pRank_of_I713 hI hp hp2 K hKs hKnab hKcat hKc h3
  have hfix : ∀ u : X, (∀ q ∈ (Q : Subgroup X), u * q = q * u) → ∀ s ∈ (S : Subgroup ↥K),
      u * (s : X) * u⁻¹ = (s : X) := by
    intro u hu s hs
    rw [mul_inv_eq_iff_eq_mul]
    exact hu s ((hSmem s).1 hs)
  by_cases hab : IsMulCommutative (S : Subgroup ↥K)
  ·
    have hSrk : 2 ≤ CFSG.Open.pRank p (S : Subgroup ↥K) := (pRank_top_eq_of_sylow S) ▸ h2
    have hAK : ∀ a ∈ A, a ∈ K := fun a ha =>
      mem_of_fixes_sylow hL hp h5 K hKs hKnab hKcat hKc hKdvd S (Or.inl hab) (hApow a ha)
        (hfix a fun q hq => (hAcent a ha q hq).symm)
    have hAKle : A ≤ K := hAK
    have hA'S : A.subgroupOf K ≤ (S : Subgroup ↥K) := by
      intro s hs
      exact (hSmem s).2 (hAQ (Subgroup.mem_subgroupOf.1 hs))
    have hA'card : Nat.card (A.subgroupOf K) = p := by
      rw [← hAcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAKle).toEquiv
    obtain ⟨g, hg1, hg2⟩ := wcOn_of_kFactWeakClosure hWC hp hp2 hKs hKnab hKcat S hab hSrk
      (A.subgroupOf K) hA'S hA'card
    rw [map_conj_subgroupOf K A hAKle g] at hg1 hg2
    have hAgK : A.map (MulAut.conj (g : X)).toMonoidHom ≤ K := by
      rintro _ ⟨a, ha, rfl⟩
      exact K.mul_mem (K.mul_mem g.2 (hAKle ha)) (K.inv_mem g.2)
    have hle : A.map (MulAut.conj (g : X)).toMonoidHom ≤ (Q : Subgroup X) := by
      intro y hy
      exact (hSmem ⟨y, hAgK hy⟩).1 (hg1 (Subgroup.mem_subgroupOf.2 hy))
    exact hg2 (by rw [hcon (g : X) hle])
  ·
    have hSn : ¬ IsMulCommutative ↥((Q : Subgroup X) ⊓ K) := fun hc =>
      hab ((isMulCommutative_map_subtype_iff K (S : Subgroup ↥K)).1 (hS ▸ hc))
    have hSle : (Q : Subgroup X) ⊓ K ≤ (Q : Subgroup X) := inf_le_left
    have hcardS : Nat.card ((Q : Subgroup X) ⊓ K : Subgroup X) = Nat.card (S : Subgroup ↥K) := by
      rw [← hS]
      exact Subgroup.card_map_of_injective K.subtype_injective
    have hcardSylow : Nat.card (S : Subgroup ↥K) = p ^ (Nat.card K).factorization p :=
      S.card_eq_multiplicity
    have hfinish : Nat.card ((Q : Subgroup X) ⊓ K : Subgroup X) = p ^ 3 → False := by
      intro hc3
      have hfac : (Nat.card K).factorization p ≤ 3 := by
        have : p ^ (Nat.card K).factorization p = p ^ 3 := by rw [← hcardSylow, ← hcardS, hc3]
        exact (Nat.pow_right_injective hp.two_le this).le
      have hZ : Nat.card (((Q : Subgroup X) ⊓ K) ⊓ centralizer (((Q : Subgroup X) ⊓ K : Subgroup X) : Set X) :
          Subgroup X) ≤ p :=
        (Generic49U3.card_inf_centralizer_of_nonabelian_card_p_cube hc3 hSn).le
      obtain ⟨u, huQ, hup, huc, hu⟩ := exists_central_order_p_not_mem hp hsh hSle hZ
      have huK : u ∈ K :=
        mem_of_fixes_sylow hL hp h5 K hKs hKnab hKcat hKc hKdvd S (Or.inr hfac) hup (hfix u huc)
      exact hu ⟨huQ, huK⟩
    rcases hD K hKs hKnab hKcat p hp h5 hKdvd with ha | hb | hb' | ⟨U, hU, hv⟩
    ·
      refine hfinish (le_antisymm ?_ ?_)
      · rw [hcardS, hcardSylow]
        exact Nat.pow_le_pow_right hp.pos ha
      · rw [hcardS]
        exact pow_three_le_card_of_nonabelian (S.isPGroup') ((isMulCommutative_map_subtype_iff K _).not.1
          (hS ▸ hSn))
    · exact hab (hb S)
    ·
      have hrk : CFSG.Open.pRank p ((Q : Subgroup X) ⊓ K) ≤ 2 := by
        rw [← hS, pRank_map_subtype_eq hp, ← pRank_top_eq_of_sylow S]
        exact hb'
      exact hfinish (card_eq_of_nonabelian_pRank_le_two hp hsh hSle hSn hrk)
    ·
      exact heis_violation_false hp Q hsh (U.map K.subtype) (hU.map K.subtype) (violation_map hp K U hv)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
