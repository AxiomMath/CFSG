module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutGlue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.AGLEmbeddingD2

section Generic

theorem sporCore_of_torusLocal {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (T : Sylow 5 K) (h : TorusLocal 5 (T : Subgroup K)) :
    SporCore 5 K T := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hcard, hmax, hcent, hsolv, t, htN, m, lam, e, hm, hlam, he, hpow, hinv, hline⟩ := h
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  have hTbot : (T : Subgroup K) ≠ ⊥ := by
    intro hb
    rw [hb] at hcard
    simp at hcard
  have hTtop : (T : Subgroup K) ≠ ⊤ := by
    intro ht
    have hK : Nat.card K = 5 ^ 2 := by
      rw [← hcard, ht]; exact Nat.card_congr Subgroup.topEquiv.symm.toEquiv
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hK
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (this.is_comm.comm a b)
  have hlam1 : (lam : ZMod 5) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hlam
    norm_num at hlam
  refine ⟨?_, hcen, ?_, isCoatom_of_overgroups (normalizer_ne_top_of_simple hs hTbot hTtop) hmax,
    hsolv, ?_, ?_⟩
  · rw [hcard]; exact ⟨5, by norm_num⟩
  · intro g hg
    exact hcent (Subgroup.mem_centralizer_iff.2 fun t ht => (hg t ht).symm)
  ·
    refine torus_of_conj_data (p := 5) (by norm_num) (Subgroup.pow_mem _ htN m) ?_
    intro a y hyT hcomm
    have hconj := conj_pow_eq_pow_pow hpow (5 ^ a) y hyT
    have hy : y ^ (lam ^ (5 ^ a)) = y := by
      rw [← hconj]
      calc (t ^ m) ^ (5 ^ a) * y * ((t ^ m) ^ (5 ^ a))⁻¹
          = y * (t ^ m) ^ (5 ^ a) * ((t ^ m) ^ (5 ^ a))⁻¹ := by rw [hcomm]
        _ = y := by group
    exact eq_one_of_pow_eq_self (p := 5) (k := 2) (by norm_num)
      (hcard ▸ Subgroup.orderOf_dvd_natCard (T : Subgroup K) hyT)
      (by rw [natCast_pow_prime_pow]; exact hlam1) hy
  ·
    intro V hVT hV hVN
    left
    have hVc : Nat.card V ∣ 5 ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hVT
    have hV1 : Nat.card V ≠ 1 := fun h1 => hV (Subgroup.card_eq_one.1 h1)
    obtain ⟨i, hi, hiV⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hVc
    interval_cases i
    · exact absurd (by simpa using hiV) hV1
    · exfalso
      have htV : t ∈ Subgroup.normalizer (V : Set K) := hVN htN
      exact hline 1 (by norm_num) (by omega) V hVT (by simpa using hiV) (by simpa using htV)
    · exact Subgroup.eq_of_le_of_card_ge hVT (by rw [hiV, hcard])

end Generic

section Certified


theorem sporCore_of_isTitsGroup {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsTitsGroup K) (T : Sylow 5 K) :
    SporCore 5 K T := by
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  exact sporCore_of_torusLocal hs hnab T
    (torusLocal_tits_sylow (X := K) (K := ⊤) hKc (Subgroup.topEquiv.trans e) T)

theorem autFixInner_of_isTitsGroup {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsTitsGroup K) (T : Sylow 5 K) :
    AutFixInner 5 K T := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  have hcen : Subgroup.center K = ⊥ := center_eq_bot_of_simple hs hnab
  have : ((MulAut.conj : K →* MulAut K).range).Normal := innerRange_normal
  refine autFixInner_of_centralizer hcen T (sylowSq_of_isTitsGroup hK T) fun R => ?_
  have hX := torusLocal_tits_sylow (X := MulAut K) (K := (MulAut.conj : K →* MulAut K).range)
    (centralizer_innerRange hcen) ((innerEquiv hcen).symm.trans e) R
  exact ⟨hX.1, hX.2.2.1⟩

end Certified

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
