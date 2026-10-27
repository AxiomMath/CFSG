module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinA7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinL42
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinNotAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2WM22
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

theorem lemma252_of_inputsW (h237 : Lemma2_3_9_7W) (hB : BenderBorelFacts)
    (hR : RankTwoBorelFacts) (hA6 : A6InnerFact) (hA7 : A7Excluded) (hM2 : M22M23Excluded)
    (hcov : M22CoverExcluded252) (hL42 : L42Excluded) (hsmall : SmallL2Facts)
    (hnalt : NotAltQuotientFacts) : Lemma252 := by
  intro G _ _ T M H S z hs ht L hL
  have hUS : UniqueSetting G T M := hs.setting
  have hT' : IsSylowTwoOf T M := hUS.isSylowTwoOf_M
  obtain ⟨hzN, hcomm, hLM, -⟩ := IsGamma0.component_normalized_commutator_not_le hUS ht.gamma0
    ht.sylow_inf hT' ht.le_T ht.z_mem ht.z_ne_one ht.z_sq hL
  obtain ⟨hinn, hlistW⟩ := h237 G T M hUS H S T z ht.gamma0 ht.sylow_inf hT' ht.le_T ht.z_mem
    ht.z_ne_one ht.z_sq L hL
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hP : IsSylowTwoOf (S ⊓ L) L := ht.sylow_inf_component hL
  set S₁ := S ⊓ Subgroup.normalizer (L : Set G) with hS₁
  have hS₁2 : IsPGroup 2 ↥S₁ := ht.sylow.2.1.to_le inf_le_left
  have hS₁N : S₁ ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hS₁P : IsSylowTwoOf (S₁ ⊓ L) L := by
    have h : S₁ ⊓ L = S ⊓ L := by
      rw [hS₁, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
    rw [h]
    exact hP
  have hS₁C : S₁ ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left.trans ht.le_centralizer
  have hS₁M : S₁ ≤ Subgroup.normalizer ((L ⊓ M : Subgroup G) : Set G) := by
    have h := Unc25G2.inf_normalizer_le_normalizer_inf_of_le (L := L) ht.le_M
    rwa [inf_comm M L] at h
  have hover : ∀ K : Subgroup G, K ≤ L → S₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K →
      K ≤ L ⊓ M :=
    fun K hKL hK hKc => le_inf hKL (ht.le_M_of_component_charTwo hs hL hKL hK hKc)
  have hLMne : L ⊓ M ≠ L := fun h => hLM (inf_eq_left.mp h)
  have hnorm_of : IsNonAltListedType L → Ch1.InducesInner z L := fun hn =>
    hinn (hnalt G L hq hn)
  have caseBender : fusionIsBenderGroup ↥L → ComponentList M S z L := fun hbend =>
    ⟨hzN, hnorm_of (Or.inl hbend), hcomm, hLM,
      Or.inl ⟨hbend, S ⊓ L, hP, ht.inf_eq_borel_of_bender hs hB hL hLM hbend⟩⟩
  have caseRank : IsRankTwoEvenType L → ComponentList M S z L := fun hrk => by
    obtain ⟨hMLB, hdyn⟩ := ht.rankTwo_data hs hR hL hLM hrk
    have hin : Ch1.InducesInner z L := by
      by_cases hA : Nonempty (↥L ≃* alternatingGroup (Fin 6))
      · refine hA6 G L S₁ (M ⊓ L) z (Or.inl hA) hS₁2 hS₁N hS₁P hzN hS₁C inf_le_right ?_ ?_
        · rw [inf_comm]
          exact hLMne
        · intro K hKL hK hKc
          rw [inf_comm]
          exact hover K hKL hK hKc
      · refine hnorm_of ?_
        rcases hrk with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd h hA
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    exact ⟨hzN, hin, hcomm, hLM, Or.inr (Or.inl ⟨hrk, hdyn, S ⊓ L, hP, hMLB⟩)⟩
  have caseCover : IsThreeFoldCoverAlt L 6 → False := fun hcov => by
    have hin : Ch1.InducesInner z L :=
      hA6 G L S₁ (L ⊓ M) z (Or.inr hcov) hS₁2 hS₁N hS₁P hzN hS₁C inf_le_left hLMne hover
    have hcen := ht.centreTwo hs hL hin
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
      (show 3 ∣ Nat.card ↥(Subgroup.center ↥L) by rw [hcov.2.1])
    have hxc : ∀ y ∈ L, y * ((x : ↥L) : G) = ((x : ↥L) : G) * y := fun y hy => by
      have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hcen _ (x : ↥L).2 hxc
    have hx3 : ((x : ↥L) : G) ^ 3 = 1 := by
      have h3 : x ^ 3 = 1 := by
        rw [← hx]
        exact pow_orderOf_eq_one x
      have := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : G)) h3
      simpa using this
    have h1 := Unc25G2.eq_one_of_pow_eq_one_of_two_pow Nat.prime_three (by norm_num) hx3 hk
    have hx1 : x = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    rw [hx1, orderOf_one] at hx
    omega
  have hlist : IsListedComponent M S L z := by
    rcases hlistW.old_or_cover with hlist | ⟨hQ22, -⟩
    · exact hlist
    · exact (hcov G L S₁ (L ⊓ M) hQ22 inf_le_left hLMne hS₁N hS₁P hover).elim
  rcases hlist with hBend | hRank | ⟨hAlt7, hPart⟩ | ⟨hD, zL, hproj, hML⟩ |
    ⟨⟨p, hp, hpL⟩, hML⟩ | hF | ⟨hG, hout, zL, hproj, hML⟩
  · exact caseBender hBend
  · rcases hRank with h | h | h | h | h
    · exact caseRank (Or.inl h)
    · exact caseRank (Or.inr (Or.inl h))
    · exact caseRank (Or.inr (Or.inr (Or.inl h)))
    · exact caseRank (Or.inr (Or.inr (Or.inr h)))
    · exact (caseCover h).elim
  · exact (hA7 G L S₁ (L ⊓ M) hAlt7 hPart inf_le_left hS₁2 hS₁N hS₁P hS₁M hover).elim
  · have hn : IsNonAltListedType L := by
      rcases hD with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    refine ⟨hzN, hnorm_of hn, hcomm, hLM, Or.inr (Or.inr (Or.inl ⟨hD, zL, hproj, ?_⟩))⟩
    rw [inf_comm]
    exact hML
  · by_cases h7 : 7 < p
    · have hn : IsNonAltListedType L :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hpL⟩)))))
      refine ⟨hzN, hnorm_of hn, hcomm, hLM, Or.inr (Or.inr (Or.inr ⟨⟨p, hp, h7, hpL⟩, ?_⟩))⟩
      rw [inf_comm]
      exact hML
    · push Not at h7
      have hp3 : 3 ≤ p := three_le_of_isFermatOrMersenne hp
      have hpp : p.Prime := hp.1
      interval_cases p
      · obtain ⟨-, -, -, -, h3⟩ := hpL.1
        exact absurd (by norm_num) h3
      · exact absurd hpp (by norm_num)
      · exact caseBender (hsmall.1 ↥L hpL)
      · exact absurd hpp (by norm_num)
      · exact caseRank (Or.inl ⟨1, le_rfl, hsmall.2 ↥L hpL⟩)
  · exact (hM2 G L S₁ (L ⊓ M) hF inf_le_left hS₁2 hS₁N hS₁P hS₁M hover).elim
  · refine (hL42 G L S₁ (L ⊓ M) z zL hG ?_ hproj hML hLMne hS₁2 hS₁N hS₁P hS₁M hS₁C
      hover).elim
    obtain ⟨s, hsS, hso⟩ := hout
    exact ⟨s, ⟨hsS, hso.1⟩, hso⟩

theorem lemma252_of_rankTwoW
    (h237 : Lemma2_3_9_7W) (hR : RankTwoBorelFacts) : Lemma252 :=
  lemma252_of_inputsW h237 benderBorelFacts hR a6InnerFact a7Excluded m22m23Excluded
    m22CoverExcluded252 l42Excluded smallL2Facts notAltQuotientFacts

end CFSG.QuasithinUnique
