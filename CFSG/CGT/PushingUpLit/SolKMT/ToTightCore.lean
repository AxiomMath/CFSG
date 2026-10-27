module

public import CFSG.CGT.PushingUpLit.SolKMT.Lemmas
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.SolKMT.Statement

public section

namespace CFSG.CGT.PushingUpLit.SolKMT

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

theorem solomonTimmesfeldTight_of_main_of_lemma25 (h25 : Asc76Lemma25)
    (hMT : SolomonTimmesfeldMain) : SolK.SolomonTimmesfeldTight := by
  intro G _ _ hKP hsimple hnab K htight hmax hchar R
  have hmain := hMT G hKP hsimple hnab K htight hmax hchar R
  have hRK : (R : Subgroup K).map K.subtype ≤ K := sylowImage_le K R
  have h2 : IsPGroup 2 ((R : Subgroup K).map K.subtype) := sylowImage_isPGroup K R
  have hcardR : Nat.card ((R : Subgroup K).map K.subtype) = Nat.card (R : Subgroup K) :=
    sylowImage_card K R
  have hbotR : (R : Subgroup K) ≠ ⊥ :=
    R.ne_bot_of_dvd_card (even_iff_two_dvd.mp htight.1)
  have hlt : 1 < Nat.card ((R : Subgroup K).map K.subtype) := by
    rw [hcardR]
    exact (R : Subgroup K).one_lt_card_iff_ne_bot.mpr hbotR
  obtain ⟨Rg, hRgdef⟩ : ∃ Rg : Subgroup G, (R : Subgroup K).map K.subtype = Rg := ⟨_, rfl⟩
  rw [hRgdef] at hmain hRK h2 hlt ⊢
  have hneRg : Rg ≠ ⊥ := Rg.one_lt_card_iff_ne_bot.mp hlt
  by_cases hnwc : ∃ g : G, conjSubgroup g Rg ≤ Subgroup.normalizer (K : Set G) ∧
      conjSubgroup g Rg ≠ Rg
  ·
    rcases hmain with h1 | h2' | h3 | h4 | h5 | h6
    · have hcardK : Nat.card K = 4 := h1.2
      have hRK' : Rg = K := by
        have hcR : Nat.card (R : Subgroup K) = Nat.card K := by
          rw [Sylow.card_eq_multiplicity, hcardK]
          have : (4 : ℕ).factorization 2 = 2 := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
            simp
          rw [this]
          norm_num
        have htop : (R : Subgroup K) = ⊤ := Subgroup.eq_top_of_card_eq _ hcR
        rw [← hRgdef, htop]
        ext x
        simp
      refine Or.inl ⟨?_, Or.inl ⟨?_, ?_⟩, hnwc⟩
      · rw [hRK', pCoreOf_eq_of_card_four K hcardK]
      · rw [hRK']
        exact h1.1
      · rw [hRK']
        exact hcardK
    · exact Or.inl ⟨h2'.1, Or.inr h2'.2, hnwc⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h3.1, by
        rcases h3.2 with a | b | c | d | e
        exacts [Or.inl a, Or.inr (Or.inl b), Or.inr (Or.inr (Or.inr (Or.inr c))),
          Or.inr (Or.inr (Or.inl d)), Or.inr (Or.inr (Or.inr (Or.inl e)))]⟩))
    · exact Or.inr (Or.inl ⟨h4.2.1, h4.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6.2))))
  ·
    have hwc : ∀ g : G, conjSubgroup g Rg ≤ Subgroup.normalizer (K : Set G) →
        conjSubgroup g Rg = Rg := by
      intro g hg
      by_contra hne
      exact hnwc ⟨g, hg, hne⟩
    rcases hmain with h1 | h2' | h3 | h4 | h5 | h6
    ·
      have hcardK : Nat.card K = 4 := h1.2
      have hRK' : Rg = K := by
        have hcR : Nat.card (R : Subgroup K) = Nat.card K := by
          rw [Sylow.card_eq_multiplicity, hcardK]
          have : (4 : ℕ).factorization 2 = 2 := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
            simp
          rw [this]
          norm_num
        have htop : (R : Subgroup K) = ⊤ := Subgroup.eq_top_of_card_eq _ hcR
        rw [← hRgdef, htop]
        ext x
        simp
      obtain ⟨gen, hgen⟩ := h1.1.exists_generator
      have hord : orderOf (gen : G) = 4 := by
        rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hgen, hcardK]
      have hzp : Subgroup.zpowers (gen : G) = K := by
        apply le_antisymm
        · exact (Subgroup.zpowers_le).mpr gen.2
        · intro y hy
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
          exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
      have hweak : WeaklyClosedInNormalizer (Subgroup.zpowers (gen : G)) := by
        intro h hh
        rw [hzp] at hh ⊢
        have := hwc h (by rw [hRK']; exact hh)
        rw [hRK'] at this
        exact this
      have hx2 : (gen : G) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
      have heven : Even (Nat.card G) := by
        rw [even_iff_two_dvd]
        have h4dvd : orderOf (gen : G) ∣ Nat.card G := orderOf_dvd_natCard (gen : G)
        rw [hord] at h4dvd
        exact (show 2 ∣ 4 by norm_num).trans h4dvd
      rcases h25 G (gen : G) hord hweak with hz | hD | hSD
      · exact (not_inZStar hsimple hnab heven hx2 hz).elim
      · have hnc : Subgroup.normalClosure ({(gen : G) ^ 2} : Set G) = ⊤ := by
          have : (Subgroup.normalClosure ({(gen : G) ^ 2} : Set G)).Normal := Subgroup.normalClosure_normal
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
              (Subgroup.normalClosure ({(gen : G) ^ 2} : Set G)) with hb | ht
          · exfalso
            apply hx2
            have hmem : (gen : G) ^ 2 ∈ Subgroup.normalClosure ({(gen : G) ^ 2} : Set G) :=
              Subgroup.subset_normalClosure rfl
            rw [hb] at hmem
            simpa using hmem
          · exact ht
        exact Or.inr (Or.inl ⟨h1.1, Or.inl (hasDihedralSylowTwo_transfer
          ((MulEquiv.subgroupCongr hnc).trans Subgroup.topEquiv) hD)⟩)
      · have hnc : Subgroup.normalClosure ({(gen : G) ^ 2} : Set G) = ⊤ := by
          have : (Subgroup.normalClosure ({(gen : G) ^ 2} : Set G)).Normal := Subgroup.normalClosure_normal
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
              (Subgroup.normalClosure ({(gen : G) ^ 2} : Set G)) with hb | ht
          · exfalso
            apply hx2
            have hmem : (gen : G) ^ 2 ∈ Subgroup.normalClosure ({(gen : G) ^ 2} : Set G) :=
              Subgroup.subset_normalClosure rfl
            rw [hb] at hmem
            simpa using hmem
          · exact ht
        exact Or.inr (Or.inl ⟨h1.1, Or.inr (hasSemidihedralSylowTwo_transfer
          ((MulEquiv.subgroupCongr hnc).trans Subgroup.topEquiv) hSD)⟩)
    ·
      obtain ⟨hRO, hel⟩ := h2'
      have hchar' : ∀ g ∈ Subgroup.normalizer (K : Set G), conjSubgroup g Rg = Rg := by
        intro g hg
        rw [hRO]
        exact conjSubgroup_pCoreOf K hg
      by_cases hc2 : Nat.card Rg = 2
      · exact (false_of_weakly_closed_order_two hsimple hnab htight hRK h2 hel hchar' hc2
          hwc).elim
      · have h4 : 4 ≤ Nat.card Rg := by
          obtain ⟨n, hn⟩ := h2.exists_card_eq
          have hn0 : n ≠ 0 := by
            rintro rfl
            rw [pow_zero] at hn
            omega
          have hn1 : n ≠ 1 := by
            rintro rfl
            rw [pow_one] at hn
            exact hc2 hn
          rw [hn]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hRO, hel, h4,
          isTI_of_tight htight hRK h2 hchar',
          normalizer_eq_of_tight htight hRK h2 hneRg hchar',
          ⟨hRK.trans (Subgroup.le_normalizer (H := K)), hwc⟩⟩))))
    · exact Or.inr (Or.inr (Or.inl ⟨h3.1, by
        rcases h3.2 with a | b | c | d | e
        exacts [Or.inl a, Or.inr (Or.inl b), Or.inr (Or.inr (Or.inr (Or.inr c))),
          Or.inr (Or.inr (Or.inl d)), Or.inr (Or.inr (Or.inr (Or.inl e)))]⟩))
    · exact Or.inr (Or.inl ⟨h4.2.1, h4.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6.2))))

end CFSG.CGT.PushingUpLit.SolKMT
