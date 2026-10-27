module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZAut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZOuter
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHallHigman

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

private theorem open_pRank_eq {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.Open.pRank p H = CFSG.pRank p ↥H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_open_pRank_top]

private theorem exists_cover_of_ncard_le_two {α : Type*} [Finite α] {S : Set α}
    (hS : S.ncard ≤ 2) {a : α} (ha : a ∈ S) : ∃ b ∈ S, ∀ c ∈ S, c = a ∨ c = b := by
  by_cases h : ∃ b ∈ S, b ≠ a
  · obtain ⟨b, hb, hba⟩ := h
    refine ⟨b, hb, fun c hc => ?_⟩
    by_contra hcon
    push Not at hcon
    have h3 : 2 < S.ncard := by
      rw [Set.two_lt_ncard_iff (Set.toFinite S)]
      exact ⟨a, b, c, ha, hb, hc, hba.symm, hcon.1.symm, hcon.2.symm⟩
    omega
  · push Not at h
    exact ⟨a, ha, fun c hc => Or.inl (h c hc)⟩

private theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {d : ℕ} {u : X}
    (hdu : ∃ n : ℕ, u ^ d ^ n = 1) : IsPGroup d (zpowers u) := by
  obtain ⟨n, hn⟩ := hdu
  refine IsPGroup.of_card_dvd_pow (n := n) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one hn

private theorem normal_of_map_conj_eq {X : Type*} [Group X] {J : Subgroup X}
    (h : ∀ g : X, J.map (MulAut.conj g).toMonoidHom = J) : J.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmem : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [h g] at hmem

theorem DEmbConfig.false {X : Type} [Group X] [Finite X] {Y W : Subgroup X} {d : ℕ}
    (hcfg : DEmbConfig X Y d W) (hcomp : ZComponentData X Y) (hk : ZKFacts) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : d.Prime := hcfg.prime
  have hd5 : 5 ≤ d := hcfg.five_le
  have hd3 : d ≠ 3 := by omega
  have hd2 : d ≠ 2 := by omega
  have hX : CFSG.Open.IsKGroup X := hcfg.isKGroup
  have hO : CFSG.pPrimeCore 3 X = ⊥ := hcfg.pPrimeCore_eq_bot
  have hr3 := hcfg.pRank_le_three
  have hW : IsPGroup d W := hcfg.isPGroup
  have hc3 := ncard_isComponent_le_three hk.omegaNotCentral hX hO hr3
  have hcd : {C : Subgroup X | CFSG.IsComponent C}.ncard < d := by omega
  have hnorm : ∀ C : Subgroup X, CFSG.IsComponent C → W ≤ normalizer (C : Set X) :=
    fun C hC => le_normalizer_of_isComponent hd hW hcd hC
  obtain ⟨L, hL, hLY, hLshape⟩ := hcomp.exists_shape
  obtain ⟨L₂, hL₂, hcover⟩ := exists_cover_of_ncard_le_two hcomp.card_le_two
    (a := L) ⟨hL, hLY⟩
  have hshape : ∀ C : Subgroup X, CFSG.IsComponent C → ¬ C ≤ Y →
      IsL34Type ↥C ∨ IsA6Type ↥C ∨ (IsA11Type ↥C ∧ d ≠ 5) := by
    intro C hC hCY
    by_cases hother : ∃ C' : Subgroup X, CFSG.IsComponent C' ∧ ¬ C' ≤ Y ∧ C' ≠ C
    · obtain ⟨C', hC', hC'Y, hne⟩ := hother
      rcases (hcomp.two_shapes C C' hC hCY hC' hC'Y hne.symm).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · push Not at hother
      have hLC : L = C := hother L hL hLY
      subst hLC
      rcases hLshape with h | h
      · exact Or.inl h
      · refine Or.inr (Or.inr ⟨h, fun hd5eq => ?_⟩)
        apply hcfg.not_dvd_card
        rw [hd5eq]
        exact hcomp.five_dvd ⟨L, hL, hLY, h⟩
  have hrank : ∀ C : Subgroup X, CFSG.IsComponent C → ¬ C ≤ Y →
      CFSG.Open.pRank d (⊤ : Subgroup (MulAut ↥C)) ≤ 1 := by
    intro C hC hCY
    rw [open_pRank_eq]
    exact pRank_mulAut_le_one hk hd hd5 hC.1 (hshape C hC hCY)
  have hU := inf_centralizer_inf_centralizer_ne_bot hd (hnorm L hL) (hnorm L₂ hL₂.1)
    (hrank L hL hLY) (hrank L₂ hL₂.1 hL₂.2) (by rw [open_pRank_eq]; exact hcfg.three_le_pRank)
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huW : u ∈ W := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu).1).1
  have huL : u ∈ centralizer (L : Set X) := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu).1).2
  have huL₂ : u ∈ centralizer (L₂ : Set X) := (Subgroup.mem_inf.mp hu).2
  have houtside : ∀ C : Subgroup X, CFSG.IsComponent C → ¬ C ≤ Y →
      u ∈ centralizer (C : Set X) := by
    intro C hC hCY
    rcases hcover C ⟨hC, hCY⟩ with h | h
    · rw [h]; exact huL
    · rw [h]; exact huL₂
  have hdu : ∃ n : ℕ, u ^ d ^ n = 1 := by
    obtain ⟨n, hn⟩ := hW ⟨u, huW⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hJ : ∃ J : Subgroup X, CFSG.IsComponent J ∧ J ≤ Y ∧ u ∉ centralizer (J : Set X) := by
    by_contra hcon
    push Not at hcon
    have hT := isPGroup_zpowers_of_pow_eq_one hdu
    have hpc : CFSG.Open.pRank 3 (CFSG.pCore 3 X) ≤ 2 := by
      rw [open_pRank_eq]
      exact pRank_pCore_le_two hk.omegaNotCentral hX hO hr3 hL
    have hWN : W ≤ normalizer (CFSG.pCore 3 X : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr (CFSG.pCore_normal (p := 3) (G := X))]
      exact le_top
    have hWpc : W ≤ centralizer (CFSG.pCore 3 X : Set X) :=
      le_centralizer_of_pRank_le_two hd hd5 (CFSG.pCore_isPGroup (p := 3) (G := X)) hpc hW hWN
    have h1 : zpowers u ≤ centralizer (CFSG.pCore 3 X : Set X) :=
      Subgroup.zpowers_le.mpr (hWpc huW)
    have h2 : ∀ C : Subgroup X, CFSG.IsComponent C → zpowers u ≤ centralizer (C : Set X) := by
      intro C hC
      rw [Subgroup.zpowers_le]
      by_cases hCY : C ≤ Y
      · exact hcon C hC hCY
      · exact houtside C hC hCY
    have hbot := eq_bot_of_le_centralizer_pCore_of_isComponent hd hd3 hO hT h1 h2
    exact hu1' (Subgroup.zpowers_eq_bot.mp hbot)
  obtain ⟨J, hJc, hJY, hJu⟩ := hJ
  have hJd : ¬ d ∣ Nat.card J := fun h =>
    hcfg.not_dvd_card (h.trans (Subgroup.card_dvd_of_le hJY))
  have huJ : u ∈ normalizer (J : Set X) := hnorm J hJc huW
  have hdJ : d ∣ Nat.card (MulAut ↥J) :=
    dvd_card_mulAut_of_not_mem_centralizer hd hdu huJ hJu
  have hnJ : ¬ J.Normal := not_normal_of_not_mem_centralizer hk.normalComplement hX hd hd2
    hcfg.no_normal_index hJc hJd hdu huJ hJu
  obtain ⟨h, hh⟩ : ∃ h : X, J.map (MulAut.conj h).toMonoidHom ≠ J := by
    by_contra hcon
    push Not at hcon
    exact hnJ (normal_of_map_conj_eq hcon)
  by_cases hLJ : ∃ x : X, L = J.map (MulAut.conj x).toMonoidHom
  ·
    obtain ⟨x, hx⟩ := hLJ
    let e : ↥J ≃* ↥L :=
      ((MulAut.conj x).subgroupMap J).trans (MulEquiv.subgroupCongr hx.symm)
    have hshapeJ : IsL34Type ↥J ∨ IsA11Type ↥J := by
      rcases hLshape with h' | h'
      · exact Or.inl (IsL34Type.of_mulEquiv e.symm h')
      · exact Or.inr (IsA11Type.of_mulEquiv e.symm h')
    exact hJd (dvd_card_of_dvd_card_mulAut hk hd hd5 hJc.1 hshapeJ hdJ)
  ·
    push Not at hLJ
    have hJ'c : CFSG.IsComponent (J.map (MulAut.conj h).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj h) hJc
    have hLJne : L ≠ J := fun h' => hLY (h' ▸ hJY)
    have hJJ' : J ≠ J.map (MulAut.conj h).toMonoidHom := fun h' => hh h'.symm
    obtain ⟨B, hBL, hBe, hBc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (G := X) (by norm_num) L
    have hb2 : 2 ≤ CFSG.Open.pRank 3 L := by
      rw [open_pRank_eq]
      exact two_le_pRank_of_isL34Type_or_isA11Type hk hL.1 hLshape
    have h3J := prime_dvd_card_of_isComponent Nat.prime_three hO hJc
    have h3J' := prime_dvd_card_of_isComponent Nat.prime_three hO hJ'c
    have hJe := hk.omegaNotCentral X hX J hJc 3 Nat.prime_three (by norm_num) h3J
    have hJe' := hk.omegaNotCentral X hX _ hJ'c 3 Nat.prime_three (by norm_num) h3J'
    have h4 := add_two_le_pRank_of_three_components Nat.prime_three hL hJc hJ'c hLJne (hLJ h)
      hJJ' hBL hBe hBc hJe hJe'
    omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
