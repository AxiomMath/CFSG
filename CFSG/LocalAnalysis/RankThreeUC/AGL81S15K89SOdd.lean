module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionY
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.RankThree.PartTwo.Sec21

theorem glb_of_spe {X : Type} [Group X] {N : Subgroup X}
    (h : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) : GLBStronglyEmbedded 3 N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun g hg => ?_⟩
  exact h3 g⁻¹ (by simpa using hg)

theorem isCyclic_of_spe {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) (hr : CFSG.Open.pRank 3 N ≤ 1)
    {R : Subgroup X} (hR : IsPGroup 3 R) : IsCyclic ↥R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPN⟩ := exists_sylow_le_of_glbStronglyEmbedded (glb_of_spe hN)
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  have hle : R.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup X) := by
    rintro _ hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hRQ hx)
  have hpg : IsPGroup 3 (R.map (MulAut.conj g).toMonoidHom) := hR.map _
  have hr' : CFSG.pRank 3 ↥N ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3
        Nat.prime_three.one_lt N]
    exact hr
  have hcyc : IsCyclic ↥(R.map (MulAut.conj g).toMonoidHom) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      (hle.trans hPN) hpg hr'
  have e : R ≃* R.map (MulAut.conj g).toMonoidHom :=
    Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem oddIndex_noChar (hW : KFactThreeRankOneOvergroupL32) (hI : LThreeTwoCoreOdd)
    (G : Type) [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G) (N : Subgroup G)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) (hr : CFSG.Open.pRank 3 N ≤ 1)
    (Y : Subgroup G) (hYN : Y ≤ N) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ¬ 2 ∣ N.index := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : ∀ R : Subgroup G, IsPGroup 3 R → IsCyclic R := fun R hR => isCyclic_of_spe hN hr hR
  set I : Subgroup G := CFSG.pPrimeCore 3 G with hIdef
  have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
  have hI3 : ¬ 3 ∣ Nat.card I := fun h => absurd (Nat.Coprime.eq_one_of_dvd hcop h) (by norm_num)
  have hY3 : 3 ∣ Nat.card Y :=
    (isLThreeTwo_three_dvd_card hY).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)))
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hY3
  set A : Subgroup G := Subgroup.zpowers ((a₀ : Y) : G) with hAdef
  have hAord : orderOf ((a₀ : Y) : G) = 3 := (Subgroup.orderOf_coe a₀).trans ha₀
  have hA : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hAord]
  have hAY : A ≤ Y := Subgroup.zpowers_le.mpr a₀.2
  have hAN : A ≤ N := hAY.trans hYN
  set X0 : Subgroup G := Subgroup.normalClosure (A : Set G) with hXdef
  have hXn : X0.Normal := Subgroup.normalClosure_normal
  have hAX : A ≤ X0 := Subgroup.subset_normalClosure
  have hX3 : 3 ∣ Nat.card X0 := by rw [← hA]; exact Subgroup.card_dvd_of_le hAX
  have hXtop : X0 ⊔ N = ⊤ := sup_eq_top_of_normal (glb_of_spe hN) hXn hX3
  set H : Subgroup G := I ⊔ N with hHdef
  have hIH : I ≤ H := le_sup_left
  have hNH' : N ≤ H := le_sup_right
  have hAH : A ≤ H := hAN.trans hNH'
  have hApg : IsPGroup 3 A := IsPGroup.iff_card.mpr ⟨1, by rw [hA, pow_one]⟩
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    omega
  have hNA : Subgroup.normalizer (A : Set G) ≤ N := hN.normalizer_le hAbot hApg hAN
  have hNH : Subgroup.normalizer (A : Set G) ≤ H := hNA.trans hNH'
  have hcent : I ⊓ Subgroup.centralizer (A : Set G) ≤ N := fun g hg =>
    hNA (Subgroup.centralizer_le_normalizer (A : Set G) hg.2)
  have hIodd : ¬ 2 ∣ (I ⊓ N).relIndex I :=
    hI G hK I N Y A inferInstance hI3 hA hAY hYN hY hcent
  have hsimple : IsSimpleGroup (Red X0 I) := red_isSimple hcyc hA hAX le_rfl
  obtain ⟨a, b, hab⟩ := red_not_comm hA hAX hAY hY
  have hcat : Open.IsCatalogGroup (Red X0 I) := hK X0 (X0 ⊓ I) inf_le_left hsimple ⟨a, b, hab⟩
  have hWdich := hW (Red X0 I) hsimple ⟨a, b, hab⟩ hcat (red_isCyclic hcyc) (redImg X0 A)
    (redW X0 H) (zToRed X0 Y).range (card_redImg hA hAX)
    (normalizer_redImg_le hcyc hA hAX hAH hNH hIH)
    (by
      rintro _ ⟨z, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(z : G), z.2.1⟩,
        Subgroup.mem_subgroupOf.mpr (hNH' (hYN z.2.2)), rfl⟩)
    (by
      intro k hk
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
      exact ⟨⟨(y : G), hAX (Subgroup.mem_subgroupOf.mp hy), hAY (Subgroup.mem_subgroupOf.mp hy)⟩,
        rfl⟩)
    (isLThreeTwo_range hA hAX hAY hY)
  have hWodd : ¬ 2 ∣ (redW X0 H).index := by
    rcases hWdich with h | h
    · rw [h, Subgroup.index_top]; omega
    · exact h
  have h1 : N.relIndex H * H.index = N.index := Subgroup.relIndex_mul_index hNH'
  have h2 : N.relIndex H = (I ⊓ N).relIndex I := by
    rw [hHdef, relIndex_sup_eq_of_normal inferInstance N, inf_comm, Subgroup.inf_relIndex_right]
  have h4 : H.index = (redW X0 H).index := by
    rw [index_redW hIH]
    have hXH : X0 ⊔ H = ⊤ := top_le_iff.mp (hXtop ▸ sup_le_sup le_rfl hNH')
    have := relIndex_sup_eq_of_normal hXn H
    rw [hXH, Subgroup.relIndex_top_right] at this
    exact this
  rw [← h1, h2, h4]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hIodd h
  · exact hWodd h

end CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof
