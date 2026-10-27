module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionY
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.RankThree.PartTwo.Sec21

theorem kFactLThreeTwoOddIndex_of (hW : KFactThreeRankOneOvergroupL32) (hI : LThreeTwoCoreOdd) :
    KFactLThreeTwoOddIndex := by
  intro N _ _ hK _hChar N₀ hN₀ hr Y hYN₀ _hsub hY
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : ∀ R : Subgroup N, IsPGroup 3 R → IsCyclic R := fun R hR =>
    isCyclic_of_isPGroup_three hN₀ hr hR
  set I : Subgroup N := CFSG.pPrimeCore 3 N with hIdef
  have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
  have hI3 : ¬ 3 ∣ Nat.card I := fun h => absurd (Nat.Coprime.eq_one_of_dvd hcop h) (by norm_num)
  have hY3 : 3 ∣ Nat.card Y :=
    (isLThreeTwo_three_dvd_card hY).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)))
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hY3
  set A : Subgroup N := Subgroup.zpowers ((a₀ : Y) : N) with hAdef
  have hAord : orderOf ((a₀ : Y) : N) = 3 := (Subgroup.orderOf_coe a₀).trans ha₀
  have hA : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hAord]
  have hAY : A ≤ Y := Subgroup.zpowers_le.mpr a₀.2
  have hAN₀ : A ≤ N₀ := hAY.trans hYN₀
  set X : Subgroup N := Subgroup.normalClosure (A : Set N) with hXdef
  have hXn : X.Normal := Subgroup.normalClosure_normal
  have hAX : A ≤ X := Subgroup.subset_normalClosure
  have hX3 : 3 ∣ Nat.card X := by
    rw [← hA]; exact Subgroup.card_dvd_of_le hAX
  have hXtop : X ⊔ N₀ = ⊤ := sup_eq_top_of_normal hN₀ hXn hX3
  set H : Subgroup N := I ⊔ N₀ with hHdef
  have hIH : I ≤ H := le_sup_left
  have hN₀H : N₀ ≤ H := le_sup_right
  have hAH : A ≤ H := hAN₀.trans hN₀H
  have hApg : IsPGroup 3 A := IsPGroup.iff_card.mpr ⟨1, by rw [hA, pow_one]⟩
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    omega
  have hNN₀ : Subgroup.normalizer (A : Set N) ≤ N₀ :=
    normalizer_le_of_glbStronglyEmbedded hN₀ hAN₀ hApg hAbot
  have hNH : Subgroup.normalizer (A : Set N) ≤ H := hNN₀.trans hN₀H
  have hcent : I ⊓ Subgroup.centralizer (A : Set N) ≤ N₀ := fun g hg =>
    hNN₀ (Subgroup.centralizer_le_normalizer (A : Set N) hg.2)
  have hIodd : ¬ 2 ∣ (I ⊓ N₀).relIndex I :=
    hI N hK I N₀ Y A inferInstance hI3 hA hAY hYN₀ hY hcent
  have hsimple : IsSimpleGroup (Red X I) := red_isSimple hcyc hA hAX le_rfl
  obtain ⟨a, b, hab⟩ := red_not_comm hA hAX hAY hY
  have hcat : Open.IsCatalogGroup (Red X I) := hK X (X ⊓ I) inf_le_left hsimple ⟨a, b, hab⟩
  have hWdich := hW (Red X I) hsimple ⟨a, b, hab⟩ hcat (red_isCyclic hcyc) (redImg X A) (redW X H)
    (zToRed X Y).range (card_redImg hA hAX)
    (normalizer_redImg_le hcyc hA hAX hAH hNH hIH)
    (by
      rintro _ ⟨z, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(z : N), z.2.1⟩,
        Subgroup.mem_subgroupOf.mpr (hN₀H (hYN₀ z.2.2)), rfl⟩)
    (by
      intro k hk
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
      exact ⟨⟨(y : N), hAX (Subgroup.mem_subgroupOf.mp hy), hAY (Subgroup.mem_subgroupOf.mp hy)⟩,
        rfl⟩)
    (isLThreeTwo_range hA hAX hAY hY)
  have hWodd : ¬ 2 ∣ (redW X H).index := by
    rcases hWdich with h | h
    · rw [h, Subgroup.index_top]; omega
    · exact h
  have h1 : N₀.relIndex H * H.index = N₀.index := Subgroup.relIndex_mul_index hN₀H
  have h2 : N₀.relIndex H = (I ⊓ N₀).relIndex I := by
    rw [hHdef, relIndex_sup_eq_of_normal inferInstance N₀, inf_comm, Subgroup.inf_relIndex_right]
  have h3 : H.index = (redW X H).index := by
    rw [index_redW hIH]
    have hXH : X ⊔ H = ⊤ := top_le_iff.mp (hXtop ▸ sup_le_sup le_rfl hN₀H)
    have := relIndex_sup_eq_of_normal hXn H
    rw [hXH, Subgroup.relIndex_top_right] at this
    exact this
  rw [← h1, h2, h3]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · exact hIodd h
  · exact hWodd h

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
