module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12Check

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs

open CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem side_data
    (A : Subgroup X12) (Al : List X12) (hA : ∀ y, y ∈ A ↔ y ∈ Al)
    (Kl : List X12) (hKnd : Kl.Nodup)
    (hKn : ∀ x ∈ Kl, nrmTest Al (Al.map enc) (Al.take 3) x = true)
    (hKc : ∀ x ∈ XlX, nrmTest Al (Al.map enc) (Al.take 3) x = true → x ∈ Kl)
    (Ql : List X12) (hQnd : Ql.Nodup) (hQK : ∀ q ∈ Ql, q ∈ Kl) (hQ1 : (1 : X12) ∈ Ql)
    (hQmul : ∀ p ∈ Ql, ∀ q ∈ Ql, p * q ∈ Ql) (hQnorm : ∀ k ∈ Kl, ∀ q ∈ Ql, k * q * k⁻¹ ∈ Ql)
    (hQpow : ∀ q ∈ Ql, q ^ (2 ^ 5) = 1) (hQcent : ∀ y ∈ Kl, (∀ q ∈ Ql, y * q = q * y) → y ∈ Ql)
    (hQA3 : ∀ b ∈ Kl, b ≠ 1 → b ^ 3 = 1 →
      4 < (Ql.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length)
    (hratio : Kl.length / Ql.length = 6) :
    (∀ x, x ∈ Subgroup.normalizer (A : Set X12) ↔ x ∈ Kl) ∧
      Nat.card ↥(Subgroup.normalizer (A : Set X12)) = Kl.length ∧
      GoodLocal (Subgroup.normalizer (A : Set X12)) := by
  have hpre : ∀ a ∈ Al.take 3, a ∈ Al := fun a ha => List.mem_of_mem_take ha
  have hK : ∀ x, x ∈ Subgroup.normalizer (A : Set X12) ↔ x ∈ Kl := by
    intro x
    rw [mem_normalizer_of_lists A Al hA x]
    constructor
    · intro h
      exact hKc x (mem_XlX x) ((nrmTest_iff hpre).2 h)
    · intro h
      exact (nrmTest_iff hpre).1 (hKn x h)
  refine ⟨hK, card_of_list hKnd hK, ?_⟩
  exact goodLocal_of_lists _ Kl hK hKnd Ql hQnd hQK hQ1 hQmul hQnorm hQpow hQcent hQA3
    (by rw [hratio]; exact not_dvd_chi0_of_lt (by norm_num) (by norm_num))

theorem m12_localPair
    : LocalPair X12 := by
  obtain ⟨hlen, hnd, h1, hmul, hpow⟩ := s0_facts
  obtain ⟨hA1len, hA2len⟩ := a_facts
  obtain ⟨hK1len, hK1nd, hK1n, hK1c⟩ := k1_facts
  obtain ⟨hK2len, hK2nd, hK2n, hK2c⟩ := k2_facts
  obtain ⟨-, hQ1nd, hQ1K, hQ11, hQ1mul, hQ1norm, hQ1pow, hQ1cent, hQ1A3, hQ1r⟩ := q1_facts
  obtain ⟨-, hQ2nd, hQ2K, hQ21, hQ2mul, hQ2norm, hQ2pow, hQ2cent, hQ2A3, hQ2r⟩ := q2_facts
  obtain ⟨hgenmem, hwA, hwB⟩ := gen_facts
  obtain ⟨S₀, hS₀⟩ := subgroupOfList_exists S0X h1 hmul
  have hS₀card : Nat.card ↥S₀ = 64 := by rw [card_of_list hnd hS₀, hlen]
  have hS₀2 : IsPGroup 2 S₀ := by
    intro g
    exact ⟨6, Subtype.ext (hpow _ ((hS₀ _).1 g.2))⟩
  have hXcard : Nat.card X12 = 95040 := m12_card
  have hS₀i : ¬ 2 ∣ S₀.index := by
    have h := Subgroup.card_mul_index S₀
    rw [hS₀card, hXcard] at h
    have : S₀.index = 1485 := by omega
    rw [this]
    omega
  have hA₁ : ∀ y, y ∈ canonZ S₀ ↔ y ∈ A1X := by
    intro y
    simp only [mem_canonZ, hS₀, A1X, List.mem_filter, List.all_eq_true, beq_iff_eq]
  have hA₂ : ∀ y, y ∈ canonC S₀ ↔ y ∈ A2X := by
    intro y
    simp only [mem_canonC, hS₀, A2X, List.mem_filter, List.all_eq_true, beq_iff_eq]
  obtain ⟨hK₁mem, hcard₁, hgood₁⟩ := side_data (canonZ S₀) A1X hA₁ K1X hK1nd hK1n hK1c Q1X hQ1nd
    hQ1K hQ11 hQ1mul hQ1norm hQ1pow hQ1cent hQ1A3 hQ1r
  obtain ⟨hK₂mem, hcard₂, hgood₂⟩ := side_data (canonC S₀) A2X hA₂ K2X hK2nd hK2n hK2c Q2X hQ2nd
    hQ2K hQ21 hQ2mul hQ2norm hQ2pow hQ2cent hQ2A3 hQ2r
  have hne₁ : Subgroup.normalizer (canonZ S₀ : Set X12) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hXcard] at hcard₁
    omega
  have hne₂ : Subgroup.normalizer (canonC S₀ : Set X12) ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hXcard] at hcard₂
    omega
  have hsup : Subgroup.normalizer (canonZ S₀ : Set X12) ⊔ Subgroup.normalizer (canonC S₀ : Set X12)
      = ⊤ := by
    set J' : Subgroup (Equiv.Perm (Fin 12)) :=
      (Subgroup.normalizer (canonZ S₀ : Set X12) ⊔
        Subgroup.normalizer (canonC S₀ : Set X12)).map NativeSporadic.M12.subtype with hJ'
    have hjg : ∀ g ∈ jGens, g ∈ J' := by
      intro g hg
      have := List.all_eq_true.1 hgenmem g hg
      obtain ⟨x, hx, hxg⟩ := List.any_eq_true.1 this
      rw [beq_iff_eq] at hxg
      refine ⟨x, ?_, hxg⟩
      rcases List.mem_append.1 hx with h | h
      · exact Subgroup.mem_sup_left ((hK₁mem x).2 h)
      · exact Subgroup.mem_sup_right ((hK₂mem x).2 h)
    have hword : ∀ w : List ℕ, (w.map fun i => jGens.getD i 1).prod ∈ J' := by
      intro w
      refine list_prod_mem fun g hg => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
      by_cases hi : i < jGens.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hjg _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact J'.one_mem
    have hMle : NativeSporadic.M12 ≤ J' := by
      have hcl : Subgroup.closure ({m12gA, m12gB} : Set (Equiv.Perm (Fin 12))) ≤ J' := by
        rw [Subgroup.closure_le]
        intro g hg
        rcases hg with rfl | rfl
        · rw [← hwA]
          exact hword wordA
        · rw [← hwB]
          exact hword wordB
      rwa [← m12_eq] at hcl
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hMle x.2
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  refine ⟨S₀, _, _, hS₀2, hS₀i, ?_, ?_, hne₁, hne₂, hsup, hgood₁, hgood₂⟩
  · exact fun α hα => canonical_normalizer canonZ canonZ_map α hα
  · exact fun α hα => canonical_normalizer canonC canonC_map α hα

end CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Blueprint

theorem pairsFor_M12
    : PairsFor (TypeSporadic .M12) := by
  have : Finite (NativeSporadic.Carrier .M12) := inferInstanceAs (Finite M12Pairs.X12)
  exact pairsFor_of_localPair .M12 M12Pairs.m12_localPair

end CFSG.QuasithinUnique.Vol2Native.L239
