module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem i112v_isSUThreeTwoPow_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSUThreeTwoPow X) : IsSUThreeTwoPow Y := by
  obtain ⟨K, hK, hf, n, h1, h2, h3, hcard, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, n, h1, h2, h3, hcard, ⟨e.symm.trans f⟩⟩

theorem i112v_exc_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X ∨ IsSLThreeExc X ∨ IsSUThreeExc X) :
    IsHatSix Y ∨ IsHatSeven Y ∨ IsHatMTwentyTwo Y ∨ IsSLThreeExc Y ∨ IsSUThreeExc Y := by
  rcases h with h | h | h | h | h
  · exact Or.inl (i112f_isHatSix_of_mulEquiv e h)
  · exact Or.inr (Or.inl (i112f_isHatSeven_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (i112f_isHatMTwentyTwo_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (i112f_isSLThreeExc_of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (i112f_isSUThreeExc_of_mulEquiv e h))))

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem i112v_bar (hS : GLStanding G m p) {X B L : Subgroup G} (hB : IsElemAbelian p B)
    (hBX : B ≤ X) (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    p.Prime ∧ p ≠ 2 ∧ X ≠ ⊤ ∧ CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) ∧
      GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ ∧ IsElemAbelian p (barX p X B) ∧
      GLATwoLocalRank p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ CFSG.Open.pRank p (barX p X B) ∧
      GLAPComponent p ⊤ (barX p X L) ∧
      ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  obtain ⟨hp, hp2, -, -⟩ := hS.beta
  have : Fact p.Prime := ⟨hp⟩
  have hXne : X ≠ ⊤ := by
    rintro rfl
    have : IsSimpleGroup G := hS.simple
    apply hnL
    rcases i112f_eq_bot_or_top_of_isSubnormal hL.2.1 with h | h
    · have hN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
    · have hN : Subgroup.normalizer ((⊤ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
  have hXK : CFSG.Open.IsKGroup ↥X := isKGroup_of_isKProper hS.kProper hXne
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨hp, hp2, hXne, isKGroup_quotient' hXK N, glaPPrimeCore_quotient_eq_bot hp,
    isElemAbelian_barX hB, ?_, i112b_glaPComponent_of_isComponentOf
      (glaPPrimeCore_quotient_eq_bot hp) hL.2.2.1, ?_⟩
  · rw [rank_barX_of_isPGroup hp hBp hBX]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  · intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, hBX hb⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, hBX hb⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2

end CFSG.HardMathSupport.Solomon.Coordinator
