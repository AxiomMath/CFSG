module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
import CFSG.RankThree.PartOne.S8.ResidualBound
import CFSG.RankThree.PartOne.LIT.RankPSL3
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.LIT

section Centre

variable {F : Type} [Field F]

theorem pow_three_eq_one_of_mem_center {g : SpecialLinearGroup (Fin 3) F}
    (hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) : g ^ 3 = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have h : ((g ^ 3 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr3, map_one]
  exact Subtype.ext h

theorem card_center_sl_three_le :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) ≤ 3 := by
  have e := SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  rw [Nat.card_congr e.toEquiv]
  rw [Fintype.card_fin]
  exact card_rootsOfUnity F 3

theorem eq_bot_or_eq_center_of_le_center [Finite F] (N : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hN : N ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F)) :
    N = ⊥ ∨ N = Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨g, hgN⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hg3 : (g : SpecialLinearGroup (Fin 3) F) ^ 3 = 1 :=
    pow_three_eq_one_of_mem_center (hN hgN)
  have hord : orderOf (g : SpecialLinearGroup (Fin 3) F) = 3 := by
    have hdvd : orderOf (g : SpecialLinearGroup (Fin 3) F) ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun h1 => hg1 (Subtype.ext h1))
    · exact h
  have hz : Subgroup.zpowers (g : SpecialLinearGroup (Fin 3) F) ≤ N :=
    (Subgroup.zpowers_le).mpr hgN
  have h3 : 3 ≤ Nat.card N := by
    calc 3 = Nat.card (Subgroup.zpowers (g : SpecialLinearGroup (Fin 3) F)) := by
          rw [Nat.card_zpowers, hord]
      _ ≤ Nat.card N := Subgroup.card_le_of_le hz
  exact Subgroup.eq_of_le_of_card_ge hN (card_center_sl_three_le.trans h3)

end Centre

section Rank

variable {f : ℕ}

theorem pRank_sl_three_le {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 f))) ≤ 2 := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
    (specialLinearGroupEquivStatedSL 3 (GaloisField 2 f))]
  have hH : ∀ h ∈ StatedSL 3 (GaloisField 2 f), (h : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)).det = 1 :=
    fun h hh => by
      have := MonoidHom.mem_ker.mp ((statedSL_eq_det_ker 3 (GaloisField 2 f)) ▸ hh)
      simpa [Units.ext_iff] using this
  exact pRank_le_two_of_det_gl hr (natCast_ne_zero_of_charTwo hr hr2) (by simp)
    (StatedSL 3 (GaloisField 2 f)) hH

theorem pRank_psl_three_le (hf : 1 ≤ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup
      (SpecialLinearGroup (Fin 3) (GaloisField 2 f) ⧸
        Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f)))) ≤ 2 := by
  have hproj : projSL 3 (GaloisField 2 f) = projImage (StatedSL 3 (GaloisField 2 f)) := by
    rw [statedSL_eq_det_ker]
    rfl
  have e1 : (SpecialLinearGroup (Fin 3) (GaloisField 2 f) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f))) ≃*
        StatedProj (StatedSL 3 (GaloisField 2 f)) :=
    projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 f)
  have e2 : (SpecialLinearGroup (Fin 3) (GaloisField 2 f) ⧸
      Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f))) ≃*
        projSL 3 (GaloisField 2 f) :=
    (e1.trans (statedProjEquiv (StatedSL 3 (GaloisField 2 f)))).trans
      (MulEquiv.subgroupCongr hproj.symm)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e2]
  exact pRank_projSL_three_le hf (GaloisField.card 2 f (by omega)) hr hr2

end Rank

theorem sqtkGroup_of_sl3_cover {Lb K : Type} [Group Lb] [Finite Lb] [Group K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (e : Lb ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))
    (h : Lb →* K) (hs : Function.Surjective h) (hker : h.ker ≤ Subgroup.center Lb)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K) :
    CFSG.Quasithin.SQTKGroup K := by
  refine ⟨?_, ?_⟩
  · set h' : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* K := h.comp e.symm.toMonoidHom
      with hh'
    have hs' : Function.Surjective h' := hs.comp e.symm.surjective
    have hker' : h'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f)) := by
      intro x hx
      have hz : e.symm x ∈ Subgroup.center Lb := hker hx
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.symm.injective
      simpa using hz (e.symm g)
    have eK := QuotientGroup.quotientKerEquivOfSurjective h' hs'
    refine CFSG.Quasithin.G11.tc_of_isStronglyQuasithin ?_
    rw [CFSG.SectionRank.isStronglyQuasithin_iff]
    intro r hr hr2
    rcases eq_bot_or_eq_center_of_le_center h'.ker hker' with hbot | hcen
    · have eK' : SpecialLinearGroup (Fin 3) (GaloisField 2 f) ≃* K :=
        (QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans eK
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt eK']
      exact pRank_sl_three_le hr hr2
    · have eK' : (SpecialLinearGroup (Fin 3) (GaloisField 2 f) ⧸
          Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f))) ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hcen.symm).trans eK
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt eK']
      exact pRank_psl_three_le hf hr hr2
  · intro H N _ hsimple
    by_cases hcomm : ∀ a b : H ⧸ N, a * b = b * a
    · exact CFSG.RankThree.PartOne.catalog_of_comm_simple _ hcomm
    · push Not at hcomm
      exact hbridge (H ⧸ N) hcomm (hcat H N ‹_› hsimple hcomm)

end CFSG.HardMathSupport.Curtis.Coordinator
