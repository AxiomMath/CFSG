module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158GInn3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (Tag adjointGroup)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr congr_mem_inner_iff
  innAutDerived_D4_three_cases)

theorem catalogD4_isD4any_isChevSimple {S : Type} [Group S]
    (h : catalogIs S (onLie fun i => ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2)) :
    catalogIs S isD4any ∧ IsChevSimple 2 S := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨q, rfl, hq⟩ := hi
    refine ⟨⟨.lie ⟨.D 4 q, hv⟩, hq, he⟩, Or.inl ⟨.lie ⟨.D 4 q, hv⟩, ?_, he⟩⟩
    show (TauCeti.LieTypeIndex.D 4 q).characteristic = 2
    rw [TauCeti.LieTypeIndex.characteristic_D, hq]
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])


theorem d4InnAutDerivedNotFG_holds : D4InnAutDerivedNotFG := by
  intro G _ _ X J b hJ hcat hb3 hb hmem hFG
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hD, hchev⟩ := catalogD4_isD4any_isChevSimple hcat
  obtain ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ := T158G.t158g_d4_model hD
  set β := MI.indAut 3 J b hb with hβdef
  have hβ3 : β ^ 3 = 1 := T156.indAut_pow_eq_one hb hb3
  set α := MulAut.congr e β with hαdef
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hβ3, map_one]
  have hαmem : α ∈ innAutDerived ↥(adjointGroup Tag.D4 F) := (mem_innAutDerived_congr e).2 hmem
  rcases innAutDerived_D4_three_cases hαmem hα3 with ⟨h, hh⟩ | ⟨g, a, ε, hε, hαeq⟩
  ·
    have hinn : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 J) :=
      (congr_mem_inner_iff e β).1 ⟨h, hh.symm⟩
    have hID : InnDiagOn 3 (Subgroup.zpowers b) J :=
      MI.inner_innDiag_any hJ hchev hb ((MI.indAut_mem_inner_iff hp hJ hb).1 hinn)
    rcases hFG with hF' | hG'
    · exact (MI.field_nonInnDiag_any hJ hF').2 hID
    · exact hG'.1.2 hID
  ·
    have hcube : centCard2 3 J b ^ 3 = card2 3 J := by
      rcases hFG with hF' | hG'
      · exact (FP.i91CentPartAt_of_stOrder (G := G) hp (by norm_num) (FQ.s10StOrderAt hp (by norm_num)))
          X J b hJ hchev hb3 hF'
      · exact hG'.2.2
    have hfix : FP.fixNum β = Nat.card ↥(fixSubgroup α) := by
      rw [← FP.fixNum_congr e β, FP.fixNum_eq_card_fixSub]
      rfl
    have hcard : twoPart (Nat.card (PSimple 3 J)) = 2 ^ (12 * n) := by
      rw [Nat.card_congr e.toEquiv]
      exact T158G.t158g_twoPart_card_adjointD4 hn hF
    rw [FP.centCard2_eq_twoPart_fixNum hb (FP.odd_card_center_pQuot hp (by norm_num) J),
      FP.card2_eq_twoPart_card_pSimple hp (by norm_num) J, ← hβdef, hfix, hcard] at hcube
    rcases T158G.t158g_d4_graph_fix hn hF hα3 g a hε hαeq with ⟨k, _, _, hk, ⟨eG⟩⟩ | ⟨π, F', _, _, hPi, hc, ⟨eP⟩⟩
    ·
      rw [Nat.card_congr eG.toEquiv, T158G.t158g_twoPart_card_adjointG2 hn hk, ← pow_mul] at hcube
      have := Nat.pow_right_injective le_rfl hcube
      omega
    ·
      obtain ⟨hcardG, h2S⟩ := T158G.t158g_card_projImage hPi hc
      have hS0 :
          Nat.card ↥(CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.slPi π 3 (2 ^ n) F')) ≠ 0 := by
        haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) F') :=
          Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F' →* _) (QuotientGroup.mk'_surjective _)
        exact Nat.card_pos.ne'
      have h2G : twoPart (Nat.card ↥(CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.glPi π 3 (2 ^ n) F'))) =
          2 ^ (3 * n) := by
        rw [hcardG, mul_comm _ 3, FP.twoPart_mul_odd (by decide) hS0, h2S]
      rw [Nat.card_congr eP.toEquiv, h2G, ← pow_mul] at hcube
      have := Nat.pow_right_injective le_rfl hcube
      omega

end CFSG.LocalAnalysis.GLTheoremA.T158

end
