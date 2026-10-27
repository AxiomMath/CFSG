module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOrthSl3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviOrthRes
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMFlag
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

theorem tD4_leviSurj_of_equiv {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A}
    {p : ℕ} (S : E3Setting K K₀ B z p) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F) {f : ℕ}
    (hF : Nat.card F = 2 ^ f)
    (e : ↥K ≃* ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) :
    LeviSurj p K₀ z (Matrix.SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ∨
      ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ LeviSurj p K₀ z
        (↥(orthResDer F b c m) ⧸ Subgroup.center ↥(orthResDer F b c m)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))) :=
    Finite.of_surjective (⇑e) e.surjective
  obtain ⟨⟨U, hU⟩, hNU, -⟩ :=
    orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (le_refl 3)
      (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
      (Or.inr finrank_fin_two_fun)
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport e S.hpar U
  have hU' : (U : Set ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) =
      ((tailUnipotent 3 (minusTailForm F b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm F b c))) :
          Set ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) :=
    congrArg (fun H : Subgroup ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))) =>
      (H : Set ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c))))) hU
  have hB : (tailBorel 3 (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm F b c))) ≤ P := by
    rw [hU', hNU] at hN
    exact hN
  obtain ⟨s, d, hd, hPd⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_exists_eq_orthParab
      (le_refl 3) hirr hB
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  have hs1 : 1 ≤ s := by
    by_contra hcon
    have h0 : s = 0 := by omega
    subst h0
    apply hP
    rw [hPd, Subgroup.eq_top_iff']
    intro x
    rw [mem_orthParab]
    intro i
    have hdi : d i = 0 := by
      have h1 : d i ≤ d (Fin.last 0) := hd.mono.monotone (Fin.le_last i)
      have h2 : d (Fin.last 0) = 0 := hd.zero
      omega
    rw [hdi, tailFlag_zero, Submodule.map_bot]
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hKrE : CFSG.Open.pRank p
      (⊤ : Subgroup ↥(orthElementaryGroup (quadTail 3 (minusTailForm F b c)))) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt e] at h1
    exact h1
  have hp2 : p ≠ 2 := by
    have := S.hp5
    omega
  have hpq : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro hdvd
    have h2 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.orthMinus_two_le_pRank
      (le_refl 3) hF hirr S.hp hp2 hdvd
    exact absurd (h2.trans hKrE) (by norm_num)
  have hzP : z' ∈ orthParab 3 (minusTailForm F b c) d := by
    rw [← hPd]
    exact hz'P
  by_cases ht : d (Fin.last s) = 3
  · left
    have hLS := orth8_levi_sl3 hirr h4 hF S.hp S.hp5 hKrE hpq hd ht hzord hzP
    rw [← hPd] at hLS
    have hfin := LeviSurj.map φ hφ hLS
    rw [hPK₀, hz'z] at hfin
    exact hfin
  · right
    have hle : d (Fin.last s) ≤ 2 := by
      have := hd.last
      omega
    obtain ⟨m, hm, hLS⟩ := orth8_levi_res hirr h4 hF S.hp S.hp5 hKrE hpq hs1 hd hle hzord hzP
    refine ⟨m, hm, ?_⟩
    rw [← hPd] at hLS
    have hfin := LeviSurj.map φ hφ hLS
    rw [hPK₀, hz'z] at hfin
    exact hfin

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
