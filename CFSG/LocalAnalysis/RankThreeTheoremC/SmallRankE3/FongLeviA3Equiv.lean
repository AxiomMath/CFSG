module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSL4Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSL4
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open

theorem a3_leviSurj_of_equiv {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 4) F) :
    LeviSurj p K₀ z
      (Matrix.SpecialLinearGroup (Fin 3) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  obtain ⟨U₀, hU₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 4)
      (by norm_num)
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport e S.hpar U₀
  have hU₀' : (U₀ : Set (Matrix.SpecialLinearGroup (Fin 4) F)) =
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 4 F :
        Set (Matrix.SpecialLinearGroup (Fin 4) F)) :=
    congrArg (fun H : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F) =>
      (H : Set (Matrix.SpecialLinearGroup (Fin 4) F))) hU₀
  have hB : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 4 F ≤ P := by
    rw [hU₀', CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular] at hN
    exact hN
  obtain ⟨hPI, -⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.borel_overgroups P hB
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  have hIne : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.borelOvergroupCuts P).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hP
    rw [hPI, hempty, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer_empty]
  have hI : ∀ i ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.borelOvergroupCuts P,
      1 ≤ i ∧ i < 4 := fun i hi => by
    obtain ⟨h1, h2, -⟩ := hi
    exact ⟨h1, h2⟩
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt e] at h1
    exact h1
  have hp2 : p ≠ 2 := by
    have := S.hp5
    omega
  have hpq : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro hdvd
    have h2 := two_le_pRank_sl4_of_dvd S.hp hp2 hdvd
    exact absurd (h2.trans hKr) (by norm_num)
  have hzP' : z' ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 4 F
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.borelOvergroupCuts P) := by
    rw [← hPI]
    exact hz'P
  have hLS := sl4_leviSurj h4 S.hp S.hp5 hKr hpq hI hIne hzord hzP'
  rw [← hPI] at hLS
  have hfin := LeviSurj.map φ hφ hLS
  rw [hPK₀, hz'z] at hfin
  exact hfin

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
