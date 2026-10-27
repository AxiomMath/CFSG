module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSp6
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviConj
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open

theorem b3_leviSurj_of_equiv {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ}
    (S : E3Setting K K₀ B z p) {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    (e : ↥K ≃* CFSG.Open.StatedSp 3 F) :
    LeviSurj p K₀ z
        (Matrix.SpecialLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ∨
      LeviSurj p K₀ z ↥(CFSG.Open.StatedSp 2 F) := by
  obtain ⟨U₀, hU₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 3
  obtain ⟨φ, P, hφ, hrange, hPK₀, hN⟩ := parabolic_transport e S.hpar U₀
  have hU₀' : (U₀ : Set (CFSG.Open.StatedSp 3 F)) =
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent 3 F :
        Set (CFSG.Open.StatedSp 3 F)) :=
    congrArg (fun H : Subgroup (CFSG.Open.StatedSp 3 F) => (H : Set (CFSG.Open.StatedSp 3 F))) hU₀
  have hB : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.borelSubgroup 3 F ≤ P := by
    rw [hU₀', CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent] at hN
    exact hN
  have hP : P ≠ ⊤ := by
    intro h
    apply S.hne
    rw [← hPK₀, h, Subgroup.map_top, hrange]
  obtain ⟨hPI, -⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borel_overgroups P hB
  have hIne : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts F P).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hP
    rw [hPI, hempty, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer_empty]
  have hI : ∀ i ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts F P,
      1 ≤ i ∧ i ≤ 3 := fun i hi =>
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts_le P i hi
  have hzmem : z ∈ P.map φ := by
    rw [hPK₀]
    exact S.hzK₀
  obtain ⟨z', hz'P, hz'z⟩ := Subgroup.mem_map.mp hzmem
  have hzord : orderOf z' = p := by
    rw [← S.hz, ← hz'z]
    exact (orderOf_injective φ hφ z').symm
  have hKr : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedSp 3 F)) ≤ 1 := by
    have h1 := S.hKr
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv S.hp.one_lt e] at h1
    exact h1
  have hpq : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro hdvd
    have hle := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
      (K := F) (n := 3) (r := p) S.hp hdvd
    have h2 := le_trans hle hKr
    omega
  have hzP' : z' ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.flagStabilizer 3 F
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.borelCuts F P) := by
    rw [← hPI]
    exact hz'P
  have hLS := sp6_leviSurj h4 S.hp S.hp5 hKr hpq hI hIne hzord hzP'
  rw [← hPI] at hLS
  rcases hLS with hL | hL
  · left
    have hfin := LeviSurj.map φ hφ hL
    rw [hPK₀, hz'z] at hfin
    exact hfin
  · right
    have hfin := LeviSurj.map φ hφ hL
    rw [hPK₀, hz'z] at hfin
    exact hfin

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
