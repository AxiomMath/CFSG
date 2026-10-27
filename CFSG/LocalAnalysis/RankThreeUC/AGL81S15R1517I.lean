module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517C
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Cut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KOutLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem five_le_of_mem_sigmaM {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h11 : Row1511 G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M) : 5 ≤ p := by
  have hpp : p.Prime := sigmaA_prime p hp.1
  have h2 : p ≠ 2 := sigmaA_odd p hp.1
  have h3 : p ≠ 3 := fun h => (show 3 ∉ sigmaM G M from h11) (h ▸ hp)
  by_contra hlt
  have : p < 5 := by omega
  interval_cases p <;> simp_all <;> exact absurd hpp (by decide)

theorem isK4143Shape_of_bad {p : ℕ} {S : Type} [Group S] (h : Bad1517 p S) : IsK4143Shape S := by
  obtain ⟨d, hd, he⟩ := bad1517_iff.1 h
  refine ⟨d, ?_, he⟩
  rcases bad1517_iff_aux_cases hd with
    ⟨Q, hd', hQ, -⟩ | ⟨Q, hd', hQ, -⟩ | ⟨Q, hd', hQc, -⟩ | ⟨Q, hd', hQc, -⟩
  · rw [hd']
    exact hQ
  · rw [hd']
    exact hQ
  · rw [hd']
    exact hQc
  · rw [hd']
    exact hQc

section BarTransfer

variable {X : Type} [Group X] [Finite X]

theorem xlevel_out1517_gen (hK4143 : K4143) (hD : K421Data) (hN : K421NonTransLin)
    (hKSM : KSMOdd) (hRank : LieOddRankChev) (hOutLin : KOutLin) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hXp : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) (hbad : Bad1517 p ↥Ls) :
    Out1517 X p ∧ CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 ∧
      ((IsLinTwo 6 ↥Ls ∨ IsLinTwo 7 ↥Ls) →
        ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 → NonTrans1517 E) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hZ, ⟨e⟩⟩ := lift_centre_trivial_of_bad hKSM hX hLs hL hbad
  have h3L : CFSG.Open.pRank 3 L = 3 := pRank_lift_three_of_bad hRank hX hLs hL hbad
  have hLn : L.Normal := lift_normal_of_pRank_three hL.1 hZ h3L hX3
  have hX3' : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 := by
    have := CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt (le_top : L ≤ ⊤)
    omega
  haveI hSn : (barO2 L).Normal :=
    Subgroup.Normal.map hLn (QuotientGroup.mk' (CFSG.pCore 2 X)) (QuotientGroup.mk'_surjective _)
  have hbad' : Bad1517 p ↥(barO2 L) := bad1517_of_equiv e.symm hbad
  have hq : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hshape := isK4143Shape_of_bad hbad'
  have h3S : CFSG.Open.pRank 3 (barO2 L) = 3 :=
    (pRank_barO2_eq hL.1 Nat.prime_three (by norm_num)).symm.trans h3L
  have hmapTop : barO2 (⊤ : Subgroup X) = ⊤ := by
    unfold barO2
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
  have h3Y : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) = 3 := by
    have := pRank_barO2_eq_aux_eq (⊤ : Subgroup X) Nat.prime_three (by norm_num)
    rw [hmapTop] at this
    omega
  have hpY : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) := by
    have := pRank_barO2_eq_aux_eq (⊤ : Subgroup X) hp hp2
    rw [hmapTop] at this
    omega
  have hData : Data421 ↥(barO2 L) p := hD _ p hp hp5 hbad'
  have hOut := bad_pRank_or_out hRank hOutLin hp hbad'
  obtain ⟨hY, hYle⟩ :=
    out1517_of_data421_of_ne_two_gen hK4143 hp hp2 hq hZ hshape h3S h3Y hpY hOut hData
  refine ⟨out1517_of_bar hp hp2 hY, hX3', fun hlin => ?_⟩
  have hlin' : IsLinTwo 6 ↥(barO2 L) ∨ IsLinTwo 7 ↥(barO2 L) :=
    hlin.imp (isLinTwo_of_equiv e.symm) (isLinTwo_of_equiv e.symm)
  exact nonTrans_of_bar (nonTrans_of_normal hYle (hN _ hlin'))

end BarTransfer

end CFSG.LocalAnalysis.RankThreeUC.S15
