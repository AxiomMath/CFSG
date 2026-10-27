module

import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)

theorem fstdLin_three_dvd_card {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (h : SmallOrd I) : 3 ∣ Nat.card ↥I := by
  have hdvd : Nat.card (↥I ⧸ Subgroup.center ↥I) ∣ Nat.card ↥I :=
    Subgroup.card_quotient_dvd_card _
  rcases h with h1 | h1 <;> rw [h1] at hdvd <;> exact dvd_trans (by norm_num) hdvd

theorem fstdLin_glaPComponent {G : Type} [Group G] [Finite G] {X I : Subgroup G}
    (hI : IsComponentOf I X) (h : SmallOrd I) : GLAPComponent 3 X I :=
  CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hI
    (fstdLin_three_dvd_card h)

theorem fstdLin_ne_top {G : Type} [Group G] [Finite G] {I : Subgroup G} (h : SmallOrd I) :
    GLAPPrimeCore 3 ↥I ≠ ⊤ := by
  intro htop
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card ↥I) := by
    have h' := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)
    have htop' : CFSG.pPrimeCore 3 ↥I = ⊤ := htop
    rw [htop'] at h'
    simpa using h'
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (fstdLin_three_dvd_card h)

theorem fstdLin_pSimple_equiv {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (hI : CFSG.Open.IsQuasisimple ↥I) (h : SmallOrd I) :
    Nonempty (PSimple 3 I ≃* (↥I ⧸ Subgroup.center ↥I)) := by
  have hle : GLAPPrimeCore 3 ↥I ≤ Subgroup.center ↥I :=
    le_center_of_normal_of_isQuasisimple hI inferInstance (fstdLin_ne_top h)
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I) : ↥I →* PQuot 3 I).ker ≤
      Subgroup.center ↥I := by
    rw [QuotientGroup.ker_mk']
    exact hle
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hI.1 (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)) (QuotientGroup.mk'_surjective _) hker
  exact ⟨e.symm⟩

theorem fstdLin_card_pSimple {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (hI : CFSG.Open.IsQuasisimple ↥I) (h : SmallOrd I) :
    Nat.card (PSimple 3 I) = 25920 ∨ Nat.card (PSimple 3 I) = 360 := by
  obtain ⟨e⟩ := fstdLin_pSimple_equiv hI h
  rw [Nat.card_congr e.toEquiv]
  exact h

theorem fstdLin_card_psl_ne {b f : ℕ} {E : Type} [Field E] [Finite E] (hb : 2 ≤ b)
    (hE : Nat.card E = 2 ^ f) :
    Nat.card (StatedProj (StatedSL b E)) ≠ 25920 ∧ Nat.card (StatedProj (StatedSL b E)) ≠ 360 := by
  have hf : 1 ≤ f := by
    by_contra hlt
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hE, show f = 0 by omega] at h1
    simp at h1
  obtain ⟨-, h2, h3⟩ := CFSG.StandardType.ggAKFG_ordSL_good hb hf
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), hE]
  exact ⟨h2, h3⟩

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
