module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.ComponentClassification.GrSLit.HeldFix

theorem mem_conjClass_t0_of_fixCard
    {p : Equiv.Perm (Fin 8330)} (hp : p ∈ heP) (hp2 : orderOf p = 2) (hf : fixCard p = 346) :
    p ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  rcases involution_conj_cases hp hp2 with h | ⟨c, -, rfl⟩
  · exact h
  · rw [fixCard_conj, fixCard_heT1] at hf
    exact absurd hf (by norm_num)

theorem mem_conjClass_t0_of_tab
    {t : Tab} {p : Equiv.Perm (Fin 8330)} (ht : TabRep t p) (hp : p ∈ heP)
    (h2 : comp 8330 t t = idTab 8330) (h1 : t ≠ idTab 8330) (hf : heGSFix t = 346) :
    p ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine mem_conjClass_t0_of_fixCard hp (orderOf_eq_prime ?_ ?_) ?_
  · rw [sq]
    exact ((ht.comp ht).eq_iff TabRep.idTab).1 h2
  · exact fun h => h1 ((ht.eq_iff TabRep.idTab).2 h)
  · rw [fixCard_eq_countP ht.2]
    exact hf

theorem hfCW_append (a b : List ℕ) : hfCW (a ++ b) = hfCW a * hfCW b := by
  simp only [hfCW, List.map_append, List.prod_append]

theorem lt_of_mem_hfRep {w : List ℕ} (hw : ∀ j ∈ w, j < 9) (k : ℕ) :
    ∀ j ∈ hfRep k w, j < 9 := by
  intro j hj
  simp only [hfRep, List.mem_flatten, List.mem_replicate] at hj
  obtain ⟨l, ⟨-, rfl⟩, hjl⟩ := hj
  exact hw j hjl

theorem heGSXWord_lt : ∀ j ∈ heGSXWord, j < 9 := by decide

theorem hfCW_mem_C1
    {w : List ℕ}
    (hw : ∀ j ∈ w, j < 9) : hfCW w ∈ centralizerIn heP heT1P := by
  rw [← heInnerGrp1_eq]
  exact hfCW_mem hw

theorem heGSX_pow :
    hfCW heGSXWord ^ 12 = 1 := by
  rw [← hfCW_rep]
  exact ((tabRep_hfCTab (lt_of_mem_hfRep heGSXWord_lt 12)).eq_iff TabRep.idTab).1
    heGS_twoB_check

end CFSG.ComponentClassification.GrSLit.HeGS
