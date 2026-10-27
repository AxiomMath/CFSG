module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107Chev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithAll
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I107LabelAt : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple 2 S →
    ∃ lab : GLALabel, GLAInLambda2 lab ∧ Rk2IsLabel S lab

@[expose] def I107AutAt : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel) (p : ℕ), IsSimpleGroup S → Rk2IsLabel S lab →
    GLAInLambda2 lab → p.Prime → p ≠ 2 →
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ upA107 lab p

@[expose] def I107CoverAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X L : Subgroup G) (lab : GLALabel), p.Prime → p ≠ 2 →
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X L → Rk2IsLabel (PSimple p L) lab → GLAInLambda2 lab →
    ¬ exempt107 lab → 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) →
    twoRankLow107 lab + CFSG.Open.pRank 2 (Subgroup.center (LTilde p L)) ≤
      CFSG.Open.pRank 2 (⊤ : Subgroup (LTilde p L))

@[expose] def I107CatAt : Prop :=
  ∀ (S : Type) [Group S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → survivor107 lab →
    catalogIs S S9.isList107

theorem i107At_of_facts (hLab : I107LabelAt) (hAut : I107AutAt) (hCov : I107CoverAt) (hCat : I107CatAt)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I107At G p := by
  intro hp hp2 X L B r hX hL hchev hB hBN hr hk hm
  have hS : IsSimpleGroup (PSimple p L) := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
  obtain ⟨lab, hlab, hrk⟩ := hLab (PSimple p L) hS hchev
  have hlow : r ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) :=
    pRank_chevAut_ge hp hL hB hBN hk
  have hup : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (PSimple p L))) ≤ upA107 lab p :=
    hAut (PSimple p L) lab p hS hrk hlab hp hp2
  have hru : r ≤ upA107 lab p := le_trans hlow hup
  have hA3 : 3 ≤ upA107 lab p := le_trans hr hru
  have hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2 := by
    by_cases hex : exempt107 lab
    · exact Or.inl hex
    · right
      have hc := hCov G p X L lab hp hp2 hX hL hrk hlab hex (le_trans hr hlow)
      omega
  obtain ⟨hp3, hsurv⟩ := arith107 hlab hp hp2 hA3 hg
  exact ⟨hp3, hCat (PSimple p L) lab hS hrk hsurv⟩

end CFSG.LocalAnalysis.GLTheoremA

end
