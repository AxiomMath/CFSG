module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AHr
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm8
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AOm10
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQA6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQCases
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Big
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp8
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 S265

private theorem catalogIs_tyA {G : Type} [Group G] (h : catalogIs G tyA) :
    catalogIs G S9.isD4two ∨ catalogIs G tyOm10m ∨ catalogIs G S9.isSp6two ∨
      catalogIs G tySp8 ∨ catalogIs G tyAlt6 := by
  obtain ⟨i, hi | hi | hi | hi | hi, f⟩ := h
  · exact Or.inl ⟨i, hi, f⟩
  · exact Or.inr (Or.inl ⟨i, hi, f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, f⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, f⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, f⟩)))


theorem quFamA_holds
    : QUFamA := by
  intro p Ω _ _ S B T x b h hp hcat
  subst hp
  have hN := h.nlAct
  have hDJ : Dgrp b x ≤ Subgroup.centralizer ((Ipart 3 S b : Subgroup Ω) : Set Ω) := by
    refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_,
      Set.singleton_subset_iff.2 (Subgroup.mem_centralizer_iff.2 fun y _ => h.cfg.xcen y)⟩)
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      (Subgroup.mem_centralizer_iff.1 (hN.comp.1 hy).2 b (Set.mem_singleton b)).symm
  have hDe : IsElemAbelian 3 (Dgrp b x) := h.cfg.elem.mono hN.le
  rcases catalogIs_tyA hcat with hJ | hJ | hJ | hJ | hJ
  · exfalso
    by_cases hinn : ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (Ipart 3 S b : Set Ω),
        chevAut 3 (Ipart 3 S b) ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 (Ipart 3 S b))
    · exact hN.false_of_d4two_inner h.cfg.elem hJ hinn
        ((card_mul_le_rank_d4two hN.comp hDe hDJ hJ).trans h.cfg.rank)
    · exact h.cfg.false_of_d4two_outer D4Y.d4BigCoreAt_holds hJ hinn
  · exfalso
    have h81 := card_mul_le_rank_om10minus hN.comp hDe hDJ hJ
    have hr := h.cfg.rank
    exact hN.false_of_om10minus h.cfg.elem hJ (by omega)
  · exfalso
    by_cases hr : 27 * Nat.card (Dgrp b x) ≤ Nat.card B
    · exact false_of_sp6_big hN h.cfg.elem hJ hr
    · exact h.false_of_sp6two_r2 hJ (not_le.1 hr)
  · exact quConcl_of_sp8 h hJ
  · exact (h.cfg.false_of_alt6 hJ).elim

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
