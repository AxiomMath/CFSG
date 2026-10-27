module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgILayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem isSimpleGroup_of_tyUnTwo {G : Type} [Group G] {n : ℕ} (h : catalogIs G (tyUnTwo n)) :
    IsSimpleGroup G := by
  obtain ⟨i, hi, e⟩ := h
  refine S10.isSimple_of_catalogIs_twistedA ⟨i, ?_, e⟩
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q => exact trivial
    | _ => exact hi.elim
  | _ => exact hi.elim

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

theorem QUNL.nlAct_of_simple {S B T : Subgroup Ω} {x b : Ω} (h : QUNL p S B T x b)
    (hs : IsSimpleGroup (PSimple p (Ipart p S b))) :
    NLAct p (S ⊓ cx b) (Ipart p S b) B (Dgrp b x) := by
  have hc := h.cfg
  have hJ : GLAPComponent p (S ⊓ cx b) (Ipart p S b) :=
    S8.CfgI.glaPLayer_isComponent_of_isSimple hc.prime hs
  have hBb : B ≤ cx b := fun g hg => Subgroup.mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact isElemAbelian_commute hc.elem hc.hb hg
  have hBX : B ≤ Subgroup.normalizer ((S ⊓ cx b : Subgroup Ω) : Set Ω) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g,
        Subgroup.le_normalizer (hBb hg)⟩
  refine nlAct_of_nl hc.prime hc.elem hJ (P65.le_normalizer_glaPLayer hBX) ?_ h.nl
  refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨⟨hc.hb, ?_⟩,
    Set.singleton_subset_iff.2 ⟨hc.xB, Subgroup.mem_centralizer_iff.2 fun y _ => hc.xcen y⟩⟩)
  exact Subgroup.mem_centralizer_iff.2 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (hJ.1 hy).2 b (Set.mem_singleton b)).symm

end CFSG.LocalAnalysis.GLTheoremA.S265

end
