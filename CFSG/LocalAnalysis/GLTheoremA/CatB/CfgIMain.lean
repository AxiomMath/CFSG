module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgILayer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgISimple
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgILift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

@[expose] def CfgIRankRow (p : ℕ) (row : S8.Row) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], catalogIs (Q ⧸ Subgroup.center Q) row.Iq →
    Nat.card (Subgroup.center Q) = row.Iz →
    ∃ E : Subgroup Q, IsElemAbelian p E ∧
      p ^ (row.rank - 1) * Nat.card (E ⊓ Subgroup.center Q : Subgroup Q) ≤ Nat.card E

@[expose] def CfgIRankS (p : ℕ) : Prop :=
  ∀ row : S8.Row, p = row.prime → CfgIRankRow p row

section Certs


theorem cfgI_isComponent
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (L D : Subgroup G) (row : S8.Row)
    (hI : S8.RowI row p (S8.cfgI p L D)) :
    GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) (S8.cfgI p L D) := by
  obtain ⟨⟨i, hi, ⟨e⟩⟩, -⟩ := hI
  have hs : IsSimpleGroup (PSimple p (GLAPLayer p (L ⊓ Subgroup.centralizer (D : Set G)))) :=
    (MulEquiv.isSimpleGroup_congr e).2 (Iq_isSimple row i hi)
  exact glaPLayer_isComponent_of_isSimple hp hs

theorem cfgIAt_of_S
    {G : Type} [Group G] [Finite G] {p : ℕ} (hS : CfgIRankS p) : S8.L89.CfgIAt G p := by
  intro x L row c _ _ _
  have hpr : p = row.prime := c.hData.1
  have hprime : p.Prime := by
    rw [hpr]
    cases row <;> norm_num [S8.Row.prime]
  haveI : Fact p.Prime := ⟨hprime⟩
  have hRowI : S8.RowI row p (S8.cfgI p L c.D) := c.hData.2.2.1
  refine ⟨cfgI_isComponent hprime L c.D row hRowI, ?_⟩
  obtain ⟨hcat, hcard⟩ := hRowI
  obtain ⟨Ebar, hE, hb⟩ := hS row hpr (PQuot p (S8.cfgI p L c.D)) hcat hcard
  exact exists_cfgI_lift Ebar hE hb

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
