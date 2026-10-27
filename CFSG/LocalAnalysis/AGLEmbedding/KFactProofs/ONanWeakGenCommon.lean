module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.AGLEmbedding CFSG.AGLEmbedding.R3
  CFSG.Blueprint

theorem coverWeakGen_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} [Fact p.Prime]
    (e : X ≃* Y) (h : CoverWeakGen X p) : CoverWeakGen Y p := by
  intro K _ _ π hπ hker hperf hZ1 hZp hZc T
  refine h K (e.symm.toMonoidHom.comp π) (e.symm.surjective.comp hπ) ?_ hperf hZ1 hZp hZc T
  rw [← hker]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  exact ⟨fun h => e.symm.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

theorem coverWeakGen_of_check {M V : Type} [Inhabited M] {O : Ops M V} {c d : ℕ} [NeZero c]
    (Sp : OpsSpec O c d) {sA sB : String} {nregs : ℕ} {prog : List Op} {D : CpSpec}
    [hp : Fact D.p.Prime] (hp2 : D.p ≠ 2) (h : cpCheck O sA sB nregs prog D = true)
    (hNF : D.noFun = true) {Y : Type} [Group Y]
    (e : (NativeSporadic.seedMonoid c d 1 sA sB)ˣ ≃* Y) : CoverWeakGen Y D.p := by
  have : Finite (NativeSporadic.seedMonoid c d 1 sA sB)ˣ := inferInstance
  exact coverWeakGen_of_mulEquiv e
    (coverWeakGen_of_coverPointDatum hp2 (coverPointDatum_of_check Sp hp.out h hNF))

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
