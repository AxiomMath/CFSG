module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def U6CompRes : Prop :=
  ∀ (T : Type) [Group T], catalogIs T S9.isU6two → ∀ α : MulAut T, α ^ 3 = 1 → α ≠ 1 →
    ∀ L : Subgroup T, CFSG.Open.IsComponentOf L (fixSub α) →
      catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i)

theorem nontrivial_pSimple_isU6two {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hb : CatDistinct.OrderBridge) (h : catalogIs (PSimple 3 J) S9.isU6two) :
    Nontrivial (PSimple 3 J) := by
  have hc := CatDistinct.card_isU6two hb h
  exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)

theorem u6_of_residual (hb : CatDistinct.OrderBridge) (hU : U6CompRes) :
    KSubT.CompFact S9.isU6two (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i) := by
  intro H _ _ J B d hJq hcat hdB hIn hd3 hdJ K hK
  have hdN : d ∈ Subgroup.normalizer (J : Set H) := hIn.1 hdB
  haveI : Nontrivial (PSimple 3 J) := nontrivial_pSimple_isU6two hb hcat
  obtain ⟨c, hc⟩ := exists_conj_equiv hdN
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  haveI : Nontrivial i.Group := e0.injective.nontrivial
  refine comp_fix hJq hdN hd3 hdJ e0 c hc ?_ K hK
  intro α _ h3 h1 L hL
  exact hU i.Group ⟨i, hi, ⟨MulEquiv.refl _⟩⟩ α h3 h1 L hL

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
