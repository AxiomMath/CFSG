module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem isDoubleCoverOfAlt_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {n : ℕ}
    (h : IsDoubleCoverOfAlt K n) : IsDoubleCoverOfAlt L n := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]; exact hc
  · have hmap : (center K).map e.toMonoidHom = center L := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        have := hx (e.symm g)
        have h2 := congrArg e this
        simpa using h2
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro g
        have := hy (e g)
        have h2 := congrArg e.symm this
        simpa using h2
    exact ⟨(QuotientGroup.congr (center K) (center L) e hmap).symm.trans φ⟩

noncomputable def toBarEquiv {G : Type} [Group G] (z : G) (hO : pPrimeCore 2 ↥(Cen z) = ⊥) :
    ↥(Cen z) ≃* CentralizerBar z :=
  MulEquiv.ofBijective (toBar z)
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, show (toBar z).ker = pPrimeCore 2 ↥(Cen z) from
        QuotientGroup.ker_mk' _, hO], QuotientGroup.mk'_surjective _⟩

theorem oneClassDoubleCover_of_sporadic {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    {n : ℕ} (hz : IsCentralInvolution z) (hO : pPrimeCore 2 ↥(Cen z) = ⊥)
    (h : Stage1Sporadic G z S n) : OneClassDoubleCover G n :=
  ⟨z, hz, h.one_class, isDoubleCoverOfAlt_of_mulEquiv (toBarEquiv z hO).symm h.cover⟩

theorem mcLLyData_of_stage2 (hno : S_noTwoAnNineTen) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} {k : Kind} (hk : k = Kind.mcl ∨ k = Kind.ly) (h : Stage2Ctx G z k S)
    (hO : pPrimeCore 2 ↥(Cen z) = ⊥) : McLLyData G := by
  have hz := h.central
  have hd := h.data
  have hn := hno G h.std
  rcases hk with rfl | rfl
  · cases hd with
    | mcl hs =>
      obtain ⟨n, hn89, hs⟩ := hs
      have hoc := oneClassDoubleCover_of_sporadic hz hO hs
      rcases hn89 with rfl | rfl
      · exact Or.inl hoc
      · exact absurd hoc hn.1
  · cases hd with
    | ly hs =>
      obtain ⟨n, hn1011, hs⟩ := hs
      have hoc := oneClassDoubleCover_of_sporadic hz hO hs
      rcases hn1011 with rfl | rfl
      · exact absurd hoc hn.2
      · exact Or.inr hoc

end CFSG.GH74.GLS.Stage2.Final
