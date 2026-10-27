module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoGeneric
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoWeightOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoEven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_hfact (hb : CatDistinct.OrderBridge) (hV : 6 ≤ Module.finrank (ZMod 2) V) :
    ∀ (A : Subgroup (V ≃ₗ[ZMod 2] V)) (g : V ≃ₗ[ZMod 2] V), GLAIsBmax 3 A → IsStdElt 3 A g →
      StdVanishes A g ∨ StdTyped 3 A g ∨ StdExtends 3 A g := by
  intro A g hA hg
  have hg3 : g ^ 3 = 1 := hg.2.2.1
  rcases lin_two_std_dichotomy hV hA hg with h2 | hfix
  ·
    exact Or.inl (lin_two_stdVanishes_of_top (by omega)
      (lin_two_weightOne_innerClosure hV hA hg h2))
  · have hsum := CFSG.LocalAnalysis.GLTheoremA.S172A.GL.finrank_fixSp hg3
    obtain ⟨m, hm⟩ := CFSG.LocalAnalysis.GLTheoremA.S172A.GL.even_finrank_comSp hg3
    rcases Nat.even_or_odd (Module.finrank (ZMod 2) V) with ⟨k, hk⟩ | ⟨k, hk⟩
    ·
      have h0 : Module.finrank (ZMod 2) (fixSp g) = 0 := by omega
      have hbot : fixSp g = ⊥ := Submodule.finrank_eq_zero.1 h0
      exact Or.inl (lin_two_stdVanishes_of_irreducible (by omega)
        (lin_two_even_irreducible (by omega) hg3 hbot))
    ·
      have h1 : Module.finrank (ZMod 2) (fixSp g) = 1 := by omega
      refine Or.inr (Or.inl ⟨lin_two_oddFull_stdFamily hb hV hA hg h1, ?_⟩)
      refine Or.inl ⟨rfl, Module.finrank (ZMod 2) V, ⟨k, hk⟩, lin_two_catalog_top (by omega),
        lin_two_oddFull_layerType (by omega) hg3 h1, ?_⟩
      rw [le_antisymm (lin_two_oddFull_innerClosure_le hV hA hg h1)
        (lin_two_oddFull_oddBlock_le hV hA hg h1)]
      exact lin_two_oddBlock_type hV hg3 h1

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
