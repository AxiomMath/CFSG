module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoGF4Layer
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_even_irreducible (hV : 4 ≤ Module.finrank (ZMod 2) V) {g : V ≃ₗ[ZMod 2] V}
    (hg3 : g ^ 3 = 1) (hfix : fixSp g = ⊥) :
    ∀ W : Submodule (ZMod 2) V, (∀ h ∈ stdLayer g, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have hcom : comSp g = ⊤ := by
    have hc := (S172A.GL.isCompl_fixSp_comSp hg3).codisjoint
    rw [codisjoint_iff] at hc
    rw [hfix, bot_sup_eq] at hc
    exact hc
  obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp (S172A.GL.even_finrank_comSp hg3)
  have h4 : 4 ≤ Module.finrank (ZMod 2) (comSp g) := by
    rw [hcom, finrank_top]
    exact hV
  have hm2 : 2 ≤ m := by omega
  obtain ⟨F, hFC, hFnorm, hFq, -, htrans, -⟩ := lin_two_gf4_layer hg3 hm hm2
  have hcomp : CFSG.Open.IsComponentOf F
      (Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V))) :=
    ⟨hFC, CFSG.Open.IsSubnormal.step hFC hFnorm (CFSG.Open.IsSubnormal.refl _), hFq⟩
  have hFle : F ≤ stdLayer g := I142N.le_GLALayer hcomp
  intro W hinv
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · refine Or.inr ?_
    rw [Submodule.eq_top_iff']
    intro v
    by_cases hv : v = 0
    · rw [hv]; exact W.zero_mem
    · obtain ⟨u, huW, hu0⟩ := (Submodule.ne_bot_iff W).mp hW
      have hu : u ∈ comSp g := by rw [hcom]; exact Submodule.mem_top
      have hv' : v ∈ comSp g := by rw [hcom]; exact Submodule.mem_top
      obtain ⟨f, hfF, hfu⟩ := htrans u hu v hv' hu0 hv
      rw [← hfu]
      exact hinv f (hFle hfF) u huW

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
