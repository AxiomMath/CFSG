module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoStdForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameSupp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDichFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDichComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_std_dichotomy (hV : 6 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} (hA : GLAIsBmax 3 A)
    (hg : IsStdElt 3 A g) :
    Module.finrank (ZMod 2) (comSp g) = 2 ∨ Module.finrank (ZMod 2) (fixSp g) ≤ 1 := by
  obtain ⟨hgA, hg1, hg3, hcomp, hcent⟩ := hg
  by_contra hcon
  push_neg at hcon
  obtain ⟨hcom2, hfix1⟩ := hcon
  obtain ⟨m, hm⟩ := S172A.GL.even_finrank_comSp hg3
  have hcom0 : Module.finrank (ZMod 2) (comSp g) ≠ 0 := by
    intro h0
    have hbot : comSp g = ⊥ := Submodule.finrank_eq_zero.1 h0
    apply hg1
    apply LinearEquiv.ext
    intro v
    have hv : g v - v ∈ comSp g := S172A.GL.mem_comSp.2 ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
    simpa using hv
  by_cases h3 : 3 ≤ Module.finrank (ZMod 2) (fixSp g)
  · exact lin_two_not_component hg3 h3 (by omega) hcomp
  · have h2 : Module.finrank (ZMod 2) (fixSp g) = 2 := by omega
    obtain ⟨x, P, V0, hF⟩ := lin_two_std_form_of_bmax (by omega) hA
    obtain ⟨y, hyA, hyg, hy1, hy2⟩ := lin_two_outside_plane hF hgA hg3 (by omega)
    have hfixL := lin_two_layer_fixed_trivial hg3 h2 hcomp
    have hyC : y ∈ Subgroup.centralizer (stdLayer g : Set (V ≃ₗ[ZMod 2] V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlg : l * g = g * l := Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 hl)
      apply LinearEquiv.ext
      intro v
      obtain ⟨a, f, rfl⟩ := S172A.GL.exists_decomp (S172A.GL.isCompl_fixSp_comSp hg3).symm v
      simp only [LinearEquiv.mul_apply, map_add]
      have e1 : y (a : V) = a := hy1 a a.2
      have e2 : y (l (a : V)) = l a := hy1 _ (S172A.GL.cent_com hlg a.2)
      have e3 : l (f : V) = f := hfixL l hl f f.2
      have e4 : l (y (f : V)) = y f := hfixL l hl _ (hy2 f f.2)
      rw [e1, e2, e3, e4]
    have hmem : y ∈ A ⊓ Subgroup.centralizer (stdLayer g : Set (V ≃ₗ[ZMod 2] V)) := ⟨hyA, hyC⟩
    rw [hcent] at hmem
    exact hyg hmem

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
