module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoGF4Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp Nsub)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_not_component {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1)
    (hc3 : 3 ≤ Module.finrank (ZMod 2) (fixSp g))
    (hm2 : 4 ≤ Module.finrank (ZMod 2) (comSp g)) :
    ¬ CFSG.Open.IsComponentOf (stdLayer g)
      (Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V))) := by
  intro hL
  let C : Subgroup (V ≃ₗ[ZMod 2] V) :=
    Subgroup.centralizer ({g} : Set (V ≃ₗ[ZMod 2] V))
  have hNq : CFSG.Open.IsQuasisimple (S172A.GL.Nsub hg3) :=
    S172A.GL.Nsub_isQuasisimple_c (c := Module.finrank (ZMod 2) (fixSp g)) hc3 hg3 rfl
  have hNC : S172A.GL.Nsub hg3 ≤ C := S172A.GL.Nsub_le_cent hg3
  have hNnormalC : ((S172A.GL.Nsub hg3).subgroupOf C).Normal :=
    S172A.GL.Nsub_normal hg3
  have hNcompC : CFSG.Open.IsComponentOf (S172A.GL.Nsub hg3) C :=
    ⟨hNC, IsSubnormal.step hNC hNnormalC (IsSubnormal.refl C), hNq⟩
  have hNL : S172A.GL.Nsub hg3 ≤ stdLayer g := I142N.le_GLALayer hNcompC
  have hNnormalL : ((S172A.GL.Nsub hg3).subgroupOf (stdLayer g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNL]
    intro n k hn hk
    exact (Subgroup.normal_subgroupOf_iff hNC).1 hNnormalC n k hn (hL.1 hk)
  have hNeqL : S172A.GL.Nsub hg3 = stdLayer g :=
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      ⟨hNL, IsSubnormal.step hNL hNnormalL (IsSubnormal.refl _), hNq⟩ hL.2.2
  obtain ⟨m, hm0⟩ := S172A.GL.even_finrank_comSp hg3
  have hm : Module.finrank (ZMod 2) (comSp g) = 2 * m := by rw [hm0, two_mul]
  have hm2' : 2 ≤ m := by omega
  obtain ⟨F, hFC, hFnormalC, hFq, hFfix, -, -⟩ := lin_two_gf4_layer hg3 hm hm2'
  have hFcompC : CFSG.Open.IsComponentOf F C :=
    ⟨hFC, IsSubnormal.step hFC hFnormalC (IsSubnormal.refl C), hFq⟩
  have hFL : F ≤ stdLayer g := I142N.le_GLALayer hFcompC
  have hFnormalL : (F.subgroupOf (stdLayer g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFL]
    intro n k hn hk
    exact (Subgroup.normal_subgroupOf_iff hFC).1 hFnormalC n k hn (hL.1 hk)
  have hFeqL : F = stdLayer g :=
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      ⟨hFL, IsSubnormal.step hFL hFnormalL (IsSubnormal.refl _), hFq⟩ hL.2.2
  have hdisj : S172A.GL.Nsub hg3 ⊓ F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro h hh
    rw [Subgroup.mem_inf] at hh
    obtain ⟨hhN, hhF⟩ := hh
    have hNfix : ∀ a ∈ comSp g, h a = a := ((S172A.GL.mem_Nsub (h3 := hg3)).1 hhN).1
    have hFfix' : ∀ l ∈ fixSp g, h l = l := hFfix h hhF
    apply LinearEquiv.ext
    intro v
    show h v = v
    obtain ⟨u, u', huv⟩ := S172A.GL.exists_decomp (S172A.GL.isCompl_fixSp_comSp hg3) v
    rw [huv, map_add, hFfix' u u.2, hNfix u' u'.2]
  have hNF : S172A.GL.Nsub hg3 = F := hNeqL.trans hFeqL.symm
  have hNbot : S172A.GL.Nsub hg3 = ⊥ := by
    simpa only [inf_idem, ← hNF] using hdisj
  have hNne : S172A.GL.Nsub hg3 ≠ ⊥ := by
    intro hbot
    refine CFSG.Fischer.Classification.Recognition.IsQuasisimple.not_le_of_comm hNq
      (A := ⊥) (fun a ha b hb => ?_) (le_of_eq hbot)
    rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]
  exact hNne hNbot

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
