module

public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsTransv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {x : LinearMap.GeneralLinearGroup k V}

theorem sub_mem_primaryComponent_of_mem_linearSpecialBlock
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V)) {g : LinearMap.GeneralLinearGroup k V}
    (hg : g ∈ linearSpecialBlock x h) (v : V) :
    (g : Module.End k V) v - v ∈ primaryComponent (x : Module.End k V) h := by
  classical
  obtain ⟨hgc, ht, -⟩ := hg
  have hv : v = ∑ a ∈ primaryFactors (x : Module.End k V),
      primaryProjection (x : Module.End k V) a v := by
    have := LinearMap.congr_fun (sum_primaryProjection hsq) v
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  have hcomm : Commute (g : Module.End k V) (x : Module.End k V) := mem_gl_centralizer.mp hgc
  rw [hv, map_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single h]
  · exact sub_mem (apply_mem_primaryComponent hcomm (primaryProjection_mem hsq hh v))
      (primaryProjection_mem hsq hh v)
  · intro a ha hah
    rw [ht a ha hah _ (primaryProjection_mem hsq ha v), sub_self]
  · intro hn
    exact absurd hh hn

theorem exists_mem_linearSpecialBlock_transvection
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V))
    {f : Module.Dual (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)}
    {u : primaryComponent (x : Module.End k V) h} (hu : f u = 0) :
    ∃ g ∈ linearSpecialBlock x h, ∀ w : primaryComponent (x : Module.End k V) h,
      (g : Module.End k V) w = ((w + f w • u : primaryComponent (x : Module.End k V) h) : V) := by
  let τ : _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) :=
    ⟨LinearEquiv.transvection hu, LinearEquiv.transvection.det_eq_one hu⟩
  obtain ⟨g, hg⟩ := linearSpecialBlockRestrict_surjective hsq hh τ
  refine ⟨g.1, g.2, fun w => ?_⟩
  rw [← coe_linearSpecialBlockRestrict, hg]
  rfl

theorem mem_primaryComponent_of_commute_linearSpecialBlock
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) (s : V →+ V)
    (hs : ∀ g ∈ linearSpecialBlock x h, ∀ v,
      s ((g : Module.End k V) v) = (g : Module.End k V) (s v))
    {w : V} (hw : w ∈ primaryComponent (x : Module.End k V) h) :
    s w ∈ primaryComponent (x : Module.End k V) h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨f, v, hfw, hfv⟩ := exists_dual_eq_zero_eq_one hm ⟨w, hw⟩
  obtain ⟨g, hg, hgv⟩ := exists_mem_linearSpecialBlock_transvection hsq hh hfw
  have h1 : (g : Module.End k V) v = (v : V) + w := by
    rw [hgv v, hfv, one_smul]
    rfl
  have h2 : w = (g : Module.End k V) v - v := by rw [h1]; abel
  rw [h2, map_sub, hs g hg]
  exact sub_mem_primaryComponent_of_mem_linearSpecialBlock hsq hh hg _

theorem exists_smul_of_commute_linearSpecialBlock
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : 2 ≤ finrank (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) (s : V →+ V)
    (hs : ∀ g ∈ linearSpecialBlock x h, ∀ v,
      s ((g : Module.End k V) v) = (g : Module.End k V) (s v)) :
    ∃ c : AdjoinRoot h, ∀ w : primaryComponent (x : Module.End k V) h,
      s (w : V) = ((c • w : primaryComponent (x : Module.End k V) h) : V) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hmem := fun w : primaryComponent (x : Module.End k V) h =>
    mem_primaryComponent_of_commute_linearSpecialBlock hsq hh hm s hs w.2
  let sW : primaryComponent (x : Module.End k V) h →+ primaryComponent (x : Module.End k V) h :=
    { toFun := fun w => ⟨s w, hmem w⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  obtain ⟨c, hc⟩ := exists_smul_eq_of_commute_transvection hm sW (by
    intro f u hu w
    obtain ⟨g, hg, hgw⟩ := exists_mem_linearSpecialBlock_transvection hsq hh hu
    apply Subtype.ext
    change s ((w + f w • u : primaryComponent (x : Module.End k V) h) : V) =
      ((sW w + f (sW w) • u : primaryComponent (x : Module.End k V) h) : V)
    rw [← hgw w, hs g hg, ← hgw (sW w)]
    rfl)
  exact ⟨c, fun w => congrArg Subtype.val (hc w)⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
