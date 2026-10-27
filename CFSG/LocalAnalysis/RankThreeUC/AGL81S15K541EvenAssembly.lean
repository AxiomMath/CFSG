module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepChain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement

section Dictionary

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

@[expose] def subrepOf (Ls : Subgroup (X ⧸ gnC T)) (P : Subgroup X)
    (hP : Ls.comap (toStar T) ≤ Subgroup.normalizer (P : Set X)) :
    Subrepresentation ((gnRep hV).comp Ls.subtype) :=
  ⟨modOf hV P, fun g w hw => isInvariant_modOf hV Ls hP g.1 g.2 w hw⟩

theorem subrepOf_le {Ls : Subgroup (X ⧸ gnC T)} {P P' : Subgroup X}
    (hP : Ls.comap (toStar T) ≤ Subgroup.normalizer (P : Set X))
    (hP' : Ls.comap (toStar T) ≤ Subgroup.normalizer (P' : Set X)) (h : P ≤ P') :
    subrepOf hV Ls P hP ≤ subrepOf hV Ls P' hP' := fun _ hw => h hw

theorem exists_nontriv_factor {Ls : Subgroup (X ⧸ gnC T)} {P P' : Subgroup X}
    (hP'V : P' ≤ gnV T) (hP : Ls.comap (toStar T) ≤ Subgroup.normalizer (P : Set X))
    (hP' : Ls.comap (toStar T) ≤ Subgroup.normalizer (P' : Set X))
    (h : ¬ ⁅P', Ls.comap (toStar T)⁆ ≤ P) :
    ∃ l : ↥Ls, factorRep (subrepOf hV Ls P hP) (subrepOf hV Ls P' hP') l ≠ 1 := by
  by_contra hall
  push Not at hall
  apply h
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨w, rfl⟩ := exists_elt hV (hP'V hx)
  have hw : w ∈ (subrepOf hV Ls P' hP').toSubmodule := hx
  have h1 := LinearMap.congr_fun (hall ⟨QuotientGroup.mk y, hy⟩) (Submodule.Quotient.mk ⟨w, hw⟩)
  rw [factorRep_mk, Module.End.one_apply, Submodule.Quotient.eq] at h1
  have h3 : elt hV (gnRep hV (QuotientGroup.mk y) w - w) ∈ P := h1
  rw [elt_sub, elt_gnRep] at h3
  have e : ⁅elt hV w, y⁆ = (y * elt hV w * y⁻¹ * (elt hV w)⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact P.inv_mem h3

variable [Finite X]

theorem three_le_nontrivCount_chain {Ls : Subgroup (X ⧸ gnC T)} (hperf : commutator ↥Ls = ⊤)
    {P₀ P₁ P₂ P₃ : Subgroup X} (h01 : P₀ ≤ P₁) (h12 : P₁ ≤ P₂) (h23 : P₂ ≤ P₃) (h3V : P₃ ≤ gnV T)
    (hn0 : Ls.comap (toStar T) ≤ Subgroup.normalizer (P₀ : Set X))
    (hn1 : Ls.comap (toStar T) ≤ Subgroup.normalizer (P₁ : Set X))
    (hn2 : Ls.comap (toStar T) ≤ Subgroup.normalizer (P₂ : Set X))
    (hn3 : Ls.comap (toStar T) ≤ Subgroup.normalizer (P₃ : Set X))
    (c1 : ¬ ⁅P₁, Ls.comap (toStar T)⁆ ≤ P₀) (c2 : ¬ ⁅P₂, Ls.comap (toStar T)⁆ ≤ P₁)
    (c3 : ¬ ⁅P₃, Ls.comap (toStar T)⁆ ≤ P₂) :
    3 ≤ nontrivCount ((gnRep hV).comp Ls.subtype) := by
  have n1 := exists_nontriv_factor hV (h12.trans (h23.trans h3V)) hn0 hn1 c1
  have n2 := exists_nontriv_factor hV (h23.trans h3V) hn1 hn2 c2
  have n3 := exists_nontriv_factor hV h3V hn2 hn3 c3
  have h := three_le_nontrivCount (MonoidHom.id ↥Ls) hperf (subrepOf_le hV hn0 hn1 h01)
    (subrepOf_le hV hn1 hn2 h12) (subrepOf_le hV hn2 hn3 h23) n1 n2 n3
  rwa [MonoidHom.comp_id] at h

end Dictionary

theorem ne_bot_of_isComponentOf {Y : Type*} [Group Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) : L ≠ ⊥ := by
  intro h
  have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  subst h
  have : Nontrivial (↥(⊥ : Subgroup Y) ⧸ Subgroup.center ↥(⊥ : Subgroup Y)) := hs.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne
    (↥(⊥ : Subgroup Y) ⧸ Subgroup.center ↥(⊥ : Subgroup Y))
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))

end CFSG.LocalAnalysis.RankThreeUC.S15
